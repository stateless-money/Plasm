//! # Plasm Staking Module
//!
//! The Plasm staking module manages era, total amounts of rewards and how to distribute.
#![cfg_attr(not(feature = "std"), no_std)]
 
use frame_support::{
   decl_event, decl_module, decl_storage, decl_error,
   traits::{Currency, Imbalance, LockableCurrency, OnUnbalanced, Time},
   StorageMap, StorageValue,
};
use frame_system::{
	self as system, ensure_signed, ensure_root, ensure_none,
	offchain::SendTransactionTypes,
};
use pallet_plasm_rewards::{
   traits::{ComputeEraWithParam, EraFinder, ForSecurityEraRewardFinder, MaybeValidators}, EraIndex
};
use sp_runtime::{
   traits::{Saturating, Zero, AtLeast32BitUnsigned},
   Perbill, RuntimeDebug, 
};
pub use sp_staking::SessionIndex;
use sp_std::{prelude::*, vec::Vec};
 
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
 
mod compute_era;
pub use compute_era::*;

use codec::{HasCompact, Encode, Decode};

  
pub type BalanceOf<T> =
   <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
pub type MomentOf<T> = <<T as Trait>::Time as Time>::Moment;
 
type PositiveImbalanceOf<T> =
   <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::PositiveImbalance;
type NegativeImbalanceOf<T> =
   <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;
 
pub trait Trait: system::Trait {
   /// The staking balance.
   type Currency: LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;
 
   /// Time used for computing era duration.
   type Time: Time;
 
   /// Tokens have been minted and are unused for validator-reward. Maybe, dapps-staking uses ().
   type RewardRemainder: OnUnbalanced<NegativeImbalanceOf<Self>>;
 
   /// Handler for the unbalanced increment when rewarding a staker. Maybe, dapps-staking uses ().
   type Reward: OnUnbalanced<PositiveImbalanceOf<Self>>;
 
   /// The information of era.
   type EraFinder: EraFinder<EraIndex, SessionIndex, MomentOf<Self>>;
 
   /// The rewards for validators.
   type ForSecurityEraReward: ForSecurityEraRewardFinder<BalanceOf<Self>>;
 
   /// The return type of ComputeEraWithParam.
   type ComputeEraParam;
 
   /// Acutually computing of ComputeEraWithParam.
   type ComputeEra: ComputeEraOnModule<Self::ComputeEraParam>;
 
   /// The overarching event type.
   type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}
 
/// Preference of what happens regarding validation.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct ValidatorPrefs {
   /// Reward that validator takes up-front; only the rest is split between themselves and
   /// nominators.
   #[codec(compact)]
   pub commission: Perbill,
}
 
impl Default for ValidatorPrefs {
   fn default() -> Self {
       ValidatorPrefs {
           commission: Default::default(),
       }
   }
}

/// Just a Balance/BlockNumber tuple to encode when a chunk of funds will be unlocked.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct UnlockChunk<Balance: HasCompact> {
	/// Amount of funds to be unlocked.
	#[codec(compact)]
	value: Balance,
	/// Era number at which point it'll be unlocked.
	#[codec(compact)]
	era: EraIndex,
}

/// The ledger of a (bonded) stash.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct StakingLedger<AccountId, Balance: HasCompact> {
	/// The stash account whose balance is actually locked and at stake.
	pub stash: AccountId,
	/// The total amount of the stash's balance that we are currently accounting for.
	/// It's just `active` plus all the `unlocking` balances.
	#[codec(compact)]
	pub total: Balance,
	/// The total amount of the stash's balance that will be at stake in any forthcoming
	/// rounds.
	#[codec(compact)]
	pub active: Balance,
	/// Any balance that is becoming free, which may eventually be transferred out
	/// of the stash (assuming it doesn't get slashed first).
	pub unlocking: Vec<UnlockChunk<Balance>>,
	/// List of eras for which the stakers behind a validator have claimed rewards. Only updated
	/// for validators.
	pub claimed_rewards: Vec<EraIndex>,
}

impl<
	AccountId,
	Balance: HasCompact + Copy + Saturating + AtLeast32BitUnsigned,
> StakingLedger<AccountId, Balance> {
	/// Remove entries from `unlocking` that are sufficiently old and reduce the
	/// total by the sum of their balances.
	fn consolidate_unlocked(self, current_era: EraIndex) -> Self {
		let mut total = self.total;
		let unlocking = self.unlocking.into_iter()
			.filter(|chunk| if chunk.era > current_era {
				true
			} else {
				total = total.saturating_sub(chunk.value);
				false
			})
			.collect();

		Self {
			stash: self.stash,
			total,
			active: self.active,
			unlocking,
			claimed_rewards: self.claimed_rewards
		}
	}

	/// Re-bond funds that were scheduled for unlocking.
	fn rebond(mut self, value: Balance) -> Self {
		let mut unlocking_balance: Balance = Zero::zero();

		while let Some(last) = self.unlocking.last_mut() {
			if unlocking_balance + last.value <= value {
				unlocking_balance += last.value;
				self.active += last.value;
				self.unlocking.pop();
			} else {
				let diff = value - unlocking_balance;

				unlocking_balance += diff;
				self.active += diff;
				last.value -= diff;
			}

			if unlocking_balance >= value {
				break
			}
		}

		self
	}
}

impl<AccountId, Balance> StakingLedger<AccountId, Balance> where
	Balance: AtLeast32BitUnsigned + Saturating + Copy,
{
	/// Slash the validator for a given amount of balance. This can grow the value
	/// of the slash in the case that the validator has less than `minimum_balance`
	/// active funds. Returns the amount of funds actually slashed.
	///
	/// Slashes from `active` funds first, and then `unlocking`, starting with the
	/// chunks that are closest to unlocking.
	fn slash(
		&mut self,
		mut value: Balance,
		minimum_balance: Balance,
	) -> Balance {
		let pre_total = self.total;
		let total = &mut self.total;
		let active = &mut self.active;

		let slash_out_of = |
			total_remaining: &mut Balance,
			target: &mut Balance,
			value: &mut Balance,
		| {
			let mut slash_from_target = (*value).min(*target);

			if !slash_from_target.is_zero() {
				*target -= slash_from_target;

				// don't leave a dust balance in the staking system.
				if *target <= minimum_balance {
					slash_from_target += *target;
					*value += sp_std::mem::replace(target, Zero::zero());
				}

				*total_remaining = total_remaining.saturating_sub(slash_from_target);
				*value -= slash_from_target;
			}
		};

		slash_out_of(total, active, &mut value);

		let i = self.unlocking.iter_mut()
			.map(|chunk| {
				slash_out_of(total, &mut chunk.value, &mut value);
				chunk.value
			})
			.take_while(|value| value.is_zero()) // take all fully-consumed chunks out.
			.count();

		// kill all drained chunks.
		let _ = self.unlocking.drain(..i);

		pre_total.saturating_sub(*total)
	}
}
 
/// A record of the nominations made by a specific account.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
pub struct Nominations<AccountId> {
   /// The targets of nomination.
   pub targets: Vec<AccountId>,
   /// The era the nominations were submitted.
   ///
   /// Except for initial nominations which are considered submitted at era 0.
   pub submitted_in: EraIndex,
   /// Whether the nominations have been suppressed. This can happen due to slashing of the
   /// validators, or other events that might invalidate the nomination.
   ///
   /// NOTE: this for future proofing and is thus far not used.
   pub suppressed: bool,
}
 
decl_storage! {
   trait Store for Module<T: Trait> as DappsStaking {
       /// The already untreated era is EraIndex.
       pub UntreatedEra get(fn untreated_era): EraIndex;
 
       
       /// Map from all (unlocked) "controller" accounts to the info regarding the staking.
	   pub Ledger get(fn ledger):
       map hasher(blake2_128_concat) T::AccountId
       => Option<StakingLedger<T::AccountId, BalanceOf<T>>>;

       /// The currently elected validator set keyed by stash account ID.
       pub ElectedValidators get(fn elected_validators):
           map hasher(twox_64_concat) EraIndex => Option<Vec<T::AccountId>>;
 
       /// The map from (wannabe) validator stash key to the preferences of that validator.
       pub Validators get(fn validators):
       map hasher(twox_64_concat) T::AccountId => ValidatorPrefs;

       /// The map from nominator stash key to the set of stash keys of all validators to nominate.
       pub Nominators get(fn nominators):
       map hasher(twox_64_concat) T::AccountId => Option<Nominations<T::AccountId>>;

       /// Set of next era accounts that can validate blocks.
       pub ValidatorsList get(fn validators_list) config(): Vec<T::AccountId>;
   }
}
 
decl_module! {
   pub struct Module<T: Trait> for enum Call where origin: T::Origin {
       fn deposit_event() = default;
 
       fn on_finalize() {
           if let Some(active_era) = T::EraFinder::active() {
               let mut untreated_era = Self::untreated_era();
 
               while active_era.index > untreated_era {
                   let rewards = match T::ForSecurityEraReward::get(&untreated_era) {
                       Some(rewards) => rewards,
                       None => {
                           frame_support::print("Error: start_session_index must be set for current_era");
                           return;
                       }
                   };
                   let actual_rewarded = Self::reward_to_validators(&untreated_era, &rewards);
 
                   // deposit event to total validator rewards
                   Self::deposit_event(RawEvent::TotalValidatorRewards(untreated_era, actual_rewarded));
 
                   untreated_era+=1;
               }
               UntreatedEra::put(untreated_era);
           }
       }
 
       #[weight = 50_000]
       fn validate(origin, prefs: ValidatorPrefs) {
           // TODO: check era election status
           // ensure!(Self::era_election_status().is_closed(), Error::<T>::CallNotAllowed);
           let controller = ensure_signed(origin)?;
           // TODO: apply controller/stash accounts
           // let ledger = Self::ledger(&controller).ok_or(Error::<T>::NotController)?;
           // let stash = &ledger.stash;
           //<Nominators<T>>::remove(stash);
           <Validators<T>>::insert(controller, prefs);
       }
 
       // ----- Root calls.
       /// Manually set new validators.
       ///
       /// # <weight>
       /// - One storage write
       /// # </weight>
       /// TODO: weight
       #[weight = 50_000]
       fn set_validators(origin, new_validators: Vec<T::AccountId>) {
           ensure_root(origin)?;
           let pref = ValidatorPrefs {
               commission: Perbill::from_percent(100)
           };
           for i in new_validators.clone() {
               <Validators<T>>::insert(i, pref.clone());
           }
           Self::deposit_event(RawEvent::NewValidators(new_validators));
       }
   }
}
 
decl_event!(
   pub enum Event<T>
   where
       AccountId = <T as system::Trait>::AccountId,
       Balance = BalanceOf<T>,
   {
       /// Validator set changed.
       NewValidators(Vec<AccountId>),
       /// The amount of minted rewards for validators.
       ValidatorReward(EraIndex, AccountId, Balance),
       /// The total amount of minted rewards for validators.
       TotalValidatorRewards(EraIndex, Balance),
   }
);

decl_error!{
    pub enum Error for Module<T: Trait> {
        /// Not a controller account.
        NotController,
        /// The call is not allowed at the given time due to restrictions of election period.
		CallNotAllowed,
    }
}
 
impl<T: Trait> Module<T> {
   pub fn reward_to_validators(era: &EraIndex, max_payout: &BalanceOf<T>) -> BalanceOf<T> {
       if let Some(validators) = Self::elected_validators(era) {
           let validator_len: u64 = validators.len() as u64;
           let mut total_imbalance = <PositiveImbalanceOf<T>>::zero();
           for v in validators.iter() {
               let reward =
                   Perbill::from_rational_approximation(1, validator_len) * max_payout.clone();
               total_imbalance.subsume(Self::reward_validator(v, reward));
           }
           let total_payout = total_imbalance.peek();
 
           let rest = max_payout.saturating_sub(total_payout.clone());
 
           T::Reward::on_unbalanced(total_imbalance);
           T::RewardRemainder::on_unbalanced(T::Currency::issue(rest));
           total_payout
       } else {
           BalanceOf::<T>::zero()
       }
   }
 
   fn reward_validator(stash: &T::AccountId, reward: BalanceOf<T>) -> PositiveImbalanceOf<T> {
       T::Currency::deposit_into_existing(&stash, reward)
           .unwrap_or(PositiveImbalanceOf::<T>::zero())
   }
}
 
/// Returns the next validator candidate for calling by plasm-rewards when new era.
impl<T: Trait> MaybeValidators<EraIndex, T::AccountId> for Module<T> {
   fn compute(current_era: EraIndex) -> Option<Vec<T::AccountId>> {
       // Apply new validator set
       <ElectedValidators<T>>::insert(&current_era, <ValidatorsList<T>>::get());
       Some(Self::validators_list())
   }
}
 
/// Get the amount of staking per Era in a module in the Plasm Network
/// for callinng by plasm-rewards when end era.
impl<T: Trait> ComputeEraWithParam<EraIndex> for Module<T> {
   type Param = T::ComputeEraParam;
   fn compute(era: &EraIndex) -> T::ComputeEraParam {
       T::ComputeEra::compute(era)
   }
}
 


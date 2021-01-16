//! Test utilities

#![cfg(test)]

use crate::*;
use frame_support::{
	assert_ok, impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types,
	traits::{Currency, FindAuthor, Get, OnFinalize, OnInitialize},
	weights::{constants::RocksDbWeight, Weight},
	IterableStorageMap, StorageDoubleMap, StorageMap, StorageValue,
};
use sp_core::{crypto::key_types, H256};
use sp_io;
use sp_npos_elections::{
	build_support_map, evaluate_support, reduce, ExtendedBalance, StakedAssignment, ElectionScore,
};
use sp_runtime::{
	curve::PiecewiseLinear,
	testing::{Header, TestXt, UintAuthorityId},
	traits::{IdentityLookup, BlakeTwo256, Zero, ConvertInto, OpaqueKeys},
};
use sp_runtime::{KeyTypeId, Perbill};
use traits::{ComputeEraWithParam, MaybeValidators};
use sp_staking::offence::{OffenceDetails, OnOffenceHandler};
use std::{cell::RefCell, collections::HashSet};

pub const INIT_TIMESTAMP: u64 = 30_000;
pub const BLOCK_TIME: u64 = 1000;

/// The AccountId alias in this test module.
pub(crate) type AccountId = u64;
pub(crate) type AccountIndex = u64;
pub(crate) type BlockNumber = u64;
pub(crate) type Balance = u128;

thread_local! {
	static SESSION: RefCell<(Vec<AccountId>, HashSet<AccountId>)> = RefCell::new(Default::default());
}

/// Another session handler struct to test on_disabled.
pub struct OtherSessionHandler;
impl pallet_session::OneSessionHandler<AccountId> for OtherSessionHandler {
	type Key = UintAuthorityId;

	fn on_genesis_session<'a, I: 'a>(_: I)
		where I: Iterator<Item=(&'a AccountId, Self::Key)>, AccountId: 'a {}

	fn on_new_session<'a, I: 'a>(_: bool, validators: I, _: I,)
		where I: Iterator<Item=(&'a AccountId, Self::Key)>, AccountId: 'a
	{
		SESSION.with(|x| {
			*x.borrow_mut() = (
				validators.map(|x| x.0.clone()).collect(),
				HashSet::new(),
			)
		});
	}

	fn on_disabled(validator_index: usize) {
		SESSION.with(|d| {
			let mut d = d.borrow_mut();
			let value = d.0[validator_index];
			d.1.insert(value);
		})
	}
}

impl sp_runtime::BoundToRuntimeAppPublic for OtherSessionHandler {
	type Public = UintAuthorityId;
}

pub fn is_disabled(controller: AccountId) -> bool {
	let stash = PlasmRewards::ledger(&controller).unwrap().stash;
	SESSION.with(|d| d.borrow().1.contains(&stash))
}


pub const ALICE_STASH: u64 = 1;

impl_outer_origin! {
    pub enum Origin for Test {}
}

impl_outer_dispatch! {
    pub enum Call for Test where origin: Origin {
        pallet_session::Session,
        pallet_balances::Balances,
        plasm_rewards::PlasmRewards,
    }
}

mod staking {
	// Re-export needed for `impl_outer_event!`.
	pub use super::super::*;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
    let mut storage = frame_system::GenesisConfig::default()
        .build_storage::<Test>()
        .unwrap();

    let _ = pallet_balances::GenesisConfig::<Test> {
        balances: vec![(ALICE_STASH, 1_000_000_000_000_000_000)],
    }
    .assimilate_storage(&mut storage);

    let validators = vec![1, 2];

    let _ = GenesisConfig::<Test> {
        ..Default::default()
    }
    .assimilate_storage(&mut storage);

    let _ = pallet_session::GenesisConfig::<Test> {
        keys: validators
            .iter()
            .map(|x| (*x, *x, UintAuthorityId(*x)))
            .collect(),
    }
    .assimilate_storage(&mut storage);

    storage.into()
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Test;

parameter_types! {
    pub const BlockHashCount: u64 = 250;
    pub const MaximumBlockWeight: u32 = 1024;
    pub const MaximumBlockLength: u32 = 2 * 1024;
    pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Trait for Test {
    type Origin = Origin;
    type BaseCallFilter = ();
    type Index = u64;
    type BlockNumber = BlockNumber;
    type Call = Call;
    type Hash = H256;
    type Hashing = BlakeTwo256;
    type AccountId = AccountId;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = Header;
    type Event = ();
    type BlockHashCount = BlockHashCount;
    type MaximumBlockWeight = MaximumBlockWeight;
    type MaximumBlockLength = MaximumBlockLength;
    type AvailableBlockRatio = AvailableBlockRatio;
    type Version = ();
    type PalletInfo = ();
    type AccountData = pallet_balances::AccountData<u64>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type DbWeight = ();
    type BlockExecutionWeight = ();
    type ExtrinsicBaseWeight = ();
    type MaximumExtrinsicWeight = ();
    type SystemWeightInfo = ();
}

parameter_types! {
    pub const MinimumPeriod: u64 = 1;
}
impl pallet_timestamp::Trait for Test {
    type Moment = u64;
    type OnTimestampSet = ();
    type MinimumPeriod = MinimumPeriod;
    type WeightInfo = ();
}

parameter_types! {
    pub const Period: u64 = 1;
    pub const Offset: u64 = 0;
}

pub struct TestSessionHandler;

impl pallet_session::SessionHandler<u64> for TestSessionHandler {
    const KEY_TYPE_IDS: &'static [KeyTypeId] = &[key_types::DUMMY];
    fn on_genesis_session<T: OpaqueKeys>(_validators: &[(u64, T)]) {}
    fn on_new_session<T: OpaqueKeys>(
        _changed: bool,
        _validators: &[(u64, T)],
        _queued_validators: &[(u64, T)],
    ) {
    }
    fn on_disabled(_validator_index: usize) {}
    fn on_before_session_ending() {}
}

impl pallet_session::Trait for Test {
    type ShouldEndSession = pallet_session::PeriodicSessions<Period, Offset>;
    type NextSessionRotation = pallet_session::PeriodicSessions<Period, Offset>;
    type SessionManager = PlasmRewards;
    type SessionHandler = TestSessionHandler;
    type ValidatorId = u64;
    type ValidatorIdOf = ConvertInto;
    type Keys = UintAuthorityId;
    type Event = ();
    type DisabledValidatorsThreshold = ();
    type WeightInfo = ();
}

impl pallet_session::historical::Trait for Test {
    type FullIdentification = crate::Exposure<AccountId, Balance>;
	type FullIdentificationOf = crate::ExposureOf<Test>;
}

/// Author of block is always 11
pub struct Author11;
impl FindAuthor<AccountId> for Author11 {
	fn find_author<'a, I>(_digests: I) -> Option<AccountId>
		where I: 'a + IntoIterator<Item = (frame_support::ConsensusEngineId, &'a [u8])>,
	{
		Some(11)
	}
}

impl pallet_authorship::Trait for Test {
	type FindAuthor = Author11;
	type UncleGenerations = UncleGenerations;
	type FilterUncle = ();
	type EventHandler = Module<Test>;
}

parameter_types! {
	pub const UncleGenerations: u64 = 0;
	pub const DisabledValidatorsThreshold: Perbill = Perbill::from_percent(25);
}

parameter_types! {
    pub const ExistentialDeposit: Balance = 10;
    
}

impl pallet_balances::Trait for Test {
    type Balance = Balance;
    type Event = ();
    type DustRemoval = ();
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = frame_system::Module<Test>;
    type WeightInfo = ();
    type MaxLocks = ();
}

pub struct DummyForSecurityStaking;
impl ComputeEraWithParam<EraIndex> for DummyForSecurityStaking {
    type Param = Balance;
    fn compute(era: &EraIndex) -> Balance {
        (era * 1_000_000).into()
    }
}

pub struct DummyForDappsStaking;
impl ComputeEraWithParam<EraIndex> for DummyForDappsStaking {
    type Param = Balance;
    fn compute(era: &EraIndex) -> Balance {
        (era * 200_000).into()
    }
}

pub struct DummyMaybeValidators;
impl MaybeValidators<EraIndex, AccountId> for DummyMaybeValidators {
    fn compute(current_era: EraIndex) -> Option<Vec<AccountId>> {
        Some(vec![1, 2, 3, (current_era + 100).into()])
    }
}

parameter_types! {
    pub const SessionsPerEra: sp_staking::SessionIndex = 3;
    pub const BondingDuration: EraIndex = 3;
    pub const MaxLocks: u32 = 1024;
	pub const SlashDeferDuration: EraIndex = 0;
	pub const ElectionLookahead: BlockNumber = 0;
	pub const MaxIterations: u32 = 0;
}

impl Trait for Test {
    type CurrencyToVote = crate::traits::SaturatingCurrencyToVote;
    type RewardRemainder = (); // Reward remainder is burned.
    type Slash = ();
    type Reward = (); // Reward is minted.
    type EraFinder = PlasmRewards;
    type SlashDeferDuration = SlashDeferDuration;
    type Currency = Balances;
    type Time = Timestamp;
    type SessionsPerEra = SessionsPerEra;
    type BondingDuration = BondingDuration;
    type ComputeEraForDapps = DummyForDappsStaking;
    type ComputeEraForSecurity = DummyForSecurityStaking;
    type ComputeTotalPayout = inflation::MaintainRatioComputeTotalPayout<Balance>;
    type MaybeValidators = DummyMaybeValidators;
    type SessionInterface = Self;
    type Event = ();
}

/// ValidatorManager module.
pub type System = frame_system::Module<Test>;
pub type Session = pallet_session::Module<Test>;
pub type Balances = pallet_balances::Module<Test>;
pub type Timestamp = pallet_timestamp::Module<Test>;
pub type PlasmRewards = Module<Test>;

pub const PER_SESSION: u64 = 60 * 1000;

pub fn advance_session() {
    let next = System::block_number() + 1;
    // increase block numebr
    System::set_block_number(next);
    // increase timestamp + 10
    let now_time = Timestamp::get();
    // on initialize
    Timestamp::set_timestamp(now_time + PER_SESSION);
    Session::rotate_session();
    assert_eq!(Session::current_index(), (next / Period::get()) as u32);

    // on finalize
    PlasmRewards::on_finalize(next);
}

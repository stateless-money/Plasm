// TODO: Remove when frame_support package in crates.io adds CurrencyToVote trait
use super::*;

/// A trait similar to `Convert` to convert values from `B` an abstract balance type
/// into u64 and back from u128. (This conversion is used in election and other places where complex
/// calculation over balance type is needed)
///
/// Total issuance of the currency is passed in, but an implementation of this trait may or may not
/// use it.
///
/// # WARNING
///
/// the total issuance being passed in implies that the implementation must be aware of the fact
/// that its values can affect the outcome. This implies that if the vote value is dependent on the
/// total issuance, it should never ber written to storage for later re-use.
pub trait CurrencyToVote<B> {
    /// Convert balance to u64.
    fn to_vote(value: B, issuance: B) -> u64;

    /// Convert u128 to balance.
    fn to_currency(value: u128, issuance: B) -> B;
}

/// An implementation of `CurrencyToVote` tailored for chain's that have a balance type of u128.
///
/// The factor is the `(total_issuance / u64::max()).max(1)`, represented as u64. Let's look at the
/// important cases:
///
/// If the chain's total issuance is less than u64::max(), this will always be 1, which means that
/// the factor will not have any effect. In this case, any account's balance is also less. Thus,
/// both of the conversions are basically an `as`; Any balance can fit in u64.
///
/// If the chain's total issuance is more than 2*u64::max(), then a factor might be multiplied and
/// divided upon conversion.
pub struct U128CurrencyToVote;

impl U128CurrencyToVote {
    fn factor(issuance: u128) -> u128 {
        (issuance / u64::max_value() as u128).max(1)
    }
}

impl CurrencyToVote<u128> for U128CurrencyToVote {
    fn to_vote(value: u128, issuance: u128) -> u64 {
        (value / Self::factor(issuance)).saturated_into()
    }

    fn to_currency(value: u128, issuance: u128) -> u128 {
        value.saturating_mul(Self::factor(issuance))
    }
}

/// A naive implementation of `CurrencyConvert` that simply saturates all conversions.
///
/// # Warning
///
/// This is designed to be used mostly for testing. Use with care, and think about the consequences.
pub struct SaturatingCurrencyToVote;

impl<B: UniqueSaturatedInto<u64> + UniqueSaturatedFrom<u128>> CurrencyToVote<B>
    for SaturatingCurrencyToVote
{
    fn to_vote(value: B, _: B) -> u64 {
        value.unique_saturated_into()
    }

    fn to_currency(value: u128, _: B) -> B {
        B::unique_saturated_from(value)
    }
}
/*
/// Something that can be checked to be a of sub type `T`.
///
/// This is useful for enums where each variant encapsulates a different sub type, and
/// you need access to these sub types.
///
/// For example, in FRAME, this trait is implemented for the runtime `Call` enum. Pallets use this
/// to check if a certain call is an instance of the local pallet's `Call` enum.
///
/// # Example
///
/// ```
/// // use frame_support::traits::IsSubType;
///
/// enum Test {
///     String(String),
///     U32(u32),
/// }
///
/// impl IsSubType<String> for Test {
///     fn is_sub_type(&self) -> Option<&String> {
///         match self {
///             Self::String(ref r) => Some(r),
///             _ => None,
///         }
///     }
/// }
///
/// impl IsSubType<u32> for Test {
///     fn is_sub_type(&self) -> Option<&u32> {
///         match self {
///             Self::U32(ref r) => Some(r),
///             _ => None,
///         }
///     }
/// }
///
/// fn main() {
///     let data = Test::String("test".into());
///
///     assert_eq!("test", IsSubType::<String>::is_sub_type(&data).unwrap().as_str());
/// }
/// ```
*/
pub trait IsSubType<T> {
    /// Returns `Some(_)` if `self` is an instance of sub type `T`.
    fn is_sub_type(&self) -> Option<&T>;
}

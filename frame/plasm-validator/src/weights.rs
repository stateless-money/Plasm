#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{
    traits::Get,
    weights::{constants::RocksDbWeight, Weight},
};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_staking.
pub trait WeightInfo {
	fn validate() -> Weight;
	fn nominate(_n: u32, ) -> Weight;
}

/// Weights for pallet_staking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
    fn validate() -> Weight {
        (25_691_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(2 as Weight))
            .saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(35_374_000 as Weight)
			.saturating_add((203_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
    fn validate() -> Weight {
        (25_691_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(2 as Weight))
            .saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn nominate(n: u32, ) -> Weight {
		(35_374_000 as Weight)
			.saturating_add((203_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
}

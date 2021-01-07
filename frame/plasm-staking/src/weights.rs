#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{
    traits::Get,
    weights::{constants::RocksDbWeight, Weight},
};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_staking.
pub trait WeightInfo {
    fn bond() -> Weight;
    fn bond_extra() -> Weight;
    fn unbond() -> Weight;
    fn withdraw_unbonded_update(_s: u32, ) -> Weight;
	fn withdraw_unbonded_kill(_s: u32, ) -> Weight;
    fn validate() -> Weight;
    fn nominate(_n: u32) -> Weight;
	fn set_controller() -> Weight;
}

/// Weights for pallet_staking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
    fn bond() -> Weight {
		(99_659_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(4 as Weight))

    }
    fn bond_extra() -> Weight {
		(79_045_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))

	}
	fn unbond() -> Weight {
		(71_716_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

    }
    fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(72_835_000 as Weight)
			.saturating_add((63_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(118_239_000 as Weight)
			.saturating_add((3_910_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().writes(8 as Weight))
			.saturating_add(T::DbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
    fn validate() -> Weight {
        (25_691_000 as Weight)
            .saturating_add(T::DbWeight::get().reads(2 as Weight))
            .saturating_add(T::DbWeight::get().writes(2 as Weight))
    }
    fn nominate(n: u32) -> Weight {
        (35_374_000 as Weight)
            .saturating_add((203_000 as Weight).saturating_mul(n as Weight))
            .saturating_add(T::DbWeight::get().reads(3 as Weight))
            .saturating_add(T::DbWeight::get().writes(2 as Weight))
    }
    fn set_controller() -> Weight {
		(37_514_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))

	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
    fn bond() -> Weight {
		(99_659_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(4 as Weight))

    }
	fn bond_extra() -> Weight {
		(79_045_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))

	}
	fn unbond() -> Weight {
		(71_716_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

    }
    fn withdraw_unbonded_update(s: u32, ) -> Weight {
		(72_835_000 as Weight)
			.saturating_add((63_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
	fn withdraw_unbonded_kill(s: u32, ) -> Weight {
		(118_239_000 as Weight)
			.saturating_add((3_910_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(8 as Weight))
			.saturating_add(RocksDbWeight::get().writes((1 as Weight).saturating_mul(s as Weight)))
	}
    fn validate() -> Weight {
        (25_691_000 as Weight)
            .saturating_add(RocksDbWeight::get().reads(2 as Weight))
            .saturating_add(RocksDbWeight::get().writes(2 as Weight))
    }
    fn nominate(n: u32) -> Weight {
        (35_374_000 as Weight)
            .saturating_add((203_000 as Weight).saturating_mul(n as Weight))
            .saturating_add(RocksDbWeight::get().reads(3 as Weight))
            .saturating_add(RocksDbWeight::get().writes(2 as Weight))
    }
    fn set_controller() -> Weight {
		(37_514_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))

	}
}

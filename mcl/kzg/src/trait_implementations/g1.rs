use crate::data_types::g1::{g1_linear_combination, is_valid_order};
use crate::data_types::{fr::Fr, g1::G1, fp::Fp, fp2::Fp2};
use crate::fk20_fft::{G1_GENERATOR, G1_NEGATIVE_GENERATOR};
use crate::mcl_methods::set_eth_serialization;
use kzg::eip_4844::BYTES_PER_G1;
use kzg::{G1Mul, G1 as CommonG1, G1LinComb};
use kzg::msm::precompute::PrecomputationTable;

impl CommonG1 for G1 {
    fn identity() -> Self {
        G1::G1_IDENTITY
    }

    fn generator() -> Self {
        G1_GENERATOR
    }

    fn negative_generator() -> Self {
        G1_NEGATIVE_GENERATOR
    }

    fn rand() -> Self {
        G1::random()
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        bytes
            .try_into()
            .map_err(|_| {
                format!(
                    "Invalid byte length. Expected {}, got {}",
                    BYTES_PER_G1,
                    bytes.len()
                )
            })
            .and_then(|bytes: &[u8; BYTES_PER_G1]| {
                set_eth_serialization(1);
                let mut g1 = G1::default();
                if !G1::deserialize(&mut g1, bytes) {
                    return Err("Failed to deserialize".to_string());
                }
                Ok(g1)
            })
    }

    fn from_hex(hex: &str) -> Result<Self, String> {
        let bytes = hex::decode(&hex[2..]).unwrap();
        Self::from_bytes(&bytes)
    }

    fn to_bytes(&self) -> [u8; 48] {
        set_eth_serialization(1);
        G1::serialize(self).try_into().unwrap()
    }

    fn add_or_dbl(&mut self, b: &Self) -> Self {
        let mut g1 = G1::zero();
        if self == b {
            G1::dbl(&mut g1, self);
        } else {
            G1::add(&mut g1, self, b);
        }
        g1
    }

    fn is_inf(&self) -> bool {
        kzg::G1::eq(self, &G1::G1_IDENTITY)
    }

    fn is_valid(&self) -> bool {
        self.is_valid() && is_valid_order(self)
    }

    fn dbl(&self) -> Self {
        let mut g1 = G1::zero();
        G1::dbl(&mut g1, self);
        g1
    }

    fn add(&self, b: &Self) -> Self {
        let mut g1 = G1::zero();
        G1::add(&mut g1, self, b);
        g1
    }

    fn sub(&self, b: &Self) -> Self {
        let mut g1 = G1::zero();
        G1::sub(&mut g1, self, b);
        g1
    }

    fn equals(&self, b: &Self) -> bool {
        kzg::G1::eq(self, b)
    }

    const ZERO: Self = Self {
            x: Fp::from([
                8505329371266088957,
                17002214543764226050,
                6865905132761471162,
                8632934651105793861,
                6631298214892334189,
                1582556514881692819,
            ]),
            y: Fp::from([
                8505329371266088957,
                17002214543764226050,
                6865905132761471162,
                8632934651105793861,
                6631298214892334189,
                1582556514881692819,
            ]),
            z: Fp::from([0, 0, 0, 0, 0, 0]),
        };

    fn add_or_dbl_assign(&mut self, b: &Self) {
        self.add_or_dbl(b)
    }

    fn add_assign(&mut self, b: &Self) {
        self.add(b)
    }

    fn dbl_assign(&mut self) {
        self.dbl()
    }
}

impl G1Mul<Fr> for G1 {
    fn mul(&self, b: &Fr) -> Self {
        let mut g1 = G1::zero();
        G1::mul(&mut g1, self, b);
        g1
    }
}

impl G1LinComb<Fr, Fp, Fp2> for G1 {
    fn g1_lincomb(points: &[Self], scalars: &[Fr], len: usize, precomputation: Option<&PrecomputationTable<Fr, Self, Fp, Fp2>>) -> Self {
        let mut result: G1 = G1::default();
        g1_linear_combination(&mut result, points, scalars, len);
        result
    }
}

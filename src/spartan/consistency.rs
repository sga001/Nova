type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
use crate::{
  traits::{circuit::StepCircuit, Group},
  StepCounterType,
};
use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use ff::PrimeField;
use generic_array::typenum;
use neptune::{
  circuit2::Elt,
  poseidon::PoseidonConstants,
  sponge::api::{IOPattern, SpongeAPI, SpongeOp},
  sponge::circuit::SpongeCircuit,
  sponge::vanilla::{Mode, SpongeTrait},
};

#[derive(Clone, Debug)]
pub struct ConsistencyCircuit<F: PrimeField> {
  pc: PoseidonConstants<F, typenum::U4>, // arity of PC can be changed as desired
  d_out: F,
  v: F,
  s: F,
}

impl<F: PrimeField> ConsistencyCircuit<F> {
  pub fn new(pc: PoseidonConstants<F, typenum::U4>, d_out: F, v: F, s: F) -> Self {
    ConsistencyCircuit { pc, d_out, v, s }
  }
}

impl<F> StepCircuit<F> for ConsistencyCircuit<F>
where
  F: PrimeField,
{
  fn arity(&self) -> usize {
    1
  }

  fn output(&self, z: &[F]) -> Vec<F> {
    vec![self.d_out]
  }

  fn synthesize<CS>(
    &self,
    cs: &mut CS,
    _z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>
  where
    CS: ConstraintSystem<F>,
    G1: Group<Base = <G2 as Group>::Scalar>,
    G2: Group<Base = <G1 as Group>::Scalar>,
  {
    //v at index 0
    let alloc_v = AllocatedNum::alloc(cs.namespace(|| "v"), || Ok(self.v))?;

    let alloc_s = AllocatedNum::alloc(cs.namespace(|| "s"), || Ok(self.s))?;

    //poseidon(v,s) == d
    let d = {
      let acc = &mut cs.namespace(|| "d hash circuit");
      let mut sponge = SpongeCircuit::new_with_constants(&self.pc, Mode::Simplex);

      sponge.start(
        IOPattern(vec![SpongeOp::Absorb(2), SpongeOp::Squeeze(1)]),
        None,
        acc,
      );

      SpongeAPI::absorb(
        &mut sponge,
        2,
        &[
          Elt::Allocated(alloc_v.clone()),
          Elt::Allocated(alloc_s.clone()),
        ],
        acc,
      );

      let output = SpongeAPI::squeeze(&mut sponge, 1, acc);

      sponge.finish(acc).unwrap();

      let output =
        Elt::ensure_allocated(&output[0], &mut acc.namespace(|| "ensure allocated"), true)?;
      output
    };

    Ok(vec![d])
  }

  fn get_counter_type(&self) -> StepCounterType {
    StepCounterType::Incremental
  }
}

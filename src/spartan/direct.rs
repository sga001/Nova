//! This module allows the use of a zkSNARK without any folding.

#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]
use crate::errors::NovaError;
use crate::traits::{
  circuit::StepCircuit,
  evaluation::EvaluationEngineTrait,
  snark::{CAPRelaxedR1CSSNARKTrait, ProverKeyTrait, RelaxedR1CSSNARKTrait, VerifierKeyTrait},
  Group,
};

use crate::{
  bellperson::{
    r1cs::{NovaShape, NovaWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
  },
  r1cs::{R1CSGens, R1CSShape, RelaxedR1CSInstance, RelaxedR1CSWitness},
  spartan::{ProverKey, RelaxedR1CSSNARK, VerifierKey},
  Commitment, CompressedCommitment,
};

use bellperson::{gadgets::num::AllocatedNum, Circuit, ConstraintSystem, SynthesisError};
use core::marker::PhantomData;
use ff::Field;
use serde::{Deserialize, Serialize};

struct SpartanCircuit<G: Group, SC: StepCircuit<G::Scalar>> {
  z_i: Option<Vec<G::Scalar>>, // inputs to the circuit
  sc: SC,
}

impl<G: Group, SC: StepCircuit<G::Scalar>> Circuit<G::Scalar> for SpartanCircuit<G, SC> {
  fn synthesize<CS: ConstraintSystem<G::Scalar>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
    // obtain the arity information
    let arity = self.sc.arity();

    // Allocate zi. If inputs.zi is not provided, allocate default value 0
    let zero = vec![G::Scalar::zero(); arity];
    let z_i = (0..arity)
      .map(|i| {
        AllocatedNum::alloc(cs.namespace(|| format!("zi_{i}")), || {
          Ok(self.z_i.as_ref().unwrap_or(&zero)[i])
        })
      })
      .collect::<Result<Vec<AllocatedNum<G::Scalar>>, _>>()?;

    let z_i_plus_one = self.sc.synthesize(&mut cs.namespace(|| "F"), &z_i)?;

    // input both z_i and z_i_plus_one
    for (j, input) in z_i.iter().enumerate().take(arity) {
      let _ = input.inputize(cs.namespace(|| format!("input {j}")));
    }

    for (j, output) in z_i_plus_one.iter().enumerate().take(arity) {
      let _ = output.inputize(cs.namespace(|| format!("output {j}")));
    }

    Ok(())
  }
}

/// A type that holds Spartan's prover key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SpartanProverKey<G, EE>
where
  G: Group,
  EE: EvaluationEngineTrait<G, CE = G::CE>,
{
  gens: R1CSGens<G>,
  S: R1CSShape<G>,
  pk: ProverKey<G, EE>,
}

/// A type that holds Spartan's verifier's key
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SpartanVerifierKey<G, EE>
where
  G: Group,
  EE: EvaluationEngineTrait<G, CE = G::CE>,
{
  vk: VerifierKey<G, EE>,
}

/// A direct zkSNARK proving a step circuit
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SpartanSNARK<G, EE, C>
where
  G: Group,
  EE: EvaluationEngineTrait<G, CE = G::CE>,
  C: StepCircuit<G::Scalar>,
{
  comm_W: Commitment<G>,          // commitment to the witness
  snark: RelaxedR1CSSNARK<G, EE>, // snark proving the witness is satisfying
  _p: PhantomData<C>,
}

impl<G: Group, EE: EvaluationEngineTrait<G, CE = G::CE>, C: StepCircuit<G::Scalar>>
  SpartanSNARK<G, EE, C>
{
  /// Produces prover and verifier keys for Spartan
  pub fn setup(sc: C) -> Result<(SpartanProverKey<G, EE>, SpartanVerifierKey<G, EE>), NovaError> {
    // construct a circuit that can be synthesized
    let circuit: SpartanCircuit<G, C> = SpartanCircuit { z_i: None, sc };

    let mut cs: ShapeCS<G> = ShapeCS::new();
    let _ = circuit.synthesize(&mut cs);
    let (S, gens) = cs.r1cs_shape();
    let S_padded = S.pad();

    let pk = ProverKey::new(&gens, &S_padded);
    let vk = VerifierKey::new(&gens, &S_padded);

    let s_pk = SpartanProverKey { gens, S, pk };
    let s_vk = SpartanVerifierKey { vk };

    Ok((s_pk, s_vk))
  }

  /// Produces a proof of satisfiability of the provided circuit
  pub fn prove(pk: &SpartanProverKey<G, EE>, sc: C, z_i: &[G::Scalar]) -> Result<Self, NovaError> {
    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();

    let circuit: SpartanCircuit<G, C> = SpartanCircuit {
      z_i: Some(z_i.to_vec()),
      sc,
    };

    let _ = circuit.synthesize(&mut cs);
    let (u, w) = cs
      .r1cs_instance_and_witness(&pk.S, &pk.gens)
      .map_err(|_e| NovaError::UnSat)?;

    // convert the instance and witness to relaxed form
    let (u_relaxed, w_relaxed) = (
      RelaxedR1CSInstance::from_r1cs_instance_unchecked(&u.comm_W, &u.X),
      RelaxedR1CSWitness::from_r1cs_witness(&pk.S, &w),
    );

    // prove the instance using Spartan
    let snark = RelaxedR1CSSNARK::prove(&pk.pk, &u_relaxed, &w_relaxed)?;

    Ok(SpartanSNARK {
      comm_W: u.comm_W,
      snark,
      _p: Default::default(),
    })
  }

  /// Verifies a proof of satisfiability
  pub fn verify(&self, vk: &SpartanVerifierKey<G, EE>, io: &[G::Scalar]) -> Result<(), NovaError> {
    // construct an instance using the provided commitment to the witness and z_i and z_{i+1}
    let u_relaxed = RelaxedR1CSInstance::from_r1cs_instance_unchecked(&self.comm_W, io);

    // verify the snark using the constructed instance
    self.snark.verify(&vk.vk, &u_relaxed)?;

    Ok(())
  }

  /// Produces a proof of satisfiability of the provided circuit (commit and proof)
  pub fn cap_prove(
    pk: &SpartanProverKey<G, EE>,
    sc: C,
    z_i: &[G::Scalar],
    cap_c: &CompressedCommitment<G>,
    cap_v: &G::Scalar,
    cap_r: &G::Scalar,
  ) -> Result<Self, NovaError> {
    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();

    let circuit: SpartanCircuit<G, C> = SpartanCircuit {
      z_i: Some(z_i.to_vec()),
      sc,
    };

    let _ = circuit.synthesize(&mut cs);
    let (u, w) = cs
      .r1cs_instance_and_witness(&pk.S, &pk.gens)
      .map_err(|_e| NovaError::UnSat)?;

    // convert the instance and witness to relaxed form
    let (u_relaxed, w_relaxed) = (
      RelaxedR1CSInstance::from_r1cs_instance_unchecked(&u.comm_W, &u.X),
      RelaxedR1CSWitness::from_r1cs_witness(&pk.S, &w),
    );

    // prove the instance using Spartan
    let snark = RelaxedR1CSSNARK::cap_prove(&pk.pk, &u_relaxed, &w_relaxed, cap_c, cap_v, cap_r)?;

    Ok(SpartanSNARK {
      comm_W: u.comm_W,
      snark,
      _p: Default::default(),
    })
  }

  /// Verifies a proof of satisfiability (commit and proof)
  pub fn cap_verify(
    &self,
    vk: &SpartanVerifierKey<G, EE>,
    io: &[G::Scalar],
    cap_c: &CompressedCommitment<G>,
  ) -> Result<(), NovaError> {
    // construct an instance using the provided commitment to the witness and z_i and z_{i+1}
    let u_relaxed = RelaxedR1CSInstance::from_r1cs_instance_unchecked(&self.comm_W, io);

    // verify the snark using the constructed instance
    self.snark.cap_verify(&vk.vk, &u_relaxed, cap_c)?;

    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::StepCounterType;
  type G = pasta_curves::pallas::Point;
  type EE = crate::provider::ipa_pc::EvaluationEngine<G>;
  use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
  use core::marker::PhantomData;
  use ff::PrimeField;

  #[derive(Clone, Debug, Default)]
  struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F> StepCircuit<F> for CubicCircuit<F>
  where
    F: PrimeField,
  {
    fn arity(&self) -> usize {
      1
    }

    fn get_counter_type(&self) -> StepCounterType {
      StepCounterType::Incremental
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      let x = &z[0];
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;
      let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), x)?;
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
      })?;

      cs.enforce(
        || "y = x^3 + x + 5",
        |lc| {
          lc + x_cu.get_variable()
            + x.get_variable()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
        },
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );

      Ok(vec![y])
    }

    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }

  #[test]
  fn test_spartan_snark() {
    let circuit = CubicCircuit::default();

    // produce keys
    let (pk, vk) =
      SpartanSNARK::<G, EE, CubicCircuit<<G as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    let num_steps = 3;

    // setup inputs
    let z0 = vec![<G as Group>::Scalar::zero()];
    let mut z_i = z0;

    for _i in 0..num_steps {
      // produce a SNARK
      let res = SpartanSNARK::prove(&pk, circuit.clone(), &z_i);
      assert!(res.is_ok());

      let z_i_plus_one = circuit.output(&z_i);

      let snark = res.unwrap();

      // verify the SNARK
      let io = z_i
        .clone()
        .into_iter()
        .chain(z_i_plus_one.clone().into_iter())
        .collect::<Vec<_>>();
      let res = snark.verify(&vk, &io);
      assert!(res.is_ok());

      // set input to the next step
      z_i = z_i_plus_one.clone();
    }

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(z_i, vec![<G as Group>::Scalar::from(2460515u64)]);
  }

  #[derive(Clone, Debug, Default)]
  struct SimpleCircuit<F: PrimeField> {
    _p: PhantomData<F>,
  }

  impl<F> StepCircuit<F> for SimpleCircuit<F>
  where
    F: PrimeField,
  {
    fn arity(&self) -> usize {
      1
    }

    fn get_counter_type(&self) -> StepCounterType {
      StepCounterType::Incremental
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      // Computes x * 1 = y, where x and y are respectively the input and output.
      let x = &z[0];
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(x.get_value().unwrap()))?;

      let useless = AllocatedNum::alloc(cs.namespace(|| "useless"), || Ok(F::one()))?;

      cs.enforce(
        || "useless is 0",
        |lc| lc + useless.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + CS::one(),
      );

      cs.enforce(
        || "y = x * 1",
        |lc| lc + x.get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );

      Ok(vec![y])
    }

    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0]]
    }
  }

  #[test]
  fn test_spartan_snark_simple() {
    let circuit = SimpleCircuit::default();

    // produce keys
    let (pk, vk) =
      SpartanSNARK::<G, EE, SimpleCircuit<<G as Group>::Scalar>>::setup(circuit.clone()).unwrap();

    // setup inputs
    let input = vec![<G as Group>::Scalar::one()];

    // produce a SNARK
    let res = SpartanSNARK::prove(&pk, circuit.clone(), &input);
    assert!(res.is_ok());

    let output = circuit.output(&input);

    let snark = res.unwrap();

    // verify the SNARK
    let io = input
      .into_iter()
      .chain(output.clone().into_iter())
      .collect::<Vec<_>>();
    let res = snark.verify(&vk, &io);
    assert!(res.is_ok());

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(output, vec![<G as Group>::Scalar::one()]);
  }
}

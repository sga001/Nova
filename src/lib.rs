//! This library implements Nova, a high-speed recursive SNARK.
#![deny(
  warnings,
  unused,
  future_incompatible,
  nonstandard_style,
  rust_2018_idioms,
  missing_docs
)]
#![allow(non_snake_case)]
#![allow(clippy::type_complexity)]
#![forbid(unsafe_code)]

// private modules
mod bellperson;
mod circuit;
mod constants;
mod nifs;
mod r1cs;

// public modules
pub mod errors;
pub mod gadgets;
pub mod provider;
pub mod spartan;
pub mod traits;

use crate::bellperson::{
  r1cs::{NovaShape, NovaWitness},
  shape_cs::ShapeCS,
  solver::SatisfyingAssignment,
};
use ::bellperson::{Circuit, ConstraintSystem};
use circuit::{NovaAugmentedCircuit, NovaAugmentedCircuitInputs, NovaAugmentedCircuitParams};
use constants::{BN_LIMB_WIDTH, BN_N_LIMBS, NUM_FE_WITHOUT_IO_FOR_CRHF, NUM_HASH_BITS};
use core::marker::PhantomData;
use errors::NovaError;
use ff::Field;
use gadgets::utils::scalar_as_base;
use nifs::NIFS;
use r1cs::{
  R1CSGens, R1CSInstance, R1CSShape, R1CSWitness, RelaxedR1CSInstance, RelaxedR1CSWitness,
};
use serde::{Deserialize, Serialize};
use traits::{
  circuit::StepCircuit,
  commitment::{CommitmentEngineTrait, CompressedCommitmentTrait},
  snark::RelaxedR1CSSNARKTrait,
  AbsorbInROTrait, Group, ROConstants, ROConstantsCircuit, ROConstantsTrait, ROTrait,
};

/// The type of counter used to measure the progress of the recusrive computation
#[derive(Eq, PartialEq, Debug, Copy, Clone, Serialize, Deserialize)]
pub enum StepCounterType {
  /// Incremental counter is a standard monotonically increasing integer
  Incremental,
  /// External counter introduces completion that is defined outside of the circuit
  External,
}

/// When using Extenral Step counter type, the verifier should use
/// `FINAL_EXTERNAL_COUNTER` as the number of steps of execution.
pub const FINAL_EXTERNAL_COUNTER: usize = 1;

/// A type that holds public parameters of Nova
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  F_arity_primary: usize,
  F_arity_secondary: usize,
  counter_type: StepCounterType,
  ro_consts_primary: ROConstants<G1>,
  ro_consts_circuit_primary: ROConstantsCircuit<G2>,
  r1cs_gens_primary: R1CSGens<G1>,
  r1cs_shape_primary: R1CSShape<G1>,
  r1cs_shape_padded_primary: R1CSShape<G1>,
  ro_consts_secondary: ROConstants<G2>,
  ro_consts_circuit_secondary: ROConstantsCircuit<G1>,
  r1cs_gens_secondary: R1CSGens<G2>,
  r1cs_shape_secondary: R1CSShape<G2>,
  r1cs_shape_padded_secondary: R1CSShape<G2>,
  augmented_circuit_params_primary: NovaAugmentedCircuitParams,
  augmented_circuit_params_secondary: NovaAugmentedCircuitParams,
  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2> PublicParams<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  /// Create a new `PublicParams`
  pub fn setup(c_primary: C1, c_secondary: C2) -> Result<Self, NovaError> {
    let augmented_circuit_params_primary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, true);
    let augmented_circuit_params_secondary =
      NovaAugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS, false);

    let ro_consts_primary: ROConstants<G1> = ROConstants::<G1>::new();
    let ro_consts_secondary: ROConstants<G2> = ROConstants::<G2>::new();

    let F_arity_primary = c_primary.arity();
    let F_arity_secondary = c_secondary.arity();

    let step_counter_primary = c_primary.get_counter_type();
    let step_counter_secondary = c_secondary.get_counter_type();

    if step_counter_primary != step_counter_secondary {
      return Err(NovaError::MismatchedCounterType);
    }

    // ro_consts_circuit_primart are parameterized by G2 because the type alias uses G2::Base = G1::Scalar
    let ro_consts_circuit_primary: ROConstantsCircuit<G2> = ROConstantsCircuit::<G2>::new();
    let ro_consts_circuit_secondary: ROConstantsCircuit<G1> = ROConstantsCircuit::<G1>::new();

    // Initialize gens for the primary
    let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
      augmented_circuit_params_primary.clone(),
      None,
      c_primary,
      ro_consts_circuit_primary.clone(),
    );
    let mut cs: ShapeCS<G1> = ShapeCS::new();
    let _ = circuit_primary.synthesize(&mut cs);
    let (r1cs_shape_primary, r1cs_gens_primary) = cs.r1cs_shape();
    let r1cs_shape_padded_primary = r1cs_shape_primary.pad();

    // Initialize gens for the secondary
    let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
      augmented_circuit_params_secondary.clone(),
      None,
      c_secondary,
      ro_consts_circuit_secondary.clone(),
    );
    let mut cs: ShapeCS<G2> = ShapeCS::new();
    let _ = circuit_secondary.synthesize(&mut cs);
    let (r1cs_shape_secondary, r1cs_gens_secondary) = cs.r1cs_shape();
    let r1cs_shape_padded_secondary = r1cs_shape_secondary.pad();

    Ok(Self {
      F_arity_primary,
      F_arity_secondary,
      counter_type: step_counter_primary,
      ro_consts_primary,
      ro_consts_circuit_primary,
      r1cs_gens_primary,
      r1cs_shape_primary,
      r1cs_shape_padded_primary,
      ro_consts_secondary,
      ro_consts_circuit_secondary,
      r1cs_gens_secondary,
      r1cs_shape_secondary,
      r1cs_shape_padded_secondary,
      augmented_circuit_params_primary,
      augmented_circuit_params_secondary,
      _p_c1: Default::default(),
      _p_c2: Default::default(),
    })
  }

  /// Returns the type of the counter for this circuit
  pub fn get_counter_type(&self) -> StepCounterType {
    self.counter_type
  }

  /// Returns the number of constraints in the primary and secondary circuits
  pub fn num_constraints(&self) -> (usize, usize) {
    (
      self.r1cs_shape_primary.num_cons,
      self.r1cs_shape_secondary.num_cons,
    )
  }

  /// Returns the number of variables in the primary and secondary circuits
  pub fn num_variables(&self) -> (usize, usize) {
    (
      self.r1cs_shape_primary.num_vars,
      self.r1cs_shape_secondary.num_vars,
    )
  }
}

/// A SNARK that proves the correct execution of an incremental computation
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  r_W_primary: RelaxedR1CSWitness<G1>,
  r_U_primary: RelaxedR1CSInstance<G1>,
  l_w_primary: R1CSWitness<G1>,
  l_u_primary: R1CSInstance<G1>,
  r_W_secondary: RelaxedR1CSWitness<G2>,
  r_U_secondary: RelaxedR1CSInstance<G2>,
  l_w_secondary: R1CSWitness<G2>,
  l_u_secondary: R1CSInstance<G2>,
  i: usize,
  zi_primary: Vec<G1::Scalar>,
  zi_secondary: Vec<G2::Scalar>,
  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2> RecursiveSNARK<G1, G2, C1, C2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
{
  /// Create a new `RecursiveSNARK` (or updates the provided `RecursiveSNARK`)
  /// by executing a step of the incremental computation
  pub fn prove_step(
    pp: &PublicParams<G1, G2, C1, C2>,
    recursive_snark: Option<Self>,
    c_primary: C1,
    c_secondary: C2,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<Self, NovaError> {
    if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
      return Err(NovaError::InvalidInitialInputLength);
    }

    let counter_type = pp.get_counter_type();

    match recursive_snark {
      None => {
        // base case for the primary
        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          pp.r1cs_shape_secondary.get_digest(),
          G1::Scalar::zero(),
          z0_primary.clone(),
          None,
          None,
          None,
          None,
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);
        let (u_primary, w_primary) = cs_primary
          .r1cs_instance_and_witness(&pp.r1cs_shape_primary, &pp.r1cs_gens_primary)
          .map_err(|_e| NovaError::UnSat)?;

        // base case for the secondary
        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.r1cs_shape_primary.get_digest(),
          G2::Scalar::zero(),
          z0_secondary.clone(),
          None,
          None,
          Some(u_primary.clone()),
          None,
        );
        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);
        let (u_secondary, w_secondary) = cs_secondary
          .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, &pp.r1cs_gens_secondary)
          .map_err(|_e| NovaError::UnSat)?;

        // IVC proof for the primary circuit
        let l_w_primary = w_primary;
        let l_u_primary = u_primary;
        let r_W_primary =
          RelaxedR1CSWitness::from_r1cs_witness(&pp.r1cs_shape_primary, &l_w_primary);
        let r_U_primary = RelaxedR1CSInstance::from_r1cs_instance(
          &pp.r1cs_gens_primary,
          &pp.r1cs_shape_primary,
          &l_u_primary,
        );

        // IVC proof of the secondary circuit
        let l_w_secondary = w_secondary;
        let l_u_secondary = u_secondary;
        let r_W_secondary = RelaxedR1CSWitness::<G2>::default(&pp.r1cs_shape_secondary);
        let r_U_secondary =
          RelaxedR1CSInstance::<G2>::default(&pp.r1cs_gens_secondary, &pp.r1cs_shape_secondary);

        // Outputs of the two circuits thus far
        let zi_primary = c_primary.output(&z0_primary);
        let zi_secondary = c_secondary.output(&z0_secondary);

        if z0_primary.len() != pp.F_arity_primary || z0_secondary.len() != pp.F_arity_secondary {
          return Err(NovaError::InvalidStepOutputLength);
        }

        let next_counter = match counter_type {
          StepCounterType::Incremental => 1,
          StepCounterType::External => 1,
        };

        Ok(Self {
          r_W_primary,
          r_U_primary,
          l_w_primary,
          l_u_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: next_counter,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
        })
      }
      Some(r_snark) => {
        // fold the secondary circuit's instance
        let (nifs_secondary, (r_U_secondary, r_W_secondary)) = NIFS::prove(
          &pp.r1cs_gens_secondary,
          &pp.ro_consts_secondary,
          &pp.r1cs_shape_secondary,
          &r_snark.r_U_secondary,
          &r_snark.r_W_secondary,
          &r_snark.l_u_secondary,
          &r_snark.l_w_secondary,
        )?;

        let mut cs_primary: SatisfyingAssignment<G1> = SatisfyingAssignment::new();
        let inputs_primary: NovaAugmentedCircuitInputs<G2> = NovaAugmentedCircuitInputs::new(
          pp.r1cs_shape_secondary.get_digest(),
          G1::Scalar::from(r_snark.i as u64),
          z0_primary,
          Some(r_snark.zi_primary.clone()),
          Some(r_snark.r_U_secondary.clone()),
          Some(r_snark.l_u_secondary.clone()),
          Some(nifs_secondary.comm_T.decompress()?),
        );

        let circuit_primary: NovaAugmentedCircuit<G2, C1> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_primary.clone(),
          Some(inputs_primary),
          c_primary.clone(),
          pp.ro_consts_circuit_primary.clone(),
        );
        let _ = circuit_primary.synthesize(&mut cs_primary);

        let (l_u_primary, l_w_primary) = cs_primary
          .r1cs_instance_and_witness(&pp.r1cs_shape_primary, &pp.r1cs_gens_primary)
          .map_err(|_e| NovaError::UnSat)?;

        // fold the primary circuit's instance
        let (nifs_primary, (r_U_primary, r_W_primary)) = NIFS::prove(
          &pp.r1cs_gens_primary,
          &pp.ro_consts_primary,
          &pp.r1cs_shape_primary,
          &r_snark.r_U_primary,
          &r_snark.r_W_primary,
          &l_u_primary,
          &l_w_primary,
        )?;

        let mut cs_secondary: SatisfyingAssignment<G2> = SatisfyingAssignment::new();
        let inputs_secondary: NovaAugmentedCircuitInputs<G1> = NovaAugmentedCircuitInputs::new(
          pp.r1cs_shape_primary.get_digest(),
          G2::Scalar::from(r_snark.i as u64),
          z0_secondary,
          Some(r_snark.zi_secondary.clone()),
          Some(r_snark.r_U_primary.clone()),
          Some(l_u_primary.clone()),
          Some(nifs_primary.comm_T.decompress()?),
        );

        let circuit_secondary: NovaAugmentedCircuit<G1, C2> = NovaAugmentedCircuit::new(
          pp.augmented_circuit_params_secondary.clone(),
          Some(inputs_secondary),
          c_secondary.clone(),
          pp.ro_consts_circuit_secondary.clone(),
        );
        let _ = circuit_secondary.synthesize(&mut cs_secondary);

        let (l_u_secondary, l_w_secondary) = cs_secondary
          .r1cs_instance_and_witness(&pp.r1cs_shape_secondary, &pp.r1cs_gens_secondary)
          .map_err(|_e| NovaError::UnSat)?;

        // update the running instances and witnesses
        let zi_primary = c_primary.output(&r_snark.zi_primary);
        let zi_secondary = c_secondary.output(&r_snark.zi_secondary);

        let next_counter = match counter_type {
          StepCounterType::Incremental => r_snark.i + 1,
          StepCounterType::External => 1,
        };

        Ok(Self {
          r_W_primary,
          r_U_primary,
          l_w_primary,
          l_u_primary,
          r_W_secondary,
          r_U_secondary,
          l_w_secondary,
          l_u_secondary,
          i: next_counter,
          zi_primary,
          zi_secondary,
          _p_c1: Default::default(),
          _p_c2: Default::default(),
        })
      }
    }
  }

  /// Verify the correctness of the `RecursiveSNARK`
  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    num_steps: usize,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), NovaError> {
    let counter_type = pp.get_counter_type();

    // If counter_type is External, the number of invocations
    // is irrevelant since progress is measured externally.
    // If it is Incremental, then it should have been executed it
    // num_steps, and num_steps should be non-zero.
    match counter_type {
      StepCounterType::External => {}
      StepCounterType::Incremental => {
        // number of steps cannot be zero
        if num_steps == 0 {
          return Err(NovaError::ProofVerifyError);
        }

        // check if the provided proof has executed num_steps
        if self.i != num_steps {
          return Err(NovaError::ProofVerifyError);
        }
      }
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_primary.X.len() != 2
      || self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <G2 as Group>::RO::new(
        pp.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
      );
      hasher.absorb(scalar_as_base::<G2>(pp.r1cs_shape_secondary.get_digest()));
      hasher.absorb(G1::Scalar::from(num_steps as u64));
      for e in &z0_primary {
        hasher.absorb(*e);
      }
      for e in &self.zi_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <G1 as Group>::RO::new(
        pp.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<G1>(pp.r1cs_shape_primary.get_digest()));
      hasher2.absorb(G2::Scalar::from(num_steps as u64));
      for e in &z0_secondary {
        hasher2.absorb(*e);
      }
      for e in &self.zi_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != scalar_as_base::<G1>(self.l_u_primary.X[1])
      || hash_secondary != scalar_as_base::<G2>(self.l_u_secondary.X[1])
      || scalar_as_base::<G1>(self.l_u_primary.X[1]) != self.l_u_secondary.X[0]
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check the satisfiability of the provided instances
    let ((res_r_primary, res_l_primary), (res_r_secondary, res_l_secondary)) = rayon::join(
      || {
        rayon::join(
          || {
            pp.r1cs_shape_primary.is_sat_relaxed(
              &pp.r1cs_gens_primary,
              &self.r_U_primary,
              &self.r_W_primary,
            )
          },
          || {
            pp.r1cs_shape_primary.is_sat(
              &pp.r1cs_gens_primary,
              &self.l_u_primary,
              &self.l_w_primary,
            )
          },
        )
      },
      || {
        rayon::join(
          || {
            pp.r1cs_shape_secondary.is_sat_relaxed(
              &pp.r1cs_gens_secondary,
              &self.r_U_secondary,
              &self.r_W_secondary,
            )
          },
          || {
            pp.r1cs_shape_secondary.is_sat(
              &pp.r1cs_gens_secondary,
              &self.l_u_secondary,
              &self.l_w_secondary,
            )
          },
        )
      },
    );

    // check the returned res objects
    res_r_primary?;
    res_l_primary?;
    res_r_secondary?;
    res_l_secondary?;

    Ok((self.zi_primary.clone(), self.zi_secondary.clone()))
  }
}

/// A SNARK that proves the knowledge of a valid `RecursiveSNARK`
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  /// r_U_primary
  pub r_U_primary: RelaxedR1CSInstance<G1>,
  /// l_u_primary
  pub l_u_primary: R1CSInstance<G1>,
  /// nifs_primary
  pub nifs_primary: NIFS<G1>,
  /// f_W_snark_primary
  pub f_W_snark_primary: S1,

  /// r_U_secondary
  pub r_U_secondary: RelaxedR1CSInstance<G2>,
  /// l_u_secondary
  pub l_u_secondary: R1CSInstance<G2>,
  /// nifs_secondary
  pub nifs_secondary: NIFS<G2>,
  /// f_W_snark_secondary
  pub f_W_snark_secondary: S2,

  /// zn primary
  pub zn_primary: Vec<G1::Scalar>,
  /// zn secondary
  pub zn_secondary: Vec<G2::Scalar>,

  _p_c1: PhantomData<C1>,
  _p_c2: PhantomData<C2>,
}

impl<G1, G2, C1, C2, S1, S2> CompressedSNARK<G1, G2, C1, C2, S1, S2>
where
  G1: Group<Base = <G2 as Group>::Scalar>,
  G2: Group<Base = <G1 as Group>::Scalar>,
  C1: StepCircuit<G1::Scalar>,
  C2: StepCircuit<G2::Scalar>,
  S1: RelaxedR1CSSNARKTrait<G1>,
  S2: RelaxedR1CSSNARKTrait<G2>,
{
  /// Create a new `CompressedSNARK`
  pub fn prove(
    pp: &PublicParams<G1, G2, C1, C2>,
    recursive_snark: &RecursiveSNARK<G1, G2, C1, C2>,
  ) -> Result<Self, NovaError> {
    let (res_primary, res_secondary) = rayon::join(
      // fold the primary circuit's instance
      || {
        NIFS::prove(
          &pp.r1cs_gens_primary,
          &pp.ro_consts_primary,
          &pp.r1cs_shape_primary,
          &recursive_snark.r_U_primary,
          &recursive_snark.r_W_primary,
          &recursive_snark.l_u_primary,
          &recursive_snark.l_w_primary,
        )
      },
      || {
        // fold the secondary circuit's instance
        NIFS::prove(
          &pp.r1cs_gens_secondary,
          &pp.ro_consts_secondary,
          &pp.r1cs_shape_secondary,
          &recursive_snark.r_U_secondary,
          &recursive_snark.r_W_secondary,
          &recursive_snark.l_u_secondary,
          &recursive_snark.l_w_secondary,
        )
      },
    );

    let (nifs_primary, (f_U_primary, f_W_primary)) = res_primary?;
    let (nifs_secondary, (f_U_secondary, f_W_secondary)) = res_secondary?;

    // produce a prover key for the SNARK
    let (pk_primary, pk_secondary) = rayon::join(
      || S1::prover_key(&pp.r1cs_gens_primary, &pp.r1cs_shape_padded_primary),
      || S2::prover_key(&pp.r1cs_gens_secondary, &pp.r1cs_shape_padded_secondary),
    );

    // create SNARKs proving the knowledge of f_W_primary and f_W_secondary
    let (f_W_snark_primary, f_W_snark_secondary) = rayon::join(
      || {
        S1::prove(
          &pk_primary,
          &f_U_primary,
          &f_W_primary.pad(&pp.r1cs_shape_padded_primary), // pad the witness since shape was padded
        )
      },
      || {
        S2::prove(
          &pk_secondary,
          &f_U_secondary,
          &f_W_secondary.pad(&pp.r1cs_shape_padded_secondary), // pad the witness since the shape was padded
        )
      },
    );

    Ok(Self {
      r_U_primary: recursive_snark.r_U_primary.clone(),
      l_u_primary: recursive_snark.l_u_primary.clone(),
      nifs_primary,
      f_W_snark_primary: f_W_snark_primary?,

      r_U_secondary: recursive_snark.r_U_secondary.clone(),
      l_u_secondary: recursive_snark.l_u_secondary.clone(),
      nifs_secondary,
      f_W_snark_secondary: f_W_snark_secondary?,

      zn_primary: recursive_snark.zi_primary.clone(),
      zn_secondary: recursive_snark.zi_secondary.clone(),

      _p_c1: Default::default(),
      _p_c2: Default::default(),
    })
  }

  /// Verify the correctness of the `CompressedSNARK`
  pub fn verify(
    &self,
    pp: &PublicParams<G1, G2, C1, C2>,
    num_steps: usize,
    z0_primary: Vec<G1::Scalar>,
    z0_secondary: Vec<G2::Scalar>,
  ) -> Result<(Vec<G1::Scalar>, Vec<G2::Scalar>), NovaError> {
    let counter_type = pp.get_counter_type();

    // If counter_type is External, the number of invocations
    // is irrevelant since progress is measured externally.
    // If it is Incremental, then it should have been executed it
    // num_steps, and num_steps should be non-zero.
    match counter_type {
      StepCounterType::External => {}
      StepCounterType::Incremental => {
        // number of steps cannot be zero
        if num_steps == 0 {
          return Err(NovaError::ProofVerifyError);
        }
      }
    }

    // check if the (relaxed) R1CS instances have two public outputs
    if self.l_u_primary.X.len() != 2
      || self.l_u_secondary.X.len() != 2
      || self.r_U_primary.X.len() != 2
      || self.r_U_secondary.X.len() != 2
    {
      return Err(NovaError::ProofVerifyError);
    }

    // check if the output hashes in R1CS instances point to the right running instances
    let (hash_primary, hash_secondary) = {
      let mut hasher = <G2 as Group>::RO::new(
        pp.ro_consts_secondary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_primary,
      );
      hasher.absorb(scalar_as_base::<G2>(pp.r1cs_shape_secondary.get_digest()));
      hasher.absorb(G1::Scalar::from(num_steps as u64));
      for e in z0_primary {
        hasher.absorb(e);
      }
      for e in &self.zn_primary {
        hasher.absorb(*e);
      }
      self.r_U_secondary.absorb_in_ro(&mut hasher);

      let mut hasher2 = <G1 as Group>::RO::new(
        pp.ro_consts_primary.clone(),
        NUM_FE_WITHOUT_IO_FOR_CRHF + 2 * pp.F_arity_secondary,
      );
      hasher2.absorb(scalar_as_base::<G1>(pp.r1cs_shape_primary.get_digest()));
      hasher2.absorb(G2::Scalar::from(num_steps as u64));
      for e in z0_secondary {
        hasher2.absorb(e);
      }
      for e in &self.zn_secondary {
        hasher2.absorb(*e);
      }
      self.r_U_primary.absorb_in_ro(&mut hasher2);

      (
        hasher.squeeze(NUM_HASH_BITS),
        hasher2.squeeze(NUM_HASH_BITS),
      )
    };

    if hash_primary != scalar_as_base::<G1>(self.l_u_primary.X[1])
      || hash_secondary != scalar_as_base::<G2>(self.l_u_secondary.X[1])
    {
      return Err(NovaError::ProofVerifyError);
    }

    // fold the running instance and last instance to get a folded instance
    let f_U_primary = self.nifs_primary.verify(
      &pp.ro_consts_primary,
      &pp.r1cs_shape_primary,
      &self.r_U_primary,
      &self.l_u_primary,
    )?;
    let f_U_secondary = self.nifs_secondary.verify(
      &pp.ro_consts_secondary,
      &pp.r1cs_shape_secondary,
      &self.r_U_secondary,
      &self.l_u_secondary,
    )?;

    // produce a verifier key for the SNARK
    let (vk_primary, vk_secondary) = rayon::join(
      || S1::verifier_key(&pp.r1cs_gens_primary, &pp.r1cs_shape_padded_primary),
      || S2::verifier_key(&pp.r1cs_gens_secondary, &pp.r1cs_shape_padded_secondary),
    );

    // check the satisfiability of the folded instances using SNARKs proving the knowledge of their satisfying witnesses
    let (res_primary, res_secondary) = rayon::join(
      || self.f_W_snark_primary.verify(&vk_primary, &f_U_primary),
      || {
        self
          .f_W_snark_secondary
          .verify(&vk_secondary, &f_U_secondary)
      },
    );

    res_primary?;
    res_secondary?;

    Ok((self.zn_primary.clone(), self.zn_secondary.clone()))
  }
}

type CommitmentGens<G> = <<G as traits::Group>::CE as CommitmentEngineTrait<G>>::CommitmentGens;
type Commitment<G> = <<G as Group>::CE as CommitmentEngineTrait<G>>::Commitment;
type CompressedCommitment<G> = <<G as Group>::CE as CommitmentEngineTrait<G>>::CompressedCommitment;
type CE<G> = <G as Group>::CE;

#[cfg(test)]
mod tests {
  use super::*;
  type G1 = pasta_curves::pallas::Point;
  type G2 = pasta_curves::vesta::Point;
  type EE1 = provider::ipa_pc::EvaluationEngine<G1>;
  type EE2 = provider::ipa_pc::EvaluationEngine<G2>;
  type S1 = spartan::RelaxedR1CSSNARK<G1, EE1>;
  type S2 = spartan::RelaxedR1CSSNARK<G2, EE2>;
  use ::bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
  use core::marker::PhantomData;
  use ff::PrimeField;
  use traits::circuit::TrivialTestCircuit;

  #[derive(Clone, Debug)]
  struct CubicCircuit<F: PrimeField> {
    _p: PhantomData<F>,
    counter_type: StepCounterType,
  }

  impl<F> CubicCircuit<F>
  where
    F: PrimeField,
  {
    pub fn new(counter_type: StepCounterType) -> CubicCircuit<F> {
      Self {
        _p: PhantomData,
        counter_type,
      }
    }
  }

  impl<F> Default for CubicCircuit<F>
  where
    F: PrimeField,
  {
    /// Creates a new trivial test circuit with step counter type Incremental
    fn default() -> CubicCircuit<F> {
      Self {
        _p: PhantomData,
        counter_type: StepCounterType::Incremental,
      }
    }
  }

  impl<F> StepCircuit<F> for CubicCircuit<F>
  where
    F: PrimeField,
  {
    fn arity(&self) -> usize {
      1
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

    fn get_counter_type(&self) -> StepCounterType {
      self.counter_type
    }

    fn output(&self, z: &[F]) -> Vec<F> {
      vec![z[0] * z[0] * z[0] + z[0] + F::from(5u64)]
    }
  }

  #[test]
  fn test_ivc_trivial() {
    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(TrivialTestCircuit::default(), TrivialTestCircuit::default())
    .unwrap();

    let num_steps = 1;

    // produce a recursive SNARK
    let res = RecursiveSNARK::prove_step(
      &pp,
      None,
      TrivialTestCircuit::default(),
      TrivialTestCircuit::default(),
      vec![<G1 as Group>::Scalar::zero()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
    let recursive_snark = res.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::zero()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_external_trivial() {
    let circuit_primary = TrivialTestCircuit::new(StepCounterType::External);
    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();

    // produce a recursive SNARK
    let res = RecursiveSNARK::prove_step(
      &pp,
      None,
      circuit_primary,
      circuit_secondary,
      vec![<G1 as Group>::Scalar::zero()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
    let recursive_snark = res.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      vec![<G1 as Group>::Scalar::zero()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_nontrivial() {
    let circuit_primary = TrivialTestCircuit::default();
    let circuit_secondary = CubicCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        TrivialTestCircuit<<G1 as Group>::Scalar>,
        CubicCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for i in 0..num_steps {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());
      let recursive_snark_unwrapped = res.unwrap();

      // verify the recursive snark at each step of recursion
      let res = recursive_snark_unwrapped.verify(
        &pp,
        i + 1,
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());

      // set the running variable for the next iteration
      recursive_snark = Some(recursive_snark_unwrapped);
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    let mut zn_secondary_direct = vec![<G2 as Group>::Scalar::zero()];
    for _i in 0..num_steps {
      zn_secondary_direct = CubicCircuit::default().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(2460515u64)]);
  }

  #[test]
  fn test_ivc_external_nontrivial() {
    let circuit_primary = TrivialTestCircuit::new(StepCounterType::External);
    let circuit_secondary = CubicCircuit::new(StepCounterType::External);

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        TrivialTestCircuit<<G1 as Group>::Scalar>,
        CubicCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for _i in 0..num_steps {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());
      let recursive_snark_unwrapped = res.unwrap();

      // verify the recursive snark at each step of recursion
      let res = recursive_snark_unwrapped.verify(
        &pp,
        FINAL_EXTERNAL_COUNTER,
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());

      // set the running variable for the next iteration
      recursive_snark = Some(recursive_snark_unwrapped);
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    let mut zn_secondary_direct = vec![<G2 as Group>::Scalar::zero()];
    for _i in 0..num_steps {
      zn_secondary_direct = CubicCircuit::default().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(2460515u64)]);
  }

  #[test]
  fn test_ivc_nontrivial_with_compression() {
    let circuit_primary = TrivialTestCircuit::default();
    let circuit_secondary = CubicCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        TrivialTestCircuit<<G1 as Group>::Scalar>,
        CubicCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for _i in 0..num_steps {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    let mut zn_secondary_direct = vec![<G2 as Group>::Scalar::zero()];
    for _i in 0..num_steps {
      zn_secondary_direct = CubicCircuit::default().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(2460515u64)]);

    // produce a compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_external_nontrivial_with_compression() {
    let circuit_primary = TrivialTestCircuit::new(StepCounterType::External);
    let circuit_secondary = CubicCircuit::new(StepCounterType::External);

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary.clone(), circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        TrivialTestCircuit<<G1 as Group>::Scalar>,
        CubicCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for _i in 0..num_steps {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        vec![<G1 as Group>::Scalar::one()],
        vec![<G2 as Group>::Scalar::zero()],
      );
      assert!(res.is_ok());
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    // sanity: check the claimed output with a direct computation of the same
    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    let mut zn_secondary_direct = vec![<G2 as Group>::Scalar::zero()];
    for _i in 0..num_steps {
      zn_secondary_direct = CubicCircuit::default().output(&zn_secondary_direct);
    }
    assert_eq!(zn_secondary, zn_secondary_direct);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(2460515u64)]);

    // produce a compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_external_nondet_with_compression() {
    // y is a non-deterministic advice representing the fifth root of the input at a step.
    #[derive(Clone, Debug)]
    struct FifthRootCheckingCircuitExternal<F: PrimeField> {
      y: F,
    }

    impl<F> FifthRootCheckingCircuitExternal<F>
    where
      F: PrimeField,
    {
      fn new(num_steps: usize) -> (Vec<F>, Vec<Self>) {
        let mut powers = Vec::new();
        let rng = &mut rand::rngs::OsRng;
        let mut seed = F::random(rng);
        for _i in 0..num_steps + 1 {
          let mut power = seed;
          power = power.square();
          power = power.square();
          power *= seed;

          powers.push(Self { y: power });

          seed = power;
        }

        // reverse the powers to get roots
        let roots = powers.into_iter().rev().collect::<Vec<Self>>();
        (vec![roots[0].y], roots[1..].to_vec())
      }
    }

    impl<F> StepCircuit<F> for FifthRootCheckingCircuitExternal<F>
    where
      F: PrimeField,
    {
      fn arity(&self) -> usize {
        1
      }

      fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
      ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x = &z[0];

        // we allocate a variable and set it to the provided non-derministic advice.
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.y))?;

        // We now check if y = x^{1/5} by checking if y^5 = x
        let y_sq = y.square(cs.namespace(|| "y_sq"))?;
        let y_quad = y_sq.square(cs.namespace(|| "y_quad"))?;
        let y_pow_5 = y_quad.mul(cs.namespace(|| "y_fifth"), &y)?;

        cs.enforce(
          || "y^5 = x",
          |lc| lc + y_pow_5.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + x.get_variable(),
        );

        Ok(vec![y])
      }

      fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::External
      }

      fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        let x = z[0];
        let y_pow_5 = {
          let y = self.y;
          let y_sq = y.square();
          let y_quad = y_sq.square();
          y_quad * self.y
        };
        assert_eq!(x, y_pow_5);

        // return non-deterministic advice
        // as the output of the step
        vec![self.y]
      }
    }

    let circuit_primary = FifthRootCheckingCircuitExternal {
      y: <G1 as Group>::Scalar::zero(),
    };

    let circuit_secondary = TrivialTestCircuit::new(StepCounterType::External);

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      FifthRootCheckingCircuitExternal<<G1 as Group>::Scalar>,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary, circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce non-deterministic advice
    let (z0_primary, roots) = FifthRootCheckingCircuitExternal::new(num_steps);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        FifthRootCheckingCircuitExternal<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for circuit_primary in roots.iter().take(num_steps) {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        z0_primary.clone(),
        z0_secondary.clone(),
      );
      assert!(res.is_ok());
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      z0_primary.clone(),
      z0_secondary.clone(),
    );
    assert!(res.is_ok());

    // produce a compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(&pp, FINAL_EXTERNAL_COUNTER, z0_primary, z0_secondary);
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_nondet_with_compression() {
    // y is a non-deterministic advice representing the fifth root of the input at a step.
    #[derive(Clone, Debug)]
    struct FifthRootCheckingCircuit<F: PrimeField> {
      y: F,
    }

    impl<F> FifthRootCheckingCircuit<F>
    where
      F: PrimeField,
    {
      fn new(num_steps: usize) -> (Vec<F>, Vec<Self>) {
        let mut powers = Vec::new();
        let rng = &mut rand::rngs::OsRng;
        let mut seed = F::random(rng);
        for _i in 0..num_steps + 1 {
          let mut power = seed;
          power = power.square();
          power = power.square();
          power *= seed;

          powers.push(Self { y: power });

          seed = power;
        }

        // reverse the powers to get roots
        let roots = powers.into_iter().rev().collect::<Vec<Self>>();
        (vec![roots[0].y], roots[1..].to_vec())
      }
    }

    impl<F> StepCircuit<F> for FifthRootCheckingCircuit<F>
    where
      F: PrimeField,
    {
      fn arity(&self) -> usize {
        1
      }

      fn synthesize<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        z: &[AllocatedNum<F>],
      ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
        let x = &z[0];

        // we allocate a variable and set it to the provided non-derministic advice.
        let y = AllocatedNum::alloc(cs.namespace(|| "y"), || Ok(self.y))?;

        // We now check if y = x^{1/5} by checking if y^5 = x
        let y_sq = y.square(cs.namespace(|| "y_sq"))?;
        let y_quad = y_sq.square(cs.namespace(|| "y_quad"))?;
        let y_pow_5 = y_quad.mul(cs.namespace(|| "y_fifth"), &y)?;

        cs.enforce(
          || "y^5 = x",
          |lc| lc + y_pow_5.get_variable(),
          |lc| lc + CS::one(),
          |lc| lc + x.get_variable(),
        );

        Ok(vec![y])
      }

      fn get_counter_type(&self) -> StepCounterType {
        StepCounterType::Incremental
      }

      fn output(&self, z: &[F]) -> Vec<F> {
        // sanity check
        let x = z[0];
        let y_pow_5 = {
          let y = self.y;
          let y_sq = y.square();
          let y_quad = y_sq.square();
          y_quad * self.y
        };
        assert_eq!(x, y_pow_5);

        // return non-deterministic advice
        // as the output of the step
        vec![self.y]
      }
    }

    let circuit_primary = FifthRootCheckingCircuit {
      y: <G1 as Group>::Scalar::zero(),
    };

    let circuit_secondary = TrivialTestCircuit::default();

    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      FifthRootCheckingCircuit<<G1 as Group>::Scalar>,
      TrivialTestCircuit<<G2 as Group>::Scalar>,
    >::setup(circuit_primary, circuit_secondary.clone())
    .unwrap();

    let num_steps = 3;

    // produce non-deterministic advice
    let (z0_primary, roots) = FifthRootCheckingCircuit::new(num_steps);
    let z0_secondary = vec![<G2 as Group>::Scalar::zero()];

    // produce a recursive SNARK
    let mut recursive_snark: Option<
      RecursiveSNARK<
        G1,
        G2,
        FifthRootCheckingCircuit<<G1 as Group>::Scalar>,
        TrivialTestCircuit<<G2 as Group>::Scalar>,
      >,
    > = None;

    for circuit_primary in roots.iter().take(num_steps) {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        circuit_primary.clone(),
        circuit_secondary.clone(),
        z0_primary.clone(),
        z0_secondary.clone(),
      );
      assert!(res.is_ok());
      recursive_snark = Some(res.unwrap());
    }

    assert!(recursive_snark.is_some());
    let recursive_snark = recursive_snark.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(&pp, num_steps, z0_primary.clone(), z0_secondary.clone());
    assert!(res.is_ok());

    // produce a compressed SNARK
    let res = CompressedSNARK::<_, _, _, _, S1, S2>::prove(&pp, &recursive_snark);
    assert!(res.is_ok());
    let compressed_snark = res.unwrap();

    // verify the compressed SNARK
    let res = compressed_snark.verify(&pp, num_steps, z0_primary, z0_secondary);
    assert!(res.is_ok());
  }

  #[test]
  fn test_ivc_external_base() {
    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(
      TrivialTestCircuit::new(StepCounterType::External),
      CubicCircuit::new(StepCounterType::External),
    )
    .unwrap();

    // produce a recursive SNARK
    let res = RecursiveSNARK::prove_step(
      &pp,
      None,
      TrivialTestCircuit::default(),
      CubicCircuit::default(),
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
    let recursive_snark = res.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      FINAL_EXTERNAL_COUNTER,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(5u64)]);
  }

  #[test]
  fn test_ivc_base() {
    // produce public parameters
    let pp = PublicParams::<
      G1,
      G2,
      TrivialTestCircuit<<G1 as Group>::Scalar>,
      CubicCircuit<<G2 as Group>::Scalar>,
    >::setup(TrivialTestCircuit::default(), CubicCircuit::default())
    .unwrap();

    let num_steps = 1;

    // produce a recursive SNARK
    let res = RecursiveSNARK::prove_step(
      &pp,
      None,
      TrivialTestCircuit::default(),
      CubicCircuit::default(),
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());
    let recursive_snark = res.unwrap();

    // verify the recursive SNARK
    let res = recursive_snark.verify(
      &pp,
      num_steps,
      vec![<G1 as Group>::Scalar::one()],
      vec![<G2 as Group>::Scalar::zero()],
    );
    assert!(res.is_ok());

    let (zn_primary, zn_secondary) = res.unwrap();

    assert_eq!(zn_primary, vec![<G1 as Group>::Scalar::one()]);
    assert_eq!(zn_secondary, vec![<G2 as Group>::Scalar::from(5u64)]);
  }
}

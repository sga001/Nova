#![allow(non_snake_case)]

use bellperson::{gadgets::num::AllocatedNum, ConstraintSystem, SynthesisError};
use core::marker::PhantomData;
use criterion::*;
use ff::PrimeField;
use nova_snark::{
  traits::{
    circuit::{StepCircuit, TrivialTestCircuit},
    Group,
  },
  PublicParams, RecursiveSNARK, StepCounterType,
};
use std::time::Duration;

type G1 = pasta_curves::pallas::Point;
type G2 = pasta_curves::vesta::Point;
type C1 = NonTrivialTestCircuit<<G1 as Group>::Scalar>;
type C2 = TrivialTestCircuit<<G2 as Group>::Scalar>;

criterion_group! {
name = recursive_snark;
config = Criterion::default().warm_up_time(Duration::from_millis(3000));
targets = bench_recursive_snark
}

criterion_main!(recursive_snark);

fn bench_recursive_snark(c: &mut Criterion) {
  let num_cons_verifier_circuit_primary = 9819;
  // we vary the number of constraints in the step circuit
  for &num_cons_in_augmented_circuit in [16384, 32768].iter() {
    // number of constraints in the step circuit
    let num_cons = num_cons_in_augmented_circuit - num_cons_verifier_circuit_primary;

    let mut group = c.benchmark_group(format!("RecursiveSNARK-StepCircuitSize-{num_cons}"));
    group.sample_size(10);

    // Produce public parameters
    let pp = PublicParams::<G1, G2, C1, C2>::setup(
      NonTrivialTestCircuit::new(num_cons),
      TrivialTestCircuit::default(),
    )
    .unwrap();

    // Bench time to produce a recursive SNARK;
    // we execute a certain number of warm-up steps since executing
    // the first step is cheaper than other steps owing to the presence of
    // a lot of zeros in the satisfying assignment
    let num_warmup_steps = 10;
    let mut recursive_snark: Option<RecursiveSNARK<G1, G2, C1, C2>> = None;

    for i in 0..num_warmup_steps {
      let res = RecursiveSNARK::prove_step(
        &pp,
        recursive_snark,
        NonTrivialTestCircuit::new(num_cons),
        TrivialTestCircuit::default(),
        vec![<G1 as Group>::Scalar::from(2u64)],
        vec![<G2 as Group>::Scalar::from(2u64)],
      );
      assert!(res.is_ok());
      let recursive_snark_unwrapped = res.unwrap();

      // verify the recursive snark at each step of recursion
      let res = recursive_snark_unwrapped.verify(
        &pp,
        i + 1,
        vec![<G1 as Group>::Scalar::from(2u64)],
        vec![<G2 as Group>::Scalar::from(2u64)],
      );
      assert!(res.is_ok());

      // set the running variable for the next iteration
      recursive_snark = Some(recursive_snark_unwrapped);
    }

    group.bench_function("Prove", |b| {
      b.iter(|| {
        // produce a recursive SNARK for a step of the recursion
        assert!(RecursiveSNARK::prove_step(
          black_box(&pp),
          black_box(recursive_snark.clone()),
          black_box(NonTrivialTestCircuit::new(num_cons)),
          black_box(TrivialTestCircuit::default()),
          black_box(vec![<G1 as Group>::Scalar::from(2u64)]),
          black_box(vec![<G2 as Group>::Scalar::from(2u64)]),
        )
        .is_ok());
      })
    });

    let recursive_snark = recursive_snark.unwrap();

    // Benchmark the verification time
    group.bench_function("Verify", |b| {
      b.iter(|| {
        assert!(black_box(&recursive_snark)
          .verify(
            black_box(&pp),
            black_box(num_warmup_steps),
            black_box(vec![<G1 as Group>::Scalar::from(2u64)]),
            black_box(vec![<G2 as Group>::Scalar::from(2u64)]),
          )
          .is_ok());
      });
    });
    group.finish();
  }
}

#[derive(Clone, Debug, Default)]
struct NonTrivialTestCircuit<F: PrimeField> {
  num_cons: usize,
  _p: PhantomData<F>,
}

impl<F> NonTrivialTestCircuit<F>
where
  F: PrimeField,
{
  pub fn new(num_cons: usize) -> Self {
    Self {
      num_cons,
      _p: Default::default(),
    }
  }
}
impl<F> StepCircuit<F> for NonTrivialTestCircuit<F>
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
    // Consider a an equation: `x^2 = y`, where `x` and `y` are respectively the input and output.
    let mut x = z[0].clone();
    let mut y = x.clone();
    for i in 0..self.num_cons {
      y = x.square(cs.namespace(|| format!("x_sq_{i}")))?;
      x = y.clone();
    }
    Ok(vec![y])
  }

  fn get_counter_type(&self) -> StepCounterType {
    StepCounterType::Incremental
  }

  fn output(&self, z: &[F]) -> Vec<F> {
    let mut x = z[0];
    let mut y = x;
    for _i in 0..self.num_cons {
      y = x * x;
      x = y;
    }
    vec![y]
  }
}

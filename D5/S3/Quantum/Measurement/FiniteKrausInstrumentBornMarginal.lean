/- GID: D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Kraus instrument branch weights equal the Born weights of their effects. -/

import D5.S3.Quantum.Measurement.StaticEffectSequentialSeparation
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition

/- Library-search audit trail (2026-08-27):
   * Exact family hits `DensityState` and `bornProbability` supply the canonical
     physical state and trace-pairing probability. The existing instrument
     modules concern sequential words or a concrete qubit separation and do not
     expose the general one-step marginal identity.
   * Body-shape searches for Kraus branches, effects, and trace marginals found
     no canonical D5 definitions; the public theorem therefore constructs them
     as local lets from a normalized finite Kraus family.
   * Pinned Mathlib exact hits `Matrix.trace_sum`, `Matrix.mul_sum`,
     `Matrix.trace_mul_cycle`, and `Matrix.trace_mul_comm` prove the identity. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Measurement.FiniteKrausInstrumentBornMarginal

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.FiniteDimensional

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A normalized finite Kraus family constructs every instrument branch and its
effect. The trace of the branch state is exactly the Born weight of that effect. -/
theorem finite_kraus_instrument_born_marginal
    {n Setting Outcome Kraus : Type*}
    [Fintype n] [Nonempty n] [DecidableEq n]
    [Fintype Outcome] [Fintype Kraus]
    (instrumentKraus :
      {K : Setting -> Outcome -> Kraus -> Matrix n n ℂ //
        ∀ x, ∑ a, ∑ k, star (K x a k) * K x a k = 1})
    (rho : DensityState n) :
    ∀ x a,
      let state : Matrix n n ℂ := CStarMatrix.ofMatrix.symm rho.1
      let branch : Matrix n n ℂ :=
        ∑ k, instrumentKraus.1 x a k * state * star (instrumentKraus.1 x a k)
      let effect : Matrix n n ℂ :=
        ∑ k, star (instrumentKraus.1 x a k) * instrumentKraus.1 x a k
      Matrix.trace branch = bornProbability state effect := by
  intro x a
  dsimp only
  rw [bornProbability, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    Matrix.trace
        (instrumentKraus.1 x a k * CStarMatrix.ofMatrix.symm rho.1 *
          star (instrumentKraus.1 x a k)) =
      Matrix.trace
        (star (instrumentKraus.1 x a k) * instrumentKraus.1 x a k *
          CStarMatrix.ofMatrix.symm rho.1) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace
        (CStarMatrix.ofMatrix.symm rho.1 *
          (star (instrumentKraus.1 x a k) * instrumentKraus.1 x a k)) :=
      Matrix.trace_mul_comm _ _

#print axioms finite_kraus_instrument_born_marginal

end D5.S3.Quantum.Measurement.FiniteKrausInstrumentBornMarginal

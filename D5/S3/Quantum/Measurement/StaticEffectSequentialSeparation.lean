/- GID: D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/StaticEffectSequentialSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal qubit instrument effects can have different two-step joint laws. -/

import D5.S3.Observer.StateNotPath

/- Library-search audit trail (2026-08-27):
   * Repository searches for equal POVMs, instrument effects, Kraus branches,
     and sequential joint laws found no theorem containing both the static and
     sequential clauses of the source result.
   * Exact current-tree hits `basisZeroDensity`, `qubitX`, and
     `bornProbability` supply the canonical initial state, post-measurement
     flip, and trace pairing. In particular, the basis-zero matrix is imported
     rather than redeclared from its body shape.
   * Body-shape searches for `K * rho * star K`, `star K * K`, and Bool-indexed
     Kraus normalization found no canonical D5 branch or effect primitive. The
     constructions remain local lets in the public theorem, not new family
     definitions.
   * Pinned Mathlib supplies matrix star, multiplication, trace, and finite Bool
     summation, but no exact instrument countermodel theorem. -/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.StaticEffectSequentialSeparation

open D5.S3.Observer.StateNotPath
open D5.S3.Quantum.FiniteDimensional

/-- Two explicit normalized single-Kraus qubit instruments have the same
effect POVM but different joint weights in one two-step experiment. The second
instrument applies the canonical Pauli-X flip after each coordinate branch;
after first outcome `false`, a subsequent measurement of the complementary
coordinate effect therefore has weight one instead of zero. -/
theorem same_effects_different_two_step_joint_law :
    let projectiveKraus : Bool -> QubitMatrix := fun outcome =>
      if outcome then 1 - basisZeroDensity else basisZeroDensity
    let flippedKraus : Bool -> QubitMatrix := fun outcome =>
      qubitX * projectiveKraus outcome
    let effect : (Bool -> QubitMatrix) -> Bool -> QubitMatrix :=
      fun kraus outcome => star (kraus outcome) * kraus outcome
    let branch : (Bool -> QubitMatrix) -> Bool -> QubitMatrix -> QubitMatrix :=
      fun kraus outcome rho => kraus outcome * rho * star (kraus outcome)
    let secondEffect : QubitMatrix := 1 - basisZeroDensity
    (forall outcome, effect projectiveKraus outcome = effect flippedKraus outcome) ∧
      (∑ outcome, effect projectiveKraus outcome) = 1 ∧
      (∑ outcome, effect flippedKraus outcome) = 1 ∧
      bornProbability (branch projectiveKraus false basisZeroDensity) secondEffect = 0 ∧
      bornProbability (branch flippedKraus false basisZeroDensity) secondEffect = 1 := by
  dsimp
  constructor
  · intro outcome
    cases outcome <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        norm_num [basisZeroDensity, qubitX, Matrix.mul_apply, Matrix.vecMul,
          Matrix.sub_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
          dotProduct, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [basisZeroDensity, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Fintype.sum_bool]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [basisZeroDensity, qubitX, Matrix.mul_apply, Matrix.vecMul,
        Matrix.sub_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
        dotProduct, Fin.sum_univ_two, Fintype.sum_bool]
  constructor <;>
    norm_num [bornProbability, basisZeroDensity, qubitX, Matrix.trace,
      Matrix.mul_apply, Matrix.vecMul, Matrix.sub_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, dotProduct, Fin.sum_univ_two]

#print axioms same_effects_different_two_step_joint_law

end D5.S3.Quantum.Measurement.StaticEffectSequentialSeparation

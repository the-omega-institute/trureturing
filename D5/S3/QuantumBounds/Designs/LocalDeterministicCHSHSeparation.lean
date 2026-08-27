/- GID: D5/S3/QuantumBounds/Designs/LocalDeterministicCHSHSeparation
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/Designs/LocalDeterministicCHSHSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate deterministic local answer tables from the fixed Bell witness. -/

/- Library-search audit trail (2026-08-27):
   * Pinned Mathlib's `CHSH_inequality_of_comm` is the exact pointwise algebraic
     ingredient, while no library declaration packages every clause below.
   * `ClassicalFiberBound.classical_chsh_abs_le_two` supplies the finite weighted
     expectation bound from nonnegative normalized preparation weights.
   * `CHSHWitness.bell_chsh_value` supplies the exact fixed Bell-state value.
   * `ClassicalAnswerTableExclusion.noncontextual_and_local_double_exclusion`
     supplies both exclusions for one preparation-independent answer table. -/

import D5.S3.Observer.ClassicalAnswerTableExclusion

namespace D5.S3.QuantumBounds.Designs.LocalDeterministicCHSHSeparation

open D5.S3.Observer.ClassicalAnswerTableExclusion
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.QuantumBounds.ClassicalFiberBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every deterministic local fiber has absolute CHSH value at most two, and
finite probability mixing preserves that bound. The fixed Bell witness has
value `2 * sqrt 2`, while the noncontextual and local branches of the same
preparation-independent deterministic answer table are both excluded. -/
theorem local_deterministic_chsh_separation
    {Fiber : Type*} [Fintype Fiber] [Nonempty Fiber]
    (preparation : FinitePreparation Fiber)
    (model : DeterministicFiberModel Fiber)
    (table : DeterministicAnswerTable Fiber) :
    (∀ fiber, |chshAt model fiber| ≤ 2) ∧
      |classicalCHSH preparation.weight model| ≤ 2 ∧
      Matrix.trace (bellDensity * chshOperator) = ((2 * Real.sqrt 2 : ℝ) : ℂ) ∧
      (Not (IsNoncontextual table) ∧ Not (ReproducesBellCHSH preparation table)) := by
  have hPointwise : ∀ fiber, |chshAt model fiber| ≤ 2 := by
    intro fiber
    cases hA0 : model.alice 0 fiber <;>
      cases hA1 : model.alice 1 fiber <;>
      cases hB0 : model.bob 0 fiber <;>
      cases hB1 : model.bob 1 fiber <;>
      norm_num [chshAt, observable, boolValue, hA0, hA1, hB0, hB1]
  exact ⟨hPointwise,
    classical_chsh_abs_le_two preparation.weight preparation.weight_nonnegative
      preparation.weight_normalized model,
    bell_chsh_value,
    noncontextual_and_local_double_exclusion preparation table⟩

#print axioms local_deterministic_chsh_separation

end D5.S3.QuantumBounds.Designs.LocalDeterministicCHSHSeparation

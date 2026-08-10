/- GID: D5/S3/Observer/ClassicalAnswerTableExclusion
   generality: G
   mirror-B: D5/B/S3/Observer/ClassicalAnswerTableExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exclude one preparation-independent answer table by noncontextual and local witnesses. -/

/- Library-search audit trail (2026-08-10):
   * Searches of the pinned mathlib tree for Kochen-Specker, contextuality, noncontextual hidden
     variables, deterministic response functions, and answer tables found no theorem combining a
     no-character obstruction with a finite local CHSH bound.
   * `D5.S3.Observer.WindowCharacter.window_algebra_has_no_character` supplies the frozen
     noncontextual obstruction at window size two.
   * `D5.S3.QuantumBounds.ClassicalFiberBound.classical_chsh_abs_le_two` supplies the frozen local
     bound, and `Real.one_lt_sqrt_two` separates it strictly from the frozen Bell-state value.
   * Preparation independence is structural: the answer field has no preparation argument, while
     one normalized preparation supplies a setting-independent hidden-fiber distribution.
-/

import D5.S3.Observer.WindowCharacter
import D5.S3.QuantumBounds.ClassicalFiberBound

namespace D5.S3.Observer.ClassicalAnswerTableExclusion

open D5.S3.Observer.WindowCharacter
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.QuantumBounds.ClassicalFiberBound
open scoped BigOperators

/-- The complete two-dimensional window algebra used by the noncontextuality witness. -/
abbrev WindowAlgebra := Matrix (ZMod 2) (ZMod 2) Complex

/-- One deterministic answer table for every relevant query and hidden fiber: all elements of the
window algebra, Alice's two settings, and Bob's two settings. In particular, `windowAnswer` covers
every projection in the algebra. The table has no preparation argument, so the same instance is
used independently of how the fiber is prepared. -/
structure DeterministicAnswerTable (Fiber : Type*) where
  windowAnswer : WindowAlgebra -> Fiber -> Complex
  aliceAnswer : Fin 2 -> Fiber -> Bool
  bobAnswer : Fin 2 -> Fiber -> Bool

/-- A finite preparation changes only the distribution on hidden fibers, not the answer table. -/
structure FinitePreparation (Fiber : Type*) [Fintype Fiber] where
  weight : Fiber -> Real
  weight_nonnegative : forall fiber, 0 <= weight fiber
  weight_normalized : Finset.univ.sum weight = 1

/-- The value assigned by a table to an arbitrary element of the window algebra. -/
def windowValue {Fiber : Type*} (table : DeterministicAnswerTable Fiber)
    (observable : WindowAlgebra) (fiber : Fiber) : Complex :=
  table.windowAnswer observable fiber

/-- The local CHSH model read from the Alice and Bob branches of the same answer table. -/
def localModel {Fiber : Type*}
    (table : DeterministicAnswerTable Fiber) : DeterministicFiberModel Fiber where
  alice := table.aliceAnswer
  bob := table.bobAnswer

/-- Noncontextuality means that, at every hidden fiber, the values assigned to all window-algebra
elements are the values of one unital complex-algebra character. -/
def IsNoncontextual {Fiber : Type*} (table : DeterministicAnswerTable Fiber) : Prop :=
  forall fiber, exists character : AlgHom Complex WindowAlgebra Complex,
    forall observable, windowValue table observable fiber = character observable

/-- The local branches reproduce the fixed Bell-state CHSH expectation under one preparation. -/
def ReproducesBellCHSH {Fiber : Type*} [Fintype Fiber]
    (preparation : FinitePreparation Fiber) (table : DeterministicAnswerTable Fiber) : Prop :=
  classicalCHSH preparation.weight (localModel table) =
    (Matrix.trace (bellDensity * chshOperator)).re

/-- A concrete total answer table, witnessing that the shared table structure is inhabited. -/
def baselineAnswerTable (Fiber : Type*) : DeterministicAnswerTable Fiber where
  windowAnswer := fun _ _ => 0
  aliceAnswer := fun _ _ => false
  bobAnswer := fun _ _ => false

/-- The one-point normalized preparation used by the non-vacuity witness. -/
def unitPreparation : FinitePreparation Unit where
  weight := fun _ => 1
  weight_nonnegative := by intro; norm_num
  weight_normalized := by simp

/-- The theorem's two explicit inputs are jointly inhabited on a one-point hidden fiber. -/
theorem answer_table_inputs_are_inhabited :
    Nonempty (FinitePreparation Unit × DeterministicAnswerTable Unit) :=
  ⟨unitPreparation, baselineAnswerTable Unit⟩

/-- The inhabited baseline table attains the sharp classical CHSH value two. -/
theorem baseline_answer_table_chsh_eq_two :
    classicalCHSH unitPreparation.weight (localModel (baselineAnswerTable Unit)) = 2 := by
  norm_num [classicalCHSH, chshAt, observable, localModel, baselineAnswerTable,
    unitPreparation, boolValue]

/-- The same local, noncontextual, preparation-independent deterministic answer table is excluded
twice. Its window branch cannot extend to a character, and its local branches cannot reproduce the
fixed Bell-state CHSH value. Thus no table instance survives either classical requirement. -/
theorem noncontextual_and_local_double_exclusion
    {Fiber : Type*} [Fintype Fiber] [Nonempty Fiber]
    (preparation : FinitePreparation Fiber) (table : DeterministicAnswerTable Fiber) :
    And (Not (IsNoncontextual table)) (Not (ReproducesBellCHSH preparation table)) := by
  constructor
  · intro hNoncontextual
    let fiber : Fiber := Classical.choice (inferInstance : Nonempty Fiber)
    rcases hNoncontextual fiber with ⟨character, _⟩
    letI : IsEmpty (AlgHom Complex WindowAlgebra Complex) :=
      window_algebra_has_no_character 2 (by norm_num)
    exact isEmptyElim character
  · intro hReproduces
    have hAbsoluteBound :
        |classicalCHSH preparation.weight (localModel table)| <= 2 :=
      classical_chsh_abs_le_two preparation.weight preparation.weight_nonnegative
        preparation.weight_normalized (localModel table)
    have hSignedBound : classicalCHSH preparation.weight (localModel table) <= 2 :=
      le_trans (le_abs_self _) hAbsoluteBound
    have hQuantumAboveClassical :
        2 < (Matrix.trace (bellDensity * chshOperator)).re := by
      rw [bell_chsh_value]
      norm_num
      nlinarith [Real.one_lt_sqrt_two]
    rw [hReproduces] at hSignedBound
    exact (not_lt_of_ge hSignedBound) hQuantumAboveClassical

end D5.S3.Observer.ClassicalAnswerTableExclusion

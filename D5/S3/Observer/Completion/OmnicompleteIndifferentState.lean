/- GID: D5/S3/Observer/Completion/OmnicompleteIndifferentState
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/OmnicompleteIndifferentState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four measure conditions define an omnicomplete indifferent state. -/

import Mathlib.Algebra.Group.PUnit
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-09-01):
   * Repository searches for `Omnicomplete`, full-support invariant measures,
     projective measure compatibility, and zero completion defects found only
     separate component results; none packages all four defining clauses.
   * The adjacent bound atom is `InfiniteCompletionDefect.infinite_completion_defect_eq_zero_iff`;
     it characterizes a weighted defect sum and does not define the four-part state.
   * Pinned Mathlib provides `Measure.support`, `SMulInvariantMeasure`,
     `IsProjectiveLimit`, and `Measure.map_id`. Searches across all pinned Lean
     packages found no aggregate structure with the source's four clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.OmnicompleteIndifferentState

open MeasureTheory

/-- An omnicomplete indifferent state consists of a measure with full support,
invariance under every symmetry, the prescribed measure at every finite
projection, and zero defect at every finite level. -/
structure OmnicompleteSystem
    (State Symmetry : Type*) [TopologicalSpace State] [MeasurableSpace State]
    [Group Symmetry] [MulAction Symmetry State]
    (FiniteState : Nat -> Type*) [forall n, MeasurableSpace (FiniteState n)]
    (projection : forall n, State -> FiniteState n)
    (finiteMeasure : forall n, Measure (FiniteState n))
    (defect : Nat -> Measure State -> Real) where
  measure : Measure State
  full_support : measure.support = Set.univ
  symmetry_invariant :
    forall g : Symmetry, Measure.map (fun state => g • state) measure = measure
  projection_compatible :
    forall n : Nat, Measure.map (projection n) measure = finiteMeasure n
  completion_defect_zero : forall n : Nat, defect n measure = 0

/-- The definition is inhabited on a genuinely two-point state space: counting
measure gives both Boolean states mass one, the one-element symmetry group acts
trivially, every finite projection is the identity, and every defect is zero. -/
theorem exists_bool_omnicomplete_indifferent_state :
    exists system : OmnicompleteSystem
        Bool PUnit (fun _ => Bool) (fun _ state => state)
        (fun _ => Measure.count) (fun _ _ => 0),
      system.measure {false} = 1 ∧ system.measure {true} = 1 := by
  letI : MulAction PUnit Bool :=
    { smul := fun _ state => state
      one_smul := by intro state; rfl
      mul_smul := by intro x y state; rfl }
  letI : Measure.IsOpenPosMeasure (Measure.count : Measure Bool) :=
    { open_pos := by
        intro U _ hU
        exact Measure.count_ne_zero hU }
  let system : OmnicompleteSystem
      Bool PUnit (fun _ => Bool) (fun _ state => state)
      (fun _ => Measure.count) (fun _ _ => 0) :=
    { measure := Measure.count
      full_support := Measure.support_eq_univ
      symmetry_invariant := by
        intro symmetry
        have haction : (fun state : Bool => symmetry • state) = id := by
          funext state
          rfl
        rw [haction, Measure.map_id]
      projection_compatible := by
        intro n
        exact Measure.map_id'
      completion_defect_zero := by
        intro n
        rfl }
  refine ⟨system, ?_, ?_⟩
  · simp [system, Measure.count_apply]
  · simp [system, Measure.count_apply]

#print axioms exists_bool_omnicomplete_indifferent_state

end D5.S3.Observer.Completion.OmnicompleteIndifferentState

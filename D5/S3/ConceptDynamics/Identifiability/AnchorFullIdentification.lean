/- GID: D5/S3/ConceptDynamics/Identifiability/AnchorFullIdentification
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/AnchorFullIdentification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full anchored identification is equivalent to reachability and injective behavior. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic

/-! Library-search audit trail (2026-08-21):
* `rg -n "Function\\.Injective|Injective|reachable|Reach|reach|anchor|identif"
  D5/S3/ConceptDynamics -g '*.lean'` found the adjacent quotient theorem
  `EmpiricalIdentifiability.empirical_identifiability`, but it has no anchored reachability
  clause and does not state full-state recovery.
* `rg -n "injective_iff_hasLeftInverse|def HasLeftInverse|theorem .*hasLeftInverse"
  .lake/packages/mathlib/Mathlib -g '*.lean'` found the exact equivalence
  `Function.injective_iff_hasLeftInverse`, applied directly below.
* Pinned Mathlib also supplies `Set.ne_univ_iff_exists_notMem` and
  `Function.not_injective_iff`; both source failure clauses use them directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.AnchorFullIdentification

/-- Relative to an anchor, all states can be recovered from their complete behavior exactly
when all states are reachable and the behavior map is injective. Failure of reachability exposes
an unreachable state; under full reachability, failure of injectivity exposes two reachable states
with identical behavior. -/
theorem anchor_full_identification_iff
    {State Readout : Type*} (anchor : State)
    (reach : State -> Set State) (behavior : State -> Readout) :
    (((reach anchor = Set.univ ∧ Function.HasLeftInverse behavior) ↔
        reach anchor = Set.univ ∧ Function.Injective behavior) ∧
      (reach anchor ≠ Set.univ -> ∃ state, state ∉ reach anchor) ∧
      (reach anchor = Set.univ -> ¬Function.Injective behavior ->
        ∃ x y,
          x ∈ reach anchor ∧ y ∈ reach anchor ∧
            behavior x = behavior y ∧ x ≠ y)) := by
  letI : Nonempty State := ⟨anchor⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.injective_iff_hasLeftInverse]
  · intro hreach
    exact (Set.ne_univ_iff_exists_notMem (reach anchor)).mp hreach
  · intro hreach hbehavior
    rcases Function.not_injective_iff.mp hbehavior with ⟨x, y, hsame, hxy⟩
    refine ⟨x, y, ?_, ?_, hsame, hxy⟩
    · simp [hreach]
    · simp [hreach]

/-- The criterion's domain and positive hypotheses are inhabited. -/
example :
    (Set.univ : Set Bool) = Set.univ ∧ Function.Injective (id : Bool -> Bool) :=
  ⟨rfl, fun _ _ h => h⟩

/-- A constant behavior on two reachable states realizes the non-injective failure clause. -/
example :
    ∃ x y : Bool,
      x ∈ (Set.univ : Set Bool) ∧ y ∈ (Set.univ : Set Bool) ∧
        (fun _ : Bool => ()) x = (fun _ : Bool => ()) y ∧ x ≠ y := by
  exact ⟨false, true, by simp⟩

#print axioms anchor_full_identification_iff

end D5.S3.ConceptDynamics.Identifiability.AnchorFullIdentification

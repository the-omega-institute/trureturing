/- GID: D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Rights/ConflictRepairHittingSet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every successful downward-closed conflict repair hits each conflicting core. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'repair_must_hit_conflict_core' D5 Golden/Frozen/accepted`
     found no existing declaration.
   * `rg -in 'hitting|minimal.*core|conflict' D5/ | head -20` found only unrelated
     uses of "conflict"; no conflict-core or hitting-set theorem was reusable.
   * Searches for `IsMinimal`, `Set.Finite`, antichains, lower sets, and monotone
     set predicates in pinned Mathlib found only generic order or finite-set machinery,
     with no conflict-repair theorem to import. The proof below uses only subset,
     difference, intersection, and the explicitly stated downward-closure hypothesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Rights.ConflictRepairHittingSet

/-- Joint satisfiability is preserved when rights are removed. -/
def DownwardClosed {Right : Type*} (Satisfiable : Set Right → Prop) : Prop :=
  ∀ ⦃smaller larger : Set Right⦄, smaller ⊆ larger →
    Satisfiable larger → Satisfiable smaller

/-- A conflict core is minimal when all of its proper subsets are satisfiable. -/
def MinimalConflictCore {Right : Type*} (Satisfiable : Set Right → Prop)
    (core : Set Right) : Prop :=
  ¬Satisfiable core ∧ ∀ ⦃smaller : Set Right⦄, smaller ⊂ core → Satisfiable smaller

/-- Any successful repair must delete a right from the specified conflicting core. -/
theorem repair_must_hit_conflict_core
    {Right : Type*} {Satisfiable : Set Right → Prop}
    (downwardClosed : DownwardClosed Satisfiable)
    {rights modified core : Set Right}
    (coreWithinRights : core ⊆ rights)
    (coreConflicts : ¬Satisfiable core)
    (repairSucceeds : Satisfiable (rights \ modified)) :
    (modified ∩ core).Nonempty := by
  by_contra noHit
  have coreWithinRepair : core ⊆ rights \ modified := by
    intro right rightInCore
    refine ⟨coreWithinRights rightInCore, ?_⟩
    intro rightModified
    exact noHit ⟨right, rightModified, rightInCore⟩
  exact coreConflicts (downwardClosed coreWithinRepair repairSucceeds)

/-- A successful repair simultaneously hits every conflict core in the original rights. -/
theorem repair_hits_every_conflict_core
    {Right : Type*} {Satisfiable : Set Right → Prop}
    (downwardClosed : DownwardClosed Satisfiable)
    {rights modified : Set Right}
    (repairSucceeds : Satisfiable (rights \ modified)) :
    ∀ core, core ⊆ rights → ¬Satisfiable core → (modified ∩ core).Nonempty := by
  intro core coreWithinRights coreConflicts
  exact repair_must_hit_conflict_core downwardClosed coreWithinRights
    coreConflicts repairSucceeds

/-- Three concrete rights used to witness a nontrivial repair problem. -/
inductive ThreeRights where
  | a
  | b
  | c
  deriving DecidableEq

/-- A set of rights is satisfiable exactly when it does not contain both `a` and `b`. -/
def threeRightsSatisfiable (rights : Set ThreeRights) : Prop :=
  ¬({ThreeRights.a, ThreeRights.b} : Set ThreeRights) ⊆ rights

/-- The three-right model has a minimal conflict, a successful hitting repair, and a
non-hitting modification that fails to repair the conflict. -/
example :
    DownwardClosed threeRightsSatisfiable ∧
      MinimalConflictCore threeRightsSatisfiable
        ({ThreeRights.a, ThreeRights.b} : Set ThreeRights) ∧
      threeRightsSatisfiable
        (({ThreeRights.a, ThreeRights.b, ThreeRights.c} : Set ThreeRights) \
          ({ThreeRights.a} : Set ThreeRights)) ∧
      (({ThreeRights.a} : Set ThreeRights) ∩
          ({ThreeRights.a, ThreeRights.b} : Set ThreeRights)).Nonempty ∧
      ¬threeRightsSatisfiable
        (({ThreeRights.a, ThreeRights.b, ThreeRights.c} : Set ThreeRights) \
          ({ThreeRights.c} : Set ThreeRights)) := by
  have downwardClosed : DownwardClosed threeRightsSatisfiable := by
    intro smaller larger smallerWithinLarger largerSatisfiable conflictWithinSmaller
    exact largerSatisfiable (conflictWithinSmaller.trans smallerWithinLarger)
  have minimalCore :
      MinimalConflictCore threeRightsSatisfiable
        ({ThreeRights.a, ThreeRights.b} : Set ThreeRights) := by
    constructor
    · simp [threeRightsSatisfiable]
    · intro smaller smallerProper conflictWithinSmaller
      exact (not_le_of_gt smallerProper) conflictWithinSmaller
  have repairA :
      threeRightsSatisfiable
        (({ThreeRights.a, ThreeRights.b, ThreeRights.c} : Set ThreeRights) \
          ({ThreeRights.a} : Set ThreeRights)) := by
    unfold threeRightsSatisfiable
    intro conflictWithinRepair
    have aInRepair := conflictWithinRepair (show ThreeRights.a ∈
      ({ThreeRights.a, ThreeRights.b} : Set ThreeRights) by simp)
    exact aInRepair.2 (by simp)
  have hitA :
      (({ThreeRights.a} : Set ThreeRights) ∩
          ({ThreeRights.a, ThreeRights.b} : Set ThreeRights)).Nonempty := by
    exact repair_must_hit_conflict_core downwardClosed (by simp)
      minimalCore.1 repairA
  have repairCFails :
      ¬threeRightsSatisfiable
        (({ThreeRights.a, ThreeRights.b, ThreeRights.c} : Set ThreeRights) \
          ({ThreeRights.c} : Set ThreeRights)) := by
    simp only [threeRightsSatisfiable, not_not]
    intro right rightInConflict
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at rightInConflict
    rcases rightInConflict with rfl | rfl <;> simp
  exact ⟨downwardClosed, minimalCore, repairA, hitA, repairCFails⟩

#print axioms repair_must_hit_conflict_core

end D5.S3.ConceptDynamics.Rights.ConflictRepairHittingSet

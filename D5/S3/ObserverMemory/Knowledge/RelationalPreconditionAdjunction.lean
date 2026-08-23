/- GID: D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relational strongest postconditions are adjoint to universal weakest preconditions. -/

import D5.S3.ObserverMemory.Knowledge.StrongestPostconditionAdjunction
import Mathlib.Data.Rel

/- Library-search audit trail (2026-08-22):
   * Exact pinned-Mathlib hits `SetRel.image`, `SetRel.preimage`, and
     `SetRel.core` are respectively the relational strongest postcondition,
     existential precondition, and universal weakest precondition; all three
     are used directly below rather than reimplemented.
   * Exact pinned-Mathlib hit `SetRel.image_subset_iff` is the complete
     relational adjunction and is applied directly.
   * The frozen predecessor `StrongestPostconditionAdjunction.sp_wp_adjunction`
     is the deterministic-function theorem. It is imported as the family
     predecessor but does not cover arbitrary relations or the may/must gap.
   * Repository and pinned-library searches found no theorem packaging the
     relational image/universal-precondition adjunction together with a
     nondeterministic countermodel to may-implies-must. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction

/-- A state may reach a target predicate when it has at least one related
outcome in that predicate. This is Mathlib's relational preimage. -/
def existentialPrecondition {X Y : Type*}
    (relation : SetRel X Y) (target : Set Y) : Set X :=
  SetRel.preimage relation target

/-- A state guarantees a target predicate when every related outcome lies in
that predicate. -/
def universalWeakestPrecondition {X Y : Type*}
    (relation : SetRel X Y) (target : Set Y) : Set X :=
  SetRel.core relation target

/-- The strongest postcondition is Mathlib's relational image of the source
predicate. -/
def relationalStrongestPostcondition {X Y : Type*}
    (relation : SetRel X Y) (source : Set X) : Set Y :=
  SetRel.image relation source

/-- A Boolean relation with both outcomes available from `false`. -/
def nondeterministicBooleanRelation : SetRel Bool Bool :=
  {(source, _target) | source = false}

/-- The successful Boolean outcome used by the public may/must contrast. -/
def successfulOutcome : Set Bool := {true}

/-- Relational strongest postcondition and universal weakest precondition form
an adjunction. Independently, the explicit nondeterministic Boolean relation
has a successful path from `false` but does not guarantee success there. -/
theorem relational_adjunction_and_may_not_guarantee
    {X Y : Type*} (relation : SetRel X Y)
    (source : Set X) (target : Set Y) :
    (relationalStrongestPostcondition relation source ⊆ target ↔
      source ⊆ universalWeakestPrecondition relation target) ∧
      (false ∈ existentialPrecondition
          nondeterministicBooleanRelation successfulOutcome ∧
        false ∉ universalWeakestPrecondition
          nondeterministicBooleanRelation successfulOutcome) := by
  constructor
  · simpa only [relationalStrongestPostcondition,
      universalWeakestPrecondition] using
      (SetRel.image_subset_iff (R := relation) (s := source) (t := target))
  · constructor
    · exact ⟨true, Set.mem_singleton true, rfl⟩
    · intro guaranteed
      exact Bool.false_ne_true (guaranteed (b := false) rfl)

/- The source and target relation carriers used by the contrast are inhabited. -/
example : Bool × Bool := (false, true)

/- The explicit countermodel witnesses both independent public contrast clauses. -/
example :
    false ∈ existentialPrecondition
        nondeterministicBooleanRelation successfulOutcome ∧
      false ∉ universalWeakestPrecondition
        nondeterministicBooleanRelation successfulOutcome := by
  exact (relational_adjunction_and_may_not_guarantee
    nondeterministicBooleanRelation Set.univ successfulOutcome).2

#print axioms relational_adjunction_and_may_not_guarantee

end D5.S3.ObserverMemory.Knowledge.RelationalPreconditionAdjunction

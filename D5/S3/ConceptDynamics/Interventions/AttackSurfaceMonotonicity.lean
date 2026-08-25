/- GID: D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Permission expansion enlarges reachable states and can do so strictly. -/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'reach_monotone_in_permissions' D5 Golden/Frozen/accepted`
     found no existing declaration.
   * Repository searches for reachability and `ReflTransGen` found
     `Control.FiniteHorizonReachability`, which concerns bounded adversarial control
     strategies rather than closure under an allowed permission set, and no matching
     monotonicity theorem or strict Boolean witness.
   * Pinned Mathlib provides the exact closure transport lemma
     `Relation.ReflTransGen.mono` in `Mathlib.Logic.Relation`; it is reused below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Interventions.AttackSurfaceMonotonicity

/-- States reachable from `start` by finitely many transitions whose permissions
all belong to `allowed`. -/
def Reach {State Permission : Type*} (step : Permission -> State -> State -> Prop)
    (allowed : Set Permission) (start : State) : Set State :=
  {target | Relation.ReflTransGen
    (fun source target => exists permission, permission ∈ allowed ∧
      step permission source target) start target}

/-- Enlarging the permission set can only enlarge the reachable set.

This covariance contrasts with experiment expansion: more experiments refine
distinguishability and therefore shrink indistinguishable pairs, whereas more
permissions enlarge the range of states the system can reach. -/
theorem reach_monotone_in_permissions
    {State Permission : Type*} (step : Permission -> State -> State -> Prop)
    {P Q : Set Permission} {start : State} (hPermissions : P ⊆ Q) :
    Reach step P start ⊆ Reach step Q start := by
  intro target reachable
  induction reachable with
  | refl => exact Relation.ReflTransGen.refl
  | tail path permittedStep ih =>
      rcases permittedStep with ⟨permission, permissionAllowed, transition⟩
      exact Relation.ReflTransGen.tail ih
        ⟨permission, hPermissions permissionAllowed, transition⟩

/-- Intersecting both attack surfaces with the bad states preserves the inclusion. -/
theorem bad_state_reach_monotone
    {State Permission : Type*} (step : Permission -> State -> State -> Prop)
    {P Q : Set Permission} {start : State} (bad : Set State)
    (hPermissions : P ⊆ Q) :
    Reach step P start ∩ bad ⊆ Reach step Q start ∩ bad := by
  rintro target ⟨reachable, targetBad⟩
  exact ⟨reach_monotone_in_permissions step hPermissions reachable, targetBad⟩

/-- With no Boolean action only `false` is reachable from `false`; allowing negation
adds `true`, so permission and reachable-set growth can both be strict. -/
theorem strict_growth_witness :
    exists P Q : Set (Bool -> Bool),
      P ⊂ Q ∧
        Reach (fun permission source target => permission source = target) P false ⊂
          Reach (fun permission source target => permission source = target) Q false := by
  refine ⟨(∅ : Set (Bool -> Bool)), ({Bool.not} : Set (Bool -> Bool)), ?_, ?_⟩
  · refine (Set.ssubset_iff_of_subset (Set.empty_subset _)).2 ?_
    exact ⟨Bool.not, rfl, fun permissionAllowed => permissionAllowed⟩
  · refine (Set.ssubset_iff_of_subset ?_).2 ?_
    · exact reach_monotone_in_permissions
        (P := (∅ : Set (Bool -> Bool))) (Q := {Bool.not}) (start := false)
        (fun (permission : Bool -> Bool) (source target : Bool) =>
          permission source = target)
        (Set.empty_subset _)
    · refine ⟨true, ?_, ?_⟩
      · exact Relation.ReflTransGen.single ⟨Bool.not, rfl, rfl⟩
      · intro reachable
        have noStep : ∀ target : Bool,
            ¬(exists permission : Bool -> Bool,
              permission ∈ (∅ : Set (Bool -> Bool)) ∧ permission false = target) := by
          intro target transition
          obtain ⟨permission, permissionAllowed, _⟩ := transition
          exact permissionAllowed
        exact Bool.false_ne_true (Relation.reflTransGen_iff_eq noStep |>.mp reachable).symm

example :
    true ∈ Reach (fun permission source target => permission source = target)
      ({Bool.not} : Set (Bool -> Bool)) false := by
  exact Relation.ReflTransGen.single ⟨Bool.not, rfl, rfl⟩

#print axioms reach_monotone_in_permissions

end D5.S3.ConceptDynamics.Interventions.AttackSurfaceMonotonicity

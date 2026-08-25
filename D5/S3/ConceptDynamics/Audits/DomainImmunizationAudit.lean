/- GID: D5/S3/ConceptDynamics/Audits/DomainImmunizationAudit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/DomainImmunizationAudit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target-dependent domain restriction can hide defects while deleting states. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Data.Set.Card

/- Library-search audit trail (2026-08-25):
   * Exact family hit `defectRelation` constructs the target-sensitive collision
     set and is imported rather than redeclared.
   * The adjacent target-recovery criterion characterizes empty whole-domain
     defects, but it does not restrict admission domains or count deletions.
   * Repository searches found no theorem combining the shrink construction,
     full-domain contrast, target-dependent audit, and cumulative exclusions.
   * Pinned Mathlib provides `Set.ncard_compl`, singleton-cardinality lemmas,
     `Set.compl_subset_compl_of_subset`, and `Set.ssubset_iff_exists`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.DomainImmunizationAudit

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Every defective finite readout can be made defect-free on a target-selected
singleton domain, with the deleted-state count exposed. A Boolean model shows
that zero restricted defects do not imply a full-domain law and that admission
can be defined by the target. Cumulative counterexample exclusion remains closed
while its admitted domains shrink in the reverse order. -/
theorem domain_immunization_audit :
    (forall (X Coordinate Target : Type*) [Finite X]
      (readout : Concept X Coordinate) (target : Concept X Target),
      (defectRelation readout target).Nonempty ->
        exists counterexample : X × X, exists admitted : Set X,
          counterexample ∈ defectRelation readout target ∧
          admitted = {counterexample.1} ∧
          defectRelation
              (fun state : admitted => readout state.1)
              (fun state : admitted => target state.1) = ∅ ∧
          admitted.ncard = 1 ∧
          admittedᶜ.ncard = Nat.card X - 1) ∧
    (let readout : Concept Bool Unit := fun _ => ()
     let target : Concept Bool Bool := id
     let admitted : Set Bool := {state | target state = false}
     (defectRelation readout target).Nonempty ∧
       defectRelation
           (fun state : admitted => readout state.1)
           (fun state : admitted => target state.1) = ∅ ∧
       admitted.ncard = 1 ∧
       admittedᶜ.ncard = 1 ∧
       forall state, state ∈ admitted ↔ target state = false) ∧
    (forall (State : Type*) (counterexamples : Nat -> Set State),
      Monotone counterexamples ->
        exists admissions : Nat -> Set State,
          (forall stage, admissions stage = (counterexamples stage)ᶜ) ∧
          Antitone admissions ∧
          (forall stage,
            admissions stage ∩ counterexamples stage = ∅) ∧
          (forall stage,
            counterexamples stage ⊂ counterexamples (stage + 1) ->
              admissions (stage + 1) ⊂ admissions stage)) := by
  classical
  constructor
  · intro X Coordinate Target _ readout target defect_nonempty
    rcases defect_nonempty with ⟨counterexample, counterexample_defect⟩
    refine ⟨counterexample, {counterexample.1}, counterexample_defect, rfl, ?_, by simp, ?_⟩
    · ext pair
      rcases pair with ⟨left, right⟩
      simp only [defectRelation, Set.mem_setOf_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨_same_readout, different_target⟩
      have left_eq : left.1 = counterexample.1 :=
        Set.mem_singleton_iff.mp left.2
      have right_eq : right.1 = counterexample.1 :=
        Set.mem_singleton_iff.mp right.2
      exact different_target (congrArg target (left_eq.trans right_eq.symm))
    · simpa using (Set.ncard_compl ({counterexample.1} : Set X))
  · constructor
    · dsimp
      refine ⟨⟨(false, true), rfl, Bool.false_ne_true⟩, ?_, ?_, ?_, ?_⟩
      · apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨⟨left, right⟩, _same_readout, different_target⟩
        have left_eq : left.1 = false := Set.mem_singleton_iff.mp left.2
        have right_eq : right.1 = false := Set.mem_singleton_iff.mp right.2
        exact different_target (left_eq.trans right_eq.symm)
      · simp
      · rw [show ({false} : Set Bool)ᶜ = {true} by
          ext state
          cases state <;> simp]
        simp
      · intro state
        rfl
    · intro State counterexamples counterexamples_monotone
      refine ⟨fun stage => (counterexamples stage)ᶜ, fun _ => rfl, ?_, ?_, ?_⟩
      · intro first second first_le_second
        exact Set.compl_subset_compl_of_subset
          (counterexamples_monotone first_le_second)
      · intro stage
        simp
      · intro stage strict_growth
        refine Set.ssubset_iff_exists.mpr ⟨?_, ?_⟩
        · exact Set.compl_subset_compl_of_subset strict_growth.le
        · rcases Set.exists_of_ssubset strict_growth with
            ⟨new_counterexample, new_at_next, absent_before⟩
          exact ⟨new_counterexample, absent_before, by simpa using new_at_next⟩

#print axioms domain_immunization_audit

end D5.S3.ConceptDynamics.Audits.DomainImmunizationAudit

/- GID: D5/S3/ConceptDynamics/Audits/TargetConditionedAdmissionAudit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/TargetConditionedAdmissionAudit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target-conditioned admission can erase defects only by deleting states. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Data.Set.Card

/- Library-search audit trail (2026-08-25):
   * Exact family hit `defectRelation` constructs target-sensitive readout
     collisions and is imported rather than redeclared.
   * The frozen domain-immunization predecessor contains a retracted
     definition-unfolding clause, so it is neither imported nor wrapped.
   * Repository body-shape searches found restriction and strict-subset proof
     patterns, but no theorem with this witnessed-deletion, target-dependence,
     and successive-exclusion statement.
   * Pinned Mathlib exact hits `Set.ncard_pos`, `Set.diff_subset`, and
     `Set.ssubset_iff_exists` are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.TargetConditionedAdmissionAudit

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A witnessed target defect can be erased on a singleton domain only while
deleting at least one state. A Boolean model separates restricted closure from
the whole-domain law and exposes target-dependent admission. Removing each
currently admitted counterexample excludes it and strictly shrinks the next
admission domain. -/
theorem target_conditioned_admission_audit :
    (forall (X Coordinate Target : Type*) [Finite X]
      (readout : Concept X Coordinate) (target : Concept X Target),
      (defectRelation readout target).Nonempty ->
        exists counterexample : X × X,
          counterexample ∈ defectRelation readout target ∧
          defectRelation
              (fun state : ({counterexample.1} : Set X) => readout state.1)
              (fun state : ({counterexample.1} : Set X) => target state.1) = ∅ ∧
          0 < (({counterexample.1} : Set X)ᶜ).ncard) ∧
    (let readout : Concept Bool Unit := fun _ => ()
     let admissionRule : Concept Bool Bool -> Set Bool :=
       fun target => {state | target state = false}
     (defectRelation readout (id : Concept Bool Bool)).Nonempty ∧
       defectRelation
           (fun state : admissionRule id => readout state.1)
           (fun state : admissionRule id => id state.1) = ∅ ∧
       admissionRule id ≠ admissionRule Bool.not ∧
       (admissionRule id)ᶜ.ncard = 1) ∧
    (forall (State : Type*) (admissions : Nat -> Set State)
      (counterexample : Nat -> State),
      (forall stage, counterexample stage ∈ admissions stage) ->
      (forall stage,
        admissions (stage + 1) =
          admissions stage \ {counterexample stage}) ->
      forall stage,
        counterexample stage ∉ admissions (stage + 1) ∧
          admissions (stage + 1) ⊂ admissions stage) := by
  classical
  constructor
  · intro X Coordinate Target _ readout target defectNonempty
    rcases defectNonempty with ⟨counterexample, counterexampleDefect⟩
    refine ⟨counterexample, counterexampleDefect, ?_, ?_⟩
    · apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨⟨left, right⟩, _sameReadout, differentTarget⟩
      have leftEq : left.1 = counterexample.1 :=
        Set.mem_singleton_iff.mp left.2
      have rightEq : right.1 = counterexample.1 :=
        Set.mem_singleton_iff.mp right.2
      exact differentTarget (congrArg target (leftEq.trans rightEq.symm))
    · have stateDifferent : counterexample.1 ≠ counterexample.2 := by
        intro statesEqual
        exact counterexampleDefect.2 (congrArg target statesEqual)
      apply (Set.ncard_pos).2
      refine ⟨counterexample.2, ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact stateDifferent.symm
  · constructor
    · dsimp
      refine ⟨⟨(false, true), rfl, Bool.false_ne_true⟩, ?_, ?_, ?_⟩
      · apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨⟨left, right⟩, _sameReadout, differentTarget⟩
        have leftEq : left.1 = false := Set.mem_singleton_iff.mp left.2
        have rightEq : right.1 = false := Set.mem_singleton_iff.mp right.2
        exact differentTarget (leftEq.trans rightEq.symm)
      · intro sameDomains
        have falseAdmitted : false ∈ ({false} : Set Bool) := Set.mem_singleton false
        rw [sameDomains] at falseAdmitted
        simp at falseAdmitted
      · rw [show ({false} : Set Bool)ᶜ = {true} by
          ext state
          cases state <;> simp]
        simp
    · intro State admissions counterexample currentlyAdmitted removesCurrent stage
      constructor
      · rw [removesCurrent stage]
        simp
      · rw [removesCurrent stage]
        apply Set.ssubset_iff_exists.mpr
        refine ⟨Set.sdiff_subset, counterexample stage, currentlyAdmitted stage, ?_⟩
        simp

#print axioms target_conditioned_admission_audit

end D5.S3.ConceptDynamics.Audits.TargetConditionedAdmissionAudit

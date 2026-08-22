/- GID: D5/S3/ConceptDynamics/Trust/TypedTrustComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Trust/TypedTrustComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed trust composes exactly when target distinctions align with report interfaces. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'typed_trust_composes_iff_interfaces_align' D5
     Golden/Frozen/accepted` returned no matches.
   * `rg -in 'transitiv' D5/S3/ | head -20` found
     `RefinementTransitivity.refinement_transitive`, which is reused for positive
     composition rather than reproved.
   * The factorization search found pinned-Mathlib
     `Function.factorsThrough_iff`; it is reused for the interface-alignment iff.
   * `history_sensitive_evaluation_not_outcome_reducible` is reused to prove the
     `snd`-through-`fst` obstruction in the explicit counterexample.
   * No repository theorem combines composition, the alignment characterization,
     and a scope/target-mismatch counterexample, so the target is not covered. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Trust.TypedTrustComposition

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.NormativeStructure.HistorySensitiveOutcomeReductionObstruction

/-- A report interface aligns with a target when the target is constant on every
fiber of the report. -/
def InterfacesAlign {State Report Target : Type*} (report : Concept State Report)
    (target : Concept State Target) : Prop :=
  ∀ ⦃first second : State⦄, report first = report second → target first = target second

/-- Typed trust composes along an aligned report chain, is exactly fiber alignment,
and fails in general when an intermediate scope omits a target-relevant distinction. -/
theorem typed_trust_composes_iff_interfaces_align :
    (∀ {State CReport BReport Target : Type*}
      (reportC : Concept State CReport) (reportB : Concept State BReport)
      (target : Concept State Target),
      Refines reportB reportC → Refines target reportB → Refines target reportC) ∧
    (∀ {State Report Target : Type*} [Nonempty Target]
      (report : Concept State Report) (target : Concept State Target),
      Refines target report ↔ InterfacesAlign report target) ∧
    ∃ (reportC : Concept (Bool × Bool) Bool)
      (reportB : Concept (Bool × Bool) (Bool × Bool))
      (scope target : Concept (Bool × Bool) Bool),
      Refines target reportB ∧ Refines scope reportC ∧ ¬Refines target reportC := by
  constructor
  · intro State CReport BReport Target reportC reportB target hCB hBT
    exact refinement_transitive target reportB reportC hCB hBT
  constructor
  · intro State Report Target _ report target
    change (∃ factor : Report → Target, target = factor ∘ report) ↔
      Function.FactorsThrough target report
    exact (Function.factorsThrough_iff (f := report) target).symm
  · refine ⟨Prod.fst, id, Prod.fst, Prod.snd, ?_⟩
    constructor
    · exact ⟨Prod.snd, by funext state; rfl⟩
    constructor
    · exact ⟨id, by funext state; rfl⟩
    · apply history_sensitive_evaluation_not_outcome_reducible
      exact ⟨(false, false), (false, true), rfl, Bool.false_ne_true⟩

example :
    InterfacesAlign (fun state : Bool × Bool => state.1) (fun state => state.1) := by
  intro first second sameReport
  exact sameReport

#print axioms typed_trust_composes_iff_interfaces_align

end D5.S3.ConceptDynamics.Trust.TypedTrustComposition

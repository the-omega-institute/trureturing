/- GID: D5/S3/ConceptDynamics/Rights/ViolationEnforceabilityCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Rights/ViolationEnforceabilityCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact violation enforcement is equivalent to audit-interface sufficiency. -/

import D5.S3.ConceptDynamics.Communication.HeterogeneousFiberMisclassification
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-25):
   * Searches for exact violation executors, enforcement criteria, canonical
     violation refinement, and the full collision consequence found no exact
     D5 theorem.
   * Exact repository hits `target_recovery_criterion` and
     `universal_sufficiency_factorization` identify raw Boolean factorization
     and canonical effective-target refinement with the same fiber condition.
   * Exact repository hit `heterogeneous_fiber_forces_misclassification`
     supplies the universal two-event error disjunction and is applied directly.
   * Pinned Mathlib's exact `Function.factorsThrough_iff` theorem is applied by
     the imported recovery criterion; core `Bool.false_ne_true` separates the
     explicit rights-interface countermodel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Rights.ViolationEnforceabilityCriterion

open D5.S3.ConceptDynamics.Communication.HeterogeneousFiberMisclassification
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Exact Boolean violation enforcement is equivalent to sufficiency of the
audit interface for the canonical violation target. A heterogeneous log fiber
forces every log-only enforcer to err on one of its two events, and a concrete
Boolean model shows that declaring a violation target does not itself provide
a sufficient audit interface. -/
theorem violation_enforceability_criterion
    {Event Log : Type*} [Nonempty Event]
    (auditLog : Concept Event Log) (violation : Concept Event Bool) :
    ((∃ enforcer : Log → Bool, violation = enforcer ∘ auditLog) ↔
      Refines (canonicalTargetReadout violation) auditLog) ∧
    (∀ ⦃event event' : Event⦄,
      auditLog event = auditLog event' →
      violation event ≠ violation event' →
      ∀ enforcer : Log → Bool,
        enforcer (auditLog event) ≠ violation event ∨
          enforcer (auditLog event') ≠ violation event') ∧
    (∃ declaredViolation : Concept Bool Bool,
      ∃ interface : Concept Bool Unit,
        (∃ event event' : Bool,
          interface event = interface event' ∧
            declaredViolation event ≠ declaredViolation event') ∧
        ¬ Refines (canonicalTargetReadout declaredViolation) interface) := by
  constructor
  · have recoveryCriterion :=
      (target_recovery_criterion auditLog violation).1
    have effectiveCriterion :=
      (universal_sufficiency_factorization auditLog violation).1.trans
        (universal_sufficiency_factorization auditLog violation).2
    exact recoveryCriterion.trans effectiveCriterion.symm
  constructor
  · intro event event' sameLog differentViolation
    exact heterogeneous_fiber_forces_misclassification
      auditLog violation event event' ⟨sameLog, differentViolation⟩
  · refine ⟨id, fun _ => (), ⟨false, true, rfl, Bool.false_ne_true⟩, ?_⟩
    rintro ⟨factor, targetFactors⟩
    have sameTarget :
        canonicalTargetReadout (id : Bool → Bool) false =
          canonicalTargetReadout (id : Bool → Bool) true := by
      rw [targetFactors]
      rfl
    exact Bool.false_ne_true (congrArg Subtype.val sameTarget)

#print axioms violation_enforceability_criterion

end D5.S3.ConceptDynamics.Rights.ViolationEnforceabilityCriterion

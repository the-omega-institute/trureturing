/- GID: D5/S3/ConceptDynamics/Audits/ProcedureDerivedCorrectOutcome
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/ProcedureDerivedCorrectOutcome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A procedure-derived judgment may be correct while its certificate escapes the log. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-25):
   * Searches for correct-outcome/procedure/oracle contrasts found only the frozen
     `OutcomeCorrectnessWithoutProcedureAudit`, whose independent judgment witness
     is the separable construction this fresh module repairs.
   * `Concept`, `Refines`, `conceptJoin`, `TargetImage`, `canonicalTargetReadout`,
     and `refinement_transitive` are the canonical family primitives and are
     imported rather than redeclared.
   * A body-shape search for an oracle composed with the nested four-channel
     certificate found no existing D5 construction.
   * Pinned Mathlib supplies generic function composition but no exact theorem
     combining correct target recovery with failure of procedure auditability. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.ProcedureDerivedCorrectOutcome

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- An oracle can derive the designated target from the canonical four-channel
procedure certificate even though that same certificate cannot be recovered from
the audit log. The judgment is the displayed composite through the certificate,
not an independent witness chosen equal to the target. -/
theorem procedure_derived_correct_outcome_can_lack_auditability
    (target : Concept Bool Bool) :
    ∃ rules : Concept Bool Unit,
      ∃ authorization : Concept Bool (TargetImage (id : Bool → Bool)),
        ∃ hearing : Concept Bool Unit,
          ∃ provenance : Concept Bool Unit,
            ∃ log : Concept Bool Unit,
              ∃ oracle :
                  (((Unit × TargetImage (id : Bool → Bool)) × Unit) × Unit) → Bool,
                oracle ∘
                    conceptJoin
                      (conceptJoin (conceptJoin rules authorization) hearing)
                      provenance = target ∧
                  ¬ Refines
                    (conceptJoin
                      (conceptJoin (conceptJoin rules authorization) hearing)
                      provenance)
                    log := by
  let rules : Concept Bool Unit := fun _ => ()
  let authorization : Concept Bool (TargetImage (id : Bool → Bool)) :=
    canonicalTargetReadout id
  let hearing : Concept Bool Unit := fun _ => ()
  let provenance : Concept Bool Unit := fun _ => ()
  let log : Concept Bool Unit := fun _ => ()
  let firstCertificate := conceptJoin rules authorization
  let secondCertificate := conceptJoin firstCertificate hearing
  let procedureCertificate := conceptJoin secondCertificate provenance
  have authorizationRefinesFirst : Refines authorization firstCertificate :=
    (concept_join_universal rules authorization firstCertificate).2.1
  have firstRefinesSecond : Refines firstCertificate secondCertificate :=
    (concept_join_universal firstCertificate hearing secondCertificate).1
  have authorizationRefinesSecond : Refines authorization secondCertificate :=
    refinement_transitive authorization firstCertificate secondCertificate
      firstRefinesSecond authorizationRefinesFirst
  have secondRefinesProcedure : Refines secondCertificate procedureCertificate :=
    (concept_join_universal secondCertificate provenance procedureCertificate).1
  have authorizationRefinesProcedure : Refines authorization procedureCertificate :=
    refinement_transitive authorization secondCertificate procedureCertificate
      secondRefinesProcedure authorizationRefinesSecond
  obtain ⟨recoverAuthorization, authorizationFactors⟩ :=
    authorizationRefinesProcedure
  let oracle :
      (((Unit × TargetImage (id : Bool → Bool)) × Unit) × Unit) → Bool :=
    target ∘ Subtype.val ∘ recoverAuthorization
  refine ⟨rules, authorization, hearing, provenance, log, oracle, ?_, ?_⟩
  · funext state
    have recoveredState :
        (recoverAuthorization (procedureCertificate state)).val = state := by
      have recoveredAuthorization := congrFun authorizationFactors state
      have recoveredValue := congrArg Subtype.val recoveredAuthorization
      calc
        (recoverAuthorization (procedureCertificate state)).val =
            (authorization state).val := recoveredValue.symm
        _ = state := by rfl
    change target ((recoverAuthorization (procedureCertificate state)).val) = target state
    rw [recoveredState]
  · rintro ⟨factorThroughLog, certificateFactors⟩
    have procedureFactors : procedureCertificate = factorThroughLog ∘ log := by
      simpa only [procedureCertificate, secondCertificate, firstCertificate] using
        certificateFactors
    have sameCertificate : procedureCertificate false = procedureCertificate true := by
      rw [procedureFactors]
      rfl
    have sameAuthorization : authorization false = authorization true :=
      congrArg (fun certificate => certificate.1.1.2) sameCertificate
    have sameState : false = true := by
      calc
        false = (authorization false).val := by rfl
        _ = (authorization true).val := congrArg Subtype.val sameAuthorization
        _ = true := by rfl
    exact Bool.false_ne_true sameState

#print axioms procedure_derived_correct_outcome_can_lack_auditability

end D5.S3.ConceptDynamics.Audits.ProcedureDerivedCorrectOutcome

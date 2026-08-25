/- GID: D5/S3/ConceptDynamics/Audits/OutcomeCorrectnessWithoutProcedureAudit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Audits/OutcomeCorrectnessWithoutProcedureAudit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A correct judgment can coexist with a procedure certificate absent from its audit log. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-25):
   * The exact D5 hit `CorrectnessLegitimacySeparation` concerns predicates on
     correct-result fibers and already serves a different atom; it does not
     expose the source's four-channel procedure certificate or audit log.
   * Searches for nested four-channel joins, procedure auditability, and the
     full correct-outcome contrast found no exact repository theorem.
   * `Concept`, `Refines`, and `conceptJoin` are the canonical family primitives
     and are used directly; no procedure-certificate wrapper is declared.
   * The pinned environment's exact `Bool.false_ne_true` theorem supplies the
     final Boolean distinction. No broader library result is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Audits.OutcomeCorrectnessWithoutProcedureAudit

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- An oracle can return any designated Boolean target exactly while the
canonical rules-authorization-hearing-provenance certificate still does not
factor through the available audit log. -/
theorem correct_outcome_can_lack_procedure_auditability
    (target : Concept Bool Bool) :
    ∃ rules : Concept Bool Unit,
      ∃ authorization : Concept Bool Bool,
        ∃ hearing : Concept Bool Unit,
          ∃ provenance : Concept Bool Unit,
            ∃ judgment : Concept Bool Bool,
              ∃ log : Concept Bool Unit,
                judgment = target ∧
                  ¬ Refines
                    (conceptJoin
                      (conceptJoin (conceptJoin rules authorization) hearing)
                      provenance)
                    log := by
  refine ⟨fun _ => (), id, fun _ => (), fun _ => (), target, fun _ => (), rfl, ?_⟩
  rintro ⟨factor, certificateFactors⟩
  have sameCertificate :
      conceptJoin
          (conceptJoin
            (conceptJoin (fun _ : Bool => ()) (id : Concept Bool Bool))
            (fun _ : Bool => ()))
          (fun _ : Bool => ()) false =
        conceptJoin
          (conceptJoin
            (conceptJoin (fun _ : Bool => ()) (id : Concept Bool Bool))
            (fun _ : Bool => ()))
          (fun _ : Bool => ()) true := by
    rw [certificateFactors]
    rfl
  exact Bool.false_ne_true
    (congrArg (fun certificate => certificate.1.1.2) sameCertificate)

#print axioms correct_outcome_can_lack_procedure_auditability

end D5.S3.ConceptDynamics.Audits.OutcomeCorrectnessWithoutProcedureAudit

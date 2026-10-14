import Reg.Support.DecoderStartupCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderStartup
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

def initial_drain_of_acquired_run_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.initial_drain_of_acquired_run.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.initial_drain_of_acquired_run_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.initialDrainEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.initialDrainArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.initialDrainArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.initialDrainArena.{u_1,u_2,u_3} ⟨Cohort.initialDrainEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderStartup
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def processing_of_safe_live_pair_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.processing_of_safe_live_pair.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 (max u_2 u_3), 0, max u_1 (max u_2 u_3), 0}
        Cohort.processingSignature.{u_1,u_2,u_3} Cohort.processingReadout.{u_1,u_2,u_3} Cohort.processingAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.processing_of_safe_live_pair_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.processingPairEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.processingPairArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.processingPairArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.processingPairArena.{u_1,u_2,u_3} ⟨Cohort.processingPairEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 (max u_2 u_3), 0, max u_1 (max u_2 u_3), 0}
        Cohort.processingSignature.{u_1,u_2,u_3} Cohort.processingReadout.{u_1,u_2,u_3} Cohort.processingAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderStartup
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

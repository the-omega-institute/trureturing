import Reg.Support.DecoderReplayCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderReplay
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay

universe u_1 u_2 u_3
noncomputable section

def trace_replay_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_replay.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullSignature.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullReadout.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.trace_replay_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.Cohort.traceReplayEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.traceReplayArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.traceReplayArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.traceReplayArena.{u_1,u_2,u_3} ⟨Cohort.traceReplayEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullSignature.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullReadout.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderReplay
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "domain", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def actual_address_eq_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_address_eq.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runFullSignature.{u_1,u_2,u_3} Cohort.runFullReadout.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.actual_address_eq_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay.Cohort.actualAddressEqEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.actualAddressEqArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.actualAddressEqArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.actualAddressEqArena.{u_1,u_2,u_3} ⟨Cohort.actualAddressEqEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runFullSignature.{u_1,u_2,u_3} Cohort.runFullReadout.{u_1,u_2,u_3} _root_.Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.fullAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderReplay
    definition := none
    coordinates := #[0, 1, 2, 3, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "body", "body", "domain", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderReplay

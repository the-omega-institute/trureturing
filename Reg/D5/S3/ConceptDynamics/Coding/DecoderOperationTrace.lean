import Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
import Reg.Support.DecoderOperationReadouts
import Reg.Support.DecoderOperationTraceCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

def trace_replay_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_replay.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_replay_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.traceReplayEvidence
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
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})
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
        Cohort.runFullSignature.{u_1,u_2,u_3} Cohort.runFullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_address_eq_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.actualAddressEqEvidence
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
        Cohort.runFullSignature.{u_1,u_2,u_3} Cohort.runFullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})
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

def peak_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_bound.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.peakBoundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.peakBoundArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.peakBoundArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.peakBoundArena.{u_1,u_2,u_3} ⟨Cohort.peakBoundEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderPeak
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def peak_trace_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_trace_bound.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_trace_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.peakTraceBoundEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.peakTraceBoundArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.peakTraceBoundArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.peakTraceBoundArena.{u_1,u_2,u_3} ⟨Cohort.peakTraceBoundEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderPeak
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def peak_monotone_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_monotone.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_monotone_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.peakMonotoneEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.peakMonotoneArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.peakMonotoneArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.peakMonotoneArena.{u_1,u_2,u_3} ⟨Cohort.peakMonotoneEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderPeak
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203
noncomputable section

def paired_source_reconstruction_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ z => compose C z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ z => compose C z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms paired_source_reconstruction_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202
noncomputable section

def literal_source_geometry_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_source_geometry)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ w => compose w) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202.literal_source_geometry_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ _ w => compose w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms literal_source_geometry_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal202

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204
noncomputable section
open Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.LiteralBranchReadout

def literal_address_path_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.literal_address_path)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204.literal_address_path_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
        (fun _ _ l => branch l) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms literal_address_path_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal204

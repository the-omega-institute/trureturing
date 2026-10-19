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

def step_unique_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.step_unique_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.stepRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨stepArena⟩
  objectArena := .source ⟨stepArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stepArena ⟨stepRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Step p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def trace_closure_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure.{u_1,u_2,u_3})
      (type_of% (realize traceSignature.{u_1,u_2,u_3}
        (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_closure_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.traceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    traceSignature.{u_1,u_2,u_3}
    (fun _ p s => Trace p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_closure_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_closure_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runClosureRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runClosureArena⟩
  objectArena := .source ⟨runClosureArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runClosureArena ⟨runClosureRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_trans_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_trans_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runTransRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runTransArena⟩
  objectArena := .source ⟨runTransArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runTransArena ⟨runTransRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def run_comparable_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable.{u_1,u_2,u_3})
      (type_of% (realize relationSignature.{u_1,u_2,u_3}
        (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s) (fun (e : Empty) _ => Empty.elim e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_comparable_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.runComparableRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨runComparableArena⟩
  objectArena := .source ⟨runComparableArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runComparableArena ⟨runComparableRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (@_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
    relationSignature.{u_1,u_2,u_3}
    (fun _ p s => Run p.2.2.2.1 p.2.2.2.2 s)
    (fun (e : Empty) _ => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

universe u_1 u_2 u_3
noncomputable section

def run_mono_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_mono.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.run_mono_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.runMonoEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.runMonoArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.runMonoArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.runMonoArena.{u_1,u_2,u_3} ⟨Cohort.runMonoEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def trace_input_transfer_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_input_transfer.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.traceSignature.{u_1,u_2,u_3} Cohort.traceReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.trace_input_transfer_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.traceInputTransferEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.traceInputTransferArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.traceInputTransferArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.traceInputTransferArena.{u_1,u_2,u_3} ⟨Cohort.traceInputTransferEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.traceSignature.{u_1,u_2,u_3} Cohort.traceReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def prefix_trace_iff_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.prefix_trace_iff.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.prefix_trace_iff_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.prefixTraceIffEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.prefixTraceIffArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.prefixTraceIffArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.prefixTraceIffArena.{u_1,u_2,u_3} ⟨Cohort.prefixTraceIffEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.fullSignature.{u_1,u_2,u_3} Cohort.fullReadout.{u_1,u_2,u_3} Cohort.fullAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def cut_unique_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.cut_unique.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.cut_unique_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.cutUniqueEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.cutUniqueArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.cutUniqueArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.cutUniqueArena.{u_1,u_2,u_3} ⟨Cohort.cutUniqueEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "domain", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def drain_acquired_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_acquired.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_acquired_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.drainAcquiredEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.drainAcquiredArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.drainAcquiredArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.drainAcquiredArena.{u_1,u_2,u_3} ⟨Cohort.drainAcquiredEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.drainSignature.{u_1,u_2,u_3} Cohort.drainReadout.{u_1,u_2,u_3} Cohort.drainAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def drain_run_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_run.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.drain_run_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.drainRunEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.drainRunArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.drainRunArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.drainRunArena.{u_1,u_2,u_3} ⟨Cohort.drainRunEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), max u_1 u_3, 0, max u_1 u_3, 0}
        Cohort.runSignature.{u_1,u_2,u_3} Cohort.runReadout.{u_1,u_2,u_3} Cohort.inputAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def actual_cut_exists_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_cut_exists.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.actual_cut_exists_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Cohort.actualCutExistsEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨Cohort.actualCutExistsArena.{u_1,u_2,u_3}⟩
  objectArena := .source ⟨Cohort.actualCutExistsArena.{u_1,u_2,u_3}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Cohort.actualCutExistsArena.{u_1,u_2,u_3} ⟨Cohort.actualCutExistsEvidence.{u_1,u_2,u_3}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_2, 0, max u_1 u_3, 0}
        Cohort.cutSignature.{u_1,u_2,u_3} Cohort.cutReadout.{u_1,u_2,u_3} Cohort.cutAnchor.{u_1,u_2,u_3})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Basic
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

import Reg.Support.DecoderPeakCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderPeak
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak

universe u_1 u_2 u_3
noncomputable section

def peak_bound_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.peak_bound.{u_1,u_2,u_3})
      (type_of% (realize.{max (u_1 + 1) (max (u_2 + 1) (u_3 + 1)), u_1, 0, 0, 0}
        Cohort.peakSignature.{u_1,u_2,u_3} Cohort.peakReadout.{u_1,u_2,u_3} Cohort.peakAnchor.{u_1,u_2,u_3})) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.peak_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.Cohort.peakBoundEvidence
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.peak_trace_bound_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.Cohort.peakTraceBoundEvidence
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
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.peak_monotone_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak.Cohort.peakMonotoneEvidence
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

end Reg.D5.S3.ConceptDynamics.Coding.DecoderPeak

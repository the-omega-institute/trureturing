import Reg.D5.S3.ConceptDynamics.Coding.Decoder.Trace
import Reg.Support.DecoderOperationReadouts
import Reg.Support.DecoderOperationTraceCohort
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import Reg.Support.DependentFamily


open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

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

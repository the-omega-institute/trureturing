import Reg.Support.ThetaShearMonotonicity

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaShearMonotonicity

namespace Reg.D5.S3.Fourier.ThetaShearMonotonicity
noncomputable section

def registration_derivative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shear_derivative_neg) (type_of% (realize shearSignature
      (fun _ p x => deriv (fun z => F p.1 z p.2) x) (fun e => nomatch e)))
    Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.shear_derivative_neg.information_unit,
  realizationName := `Reg.Support.ThetaShearMonotonicity.shearRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨shearArena⟩, objectArena := .source ⟨shearArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source shearArena ⟨shearRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize shearSignature
    (fun _ p x => deriv (fun z => F p.1 z p.2) x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaShearMonotonicity, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_minimum : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@shear_minimum) (type_of% (realize shearSignature
      (fun _ p x => F p.1 x p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.shear_minimum.information_unit,
  realizationName := `Reg.Support.ThetaShearMonotonicity.minimumRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨minimumArena⟩, objectArena := .source ⟨minimumArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source minimumArena ⟨minimumRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize shearSignature
    (fun _ p x => F p.1 x p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaShearMonotonicity, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaShearMonotonicity

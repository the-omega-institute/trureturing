import Reg.Support.HexagonalThetaMinimum

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaVerticalTail

namespace Reg.D5.S3.Fourier.ThetaVerticalTail
noncomputable section

def registration_negative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@vertical_negative_bound) (type_of% (realize negativeSignature
      (fun _ t y => verticalNegative t y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.vertical_negative_bound.information_unit,
  realizationName := `Reg.Support.ThetaVerticalTail.negativeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨negativeArena⟩, objectArena := .source ⟨negativeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source negativeArena ⟨negativeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize negativeSignature
    (fun _ t y => verticalNegative t y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaMinimum, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaVerticalTail

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaVerticalPositive
open Reg.Support.PlanarThetaFoundation
open Reg.Support.HexagonalThetaMinimum

namespace Reg.D5.S3.Fourier.HexagonalThetaMinimum
noncomputable section

def registration_margin : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hexagonal_vertical_differential_bound) (type_of% (realize heightSignature
      (fun _ y t => F t (1 / 2) y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hexagonal_vertical_differential_bound.information_unit,
  realizationName := `Reg.Support.HexagonalThetaMinimum.marginRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨marginArena⟩, objectArena := .source ⟨marginArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source marginArena ⟨marginRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => F t (1 / 2) y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaMinimum, definition := none,
    coordinates := #[4], readouts := #[{
      path := #[
        "body", "body", "body", "body", "arg", "arg",
        "arg", "fn", "arg", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false
    }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_derivative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@height_derivative_pos) (type_of% (realize heightSignature
      (fun _ y t => F t (1 / 2) y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.height_derivative_pos.information_unit,
  realizationName := `Reg.Support.HexagonalThetaMinimum.derivativeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨derivativeArena⟩, objectArena := .source ⟨derivativeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source derivativeArena ⟨derivativeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => F t (1 / 2) y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaMinimum, definition := none,
    coordinates := #[4], readouts := #[{
      path := #[
        "body", "body", "body", "body", "arg", "fn",
        "arg", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false
    }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_height : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hexagonal_height_minimum) (type_of% (realize heightSignature
      (fun _ y t => F t (1 / 2) y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hexagonal_height_minimum.information_unit,
  realizationName := `Reg.Support.HexagonalThetaMinimum.heightRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨heightArena⟩, objectArena := .source ⟨heightArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source heightArena ⟨heightRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => F t (1 / 2) y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaMinimum, definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false
    }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_reduced : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reduced_theta_minimum) (type_of% (realize thetaSignature
      (fun _ p t => F t p.1 p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.reduced_theta_minimum.information_unit,
  realizationName := `Reg.Support.HexagonalThetaMinimum.reducedRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨reducedArena⟩, objectArena := .source ⟨reducedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source reducedArena ⟨reducedRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize thetaSignature
    (fun _ p t => F t p.1 p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaMinimum, definition := none,
    coordinates := #[1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false
    }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.HexagonalThetaMinimum

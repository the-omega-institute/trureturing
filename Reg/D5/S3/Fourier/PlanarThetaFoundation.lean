import Reg.Support.PlanarThetaFoundation

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.PlanarThetaFoundation

namespace Reg.D5.S3.Fourier.PlanarThetaFoundation
noncomputable section

def registration_control : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quadratic_control) (type_of% (realize formSignature
      (fun _ p v => Q p.1 p.2 v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.quadratic_control.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.controlRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨controlArena⟩, objectArena := .source ⟨controlArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source controlArena ⟨controlRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize formSignature
    (fun _ p v => Q p.1 p.2 v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[3, 4], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg", "arg"],
      stateBinder := 9, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_summable : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable) (type_of% (realize gaussianSignature
      (fun _ p v => Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.summable.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.summableRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨summableArena⟩, objectArena := .source ⟨summableArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source summableArena ⟨summableRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize gaussianSignature
    (fun _ p v => Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_duality : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@temperature_duality) (type_of% (realize thetaSignature
      (fun _ p v => F v p.1 p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.temperature_duality.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.dualityRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨dualityArena⟩, objectArena := .source ⟨dualityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source dualityArena ⟨dualityRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize thetaSignature
    (fun _ p v => F v p.1 p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_shearDerivative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_shear) (type_of% (realize gaussianSignature
      (fun _ p v => shearDerivativeTerm p v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hasDerivAt_shear.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.shearDerivativeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨shearDerivativeArena⟩, objectArena := .source ⟨shearDerivativeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source shearDerivativeArena ⟨shearDerivativeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize gaussianSignature
    (fun _ p v => shearDerivativeTerm p v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_heightDerivative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_height) (type_of% (realize gaussianSignature
      (fun _ p v => heightDerivativeTerm p v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hasDerivAt_height.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.heightDerivativeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨heightDerivativeArena⟩, objectArena := .source ⟨heightDerivativeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source heightDerivativeArena ⟨heightDerivativeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize gaussianSignature
    (fun _ p v => heightDerivativeTerm p v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_heightSecond : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_height_deriv) (type_of% (realize gaussianSignature
      (fun _ p v => heightSecondTerm p v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hasDerivAt_height_deriv.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.heightSecondRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨heightSecondArena⟩, objectArena := .source ⟨heightSecondArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source heightSecondArena ⟨heightSecondRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize gaussianSignature
    (fun _ p v => heightSecondTerm p v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_geometry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@lattice_geometry) (type_of% (realize formSignature
      (fun _ p v => Q p.1 p.2 v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.lattice_geometry.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.geometryRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨geometryArena⟩, objectArena := .source ⟨geometryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source geometryArena ⟨geometryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize formSignature
    (fun _ p v => Q p.1 p.2 v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #[
        "body", "body", "body", "arg", "body", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }
def registration_basisGeometry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_reduction_geometry) (type_of% (realize basisFormSignature
      (fun _ p v => Complex.normSq ((v.1 : ℂ) * p.1 + (v.2 : ℂ) * p.2))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_reduction_geometry.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.basisGeometryRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨basisGeometryArena⟩, objectArena := .source ⟨basisGeometryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source basisGeometryArena ⟨basisGeometryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize basisFormSignature
    (fun _ p v => Complex.normSq ((v.1 : ℂ) * p.1 + (v.2 : ℂ) * p.2))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg",
        "arg", "arg", "arg", "arg", "arg", "body", "body", "fn", "arg"],
      stateBinder := 6, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.PlanarThetaFoundation

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaLatticeIsometry

namespace Reg.D5.S3.Fourier.ThetaLatticeIsometry
noncomputable section

def registration_isometry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_isometry_of_quadratic_reindex) (type_of% (realize pointSignature
      (fun _ p v => latticePoint p.1 p.2 v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_isometry_of_quadratic_reindex.information_unit,
  realizationName := `Reg.Support.ThetaLatticeIsometry.isometryRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨isometryArena⟩, objectArena := .source ⟨isometryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source isometryArena ⟨isometryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize pointSignature
    (fun _ p v => latticePoint p.1 p.2 v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.PlanarThetaFoundation, definition := none,
    coordinates := #[2, 3], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaLatticeIsometry

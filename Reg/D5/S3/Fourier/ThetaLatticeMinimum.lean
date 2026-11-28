import Reg.Support.ThetaLatticeMinimum

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.PlanarThetaFoundation
open Reg.Support.ThetaLatticeMinimum

namespace Reg.D5.S3.Fourier.ThetaLatticeMinimum
noncomputable section

def registration_minimum : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_theta_minimum_isometry) (type_of% (realize basisSignature
      (fun _ p t => basisTheta t p.1 p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_theta_minimum_isometry.information_unit,
  realizationName := `Reg.Support.ThetaLatticeMinimum.minimumRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨minimumArena⟩, objectArena := .source ⟨minimumArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source minimumArena ⟨minimumRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize basisSignature
    (fun _ p t => basisTheta t p.1 p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaLatticeMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaLatticeMinimum


open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.PlanarThetaFoundation
open Reg.Support.ThetaLatticeMinimum

namespace Reg.D5.S3.Fourier.ThetaLatticeMinimum
noncomputable section

def registration_normScale : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_normSq_scale) (type_of% (realize normScaleSignature
      (fun _ p v =>
        Complex.normSq ((v.1 : ℂ) * (p.1 • p.2.1) + (v.2 : ℂ) * (p.1 • p.2.2)))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_normSq_scale.information_unit,
  realizationName := `Reg.Support.ThetaLatticeMinimum.normScaleRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨normScaleArena⟩, objectArena := .source ⟨normScaleArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source normScaleArena ⟨normScaleRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize normScaleSignature
    (fun _ p v =>
        Complex.normSq ((v.1 : ℂ) * (p.1 • p.2.1) + (v.2 : ℂ) * (p.1 • p.2.2)))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaLatticeMinimum, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_thetaScale : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basisTheta_scale) (type_of% (realize thetaScaleSignature
      (fun _ p t => basisTheta t (p.1 • p.2.1) (p.1 • p.2.2)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basisTheta_scale.information_unit,
  realizationName := `Reg.Support.ThetaLatticeMinimum.thetaScaleRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨thetaScaleArena⟩, objectArena := .source ⟨thetaScaleArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source thetaScaleArena ⟨thetaScaleRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize thetaScaleSignature
    (fun _ p t => basisTheta t (p.1 • p.2.1) (p.1 • p.2.2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaLatticeMinimum, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_area : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_normalized_area) (type_of% (realize areaSignature
      (fun _ p A => |(((Real.sqrt A)⁻¹ : ℝ) • p.1).re * (((Real.sqrt A)⁻¹ : ℝ) • p.2).im -
      (((Real.sqrt A)⁻¹ : ℝ) • p.1).im * (((Real.sqrt A)⁻¹ : ℝ) • p.2).re|)
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_normalized_area.information_unit,
  realizationName := `Reg.Support.ThetaLatticeMinimum.areaRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨areaArena⟩, objectArena := .source ⟨areaArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source areaArena ⟨areaRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize areaSignature
    (fun _ p A => |(((Real.sqrt A)⁻¹ : ℝ) • p.1).re * (((Real.sqrt A)⁻¹ : ℝ) • p.2).im -
      (((Real.sqrt A)⁻¹ : ℝ) • p.1).im * (((Real.sqrt A)⁻¹ : ℝ) • p.2).re|) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaLatticeMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaLatticeMinimum

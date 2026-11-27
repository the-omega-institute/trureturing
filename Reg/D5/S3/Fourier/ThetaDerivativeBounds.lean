import Reg.Support.ThetaDerivativeBounds

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaFourierBounds

namespace Reg.D5.S3.Fourier.ThetaFourierBounds
noncomputable section

def registration_derivative : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_thetaFourier) (type_of% (realize fourierSignature
      (fun _ s b => thetaSine s b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hasDerivAt_thetaFourier.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.derivativeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨derivativeArena⟩, objectArena := .source ⟨derivativeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source derivativeArena ⟨derivativeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fourierSignature
    (fun _ s b => thetaSine s b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_firstMode : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaSine_first_mode) (type_of% (realize fourierSignature
      (fun _ s b => thetaSine s b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaSine_first_mode.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.firstModeRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨firstModeArena⟩, objectArena := .source ⟨firstModeArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source firstModeArena ⟨firstModeRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fourierSignature
    (fun _ s b => thetaSine s b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_bounds : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_derivative_bounds) (type_of% (realize fourierSignature
      (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_derivative_bounds.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.boundsRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨boundsArena⟩, objectArena := .source ⟨boundsArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source boundsArena ⟨boundsRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fourierSignature
    (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_control : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_derivative_control) (type_of% (realize fourierSignature
      (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_derivative_control.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.controlRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨controlArena⟩, objectArena := .source ⟨controlArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source controlArena ⟨controlRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fourierSignature
    (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_moment : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_moment) (type_of% (realize momentSignature
      (fun _ p k => ((k : ℝ) + 1) ^ p.2 *
        Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.gaussian_moment.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.momentRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨momentArena⟩, objectArena := .source ⟨momentArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source momentArena ⟨momentRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize momentSignature
    (fun _ p k => ((k : ℝ) + 1) ^ p.2 *
      Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0, 2], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_cosine : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cos_summable) (type_of% (realize cosineSignature
      (fun _ p k => Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2) *
        Real.cos (2 * Real.pi * ((k : ℝ) + 1) * p.2))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.cos_summable.information_unit,
  realizationName := `Reg.Support.ThetaFourierBounds.cosineRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨cosineArena⟩, objectArena := .source ⟨cosineArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source cosineArena ⟨cosineRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize cosineSignature
    (fun _ p k => Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * ((k : ℝ) + 1) * p.2)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0, 2], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaFourierBounds

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaPoisson
open Reg.Support.ThetaFourierBounds

namespace Reg.D5.S3.Fourier.ThetaPoisson
noncomputable section

def registration_value : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_poisson) (type_of% (realize valueSignature
      (fun _ b s => thetaFourier s b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_poisson.information_unit,
  realizationName := `Reg.Support.ThetaPoisson.valueRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨valueArena⟩, objectArena := .source ⟨valueArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source valueArena ⟨valueRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize valueSignature
    (fun _ b s => thetaFourier s b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[2], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_zero : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_zero_duality) (type_of% (realize zeroSignature
      (fun _ _ s => thetaFourier s 0) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_zero_duality.information_unit,
  realizationName := `Reg.Support.ThetaPoisson.zeroRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨zeroArena⟩, objectArena := .source ⟨zeroArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source zeroArena ⟨zeroRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize zeroSignature
    (fun _ _ s => thetaFourier s 0) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_translate : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_gaussianTranslate) (type_of% (realize translateSignature
      (fun _ p n => translateTerm p n) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hasDerivAt_gaussianTranslate.information_unit,
  realizationName := `Reg.Support.ThetaPoisson.translateRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨translateArena⟩, objectArena := .source ⟨translateArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source translateArena ⟨translateRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize translateSignature
    (fun _ p n => translateTerm p n) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0, 2], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "body"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_force : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_derivative_gaussian) (type_of% (realize fourierSignature
      (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_derivative_gaussian.information_unit,
  realizationName := `Reg.Support.ThetaPoisson.forceRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨forceArena⟩, objectArena := .source ⟨forceArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source forceArena ⟨forceRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize fourierSignature
    (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_integerFourier : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@real_fourier_int) (type_of% (realize valueSignature
      (fun _ b s => thetaFourier s b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.real_fourier_int.information_unit,
  realizationName := `Reg.Support.ThetaPoisson.integerFourierRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨integerFourierArena⟩, objectArena := .source ⟨integerFourierArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source integerFourierArena ⟨integerFourierRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize valueSignature
    (fun _ b s => thetaFourier s b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[2], readouts := #[{
      path := #["body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaPoisson

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaDerivativeBounds

namespace Reg.D5.S3.Fourier.ThetaDerivativeBounds
noncomputable section

def registration_small : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@thetaFourier_small_derivative_bounds) (type_of% (realize derivativeSignature
      (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.thetaFourier_small_derivative_bounds.information_unit,
  realizationName := `Reg.Support.ThetaDerivativeBounds.smallRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨smallArena⟩, objectArena := .source ⟨smallArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source smallArena ⟨smallRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize derivativeSignature
    (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaDerivativeBounds, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaDerivativeBounds

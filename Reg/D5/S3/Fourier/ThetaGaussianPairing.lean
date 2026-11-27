import Reg.Support.ThetaGaussianPairing

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaGaussianTail

namespace Reg.D5.S3.Fourier.ThetaGaussianTail
noncomputable section

def registration_bound : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_tail_bound) (type_of% (realize tailSignature
      (fun _ _ v => gaussianTail v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.gaussian_tail_bound.information_unit,
  realizationName := `Reg.Support.ThetaGaussianTail.boundRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨boundArena⟩, objectArena := .source ⟨boundArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source boundArena ⟨boundRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tailSignature
    (fun _ _ v => gaussianTail v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaGaussianPairing, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg", "fn", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_scaled : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_tail_scaled_bound) (type_of% (realize tailSignature
      (fun _ _ v => gaussianTail v) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.gaussian_tail_scaled_bound.information_unit,
  realizationName := `Reg.Support.ThetaGaussianTail.scaledRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨scaledArena⟩, objectArena := .source ⟨scaledArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source scaledArena ⟨scaledRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tailSignature
    (fun _ _ v => gaussianTail v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaGaussianPairing, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_pair : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_pair_tail_bound) (type_of% (realize tailSignature
      (fun _ _ a => gaussianPairTail a) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.gaussian_pair_tail_bound.information_unit,
  realizationName := `Reg.Support.ThetaGaussianTail.pairRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨pairArena⟩, objectArena := .source ⟨pairArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source pairArena ⟨pairRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tailSignature
    (fun _ _ a => gaussianPairTail a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaGaussianPairing, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaGaussianTail

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaGaussianPairing

namespace Reg.D5.S3.Fourier.ThetaGaussianPairing
noncomputable section

def registration_moment : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@summable_gaussian_force) (type_of% (realize momentSignature
      (fun _ p m => (p.2 - m) * Real.exp (-p.1 * (p.2 - m) ^ 2))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.summable_gaussian_force.information_unit,
  realizationName := `Reg.Support.ThetaGaussianPairing.momentRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨momentArena⟩, objectArena := .source ⟨momentArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source momentArena ⟨momentRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize momentSignature
    (fun _ p m => (p.2 - m) * Real.exp (-p.1 * (p.2 - m) ^ 2))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaGaussianPairing, definition := none,
    coordinates := #[0, 2], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_lower : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_force_lower) (type_of% (realize forceSignature
      (fun _ a b => gaussianForce a b) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.gaussian_force_lower.information_unit,
  realizationName := `Reg.Support.ThetaGaussianPairing.lowerRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨lowerArena⟩, objectArena := .source ⟨lowerArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source lowerArena ⟨lowerRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize forceSignature
    (fun _ a b => gaussianForce a b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaGaussianPairing, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"],
      stateBinder := 1, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaGaussianPairing

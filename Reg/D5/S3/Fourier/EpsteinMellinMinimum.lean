import Reg.Support.EpsteinMellinMinimum

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.EpsteinMellinMinimum

namespace Reg.D5.S3.Fourier.EpsteinMellinMinimum
noncomputable section

def registration_summable : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@epstein_summable) (type_of% (realize termSignature
      (fun _ p v => (Q p.2.1 p.2.2 v) ^ (-p.1)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.epstein_summable.information_unit,
  realizationName := `Reg.Support.EpsteinMellinMinimum.summableRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨summableArena⟩, objectArena := .source ⟨summableArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source summableArena ⟨summableRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize termSignature
    (fun _ p v => (Q p.2.1 p.2.2 v) ^ (-p.1)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_integrable : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@epstein_mellin_integrable) (type_of% (realize mellinSignature
      (fun _ p t => (F t p.2.1 p.2.2 - 1) * t ^ (p.1 - 1)) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.epstein_mellin_integrable.information_unit,
  realizationName := `Reg.Support.EpsteinMellinMinimum.integrableRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨integrableArena⟩, objectArena := .source ⟨integrableArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source integrableArena ⟨integrableRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize mellinSignature
    (fun _ p t => (F t p.2.1 p.2.2 - 1) * t ^ (p.1 - 1)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn", "arg", "body"],
      stateBinder := 5, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_formula : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@epstein_mellin) (type_of% (realize zetaSignature
      (fun _ p y => epstein p.1 p.2 y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.epstein_mellin.information_unit,
  realizationName := `Reg.Support.EpsteinMellinMinimum.formulaRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨formulaArena⟩, objectArena := .source ⟨formulaArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source formulaArena ⟨formulaRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize zetaSignature
    (fun _ p y => epstein p.1 p.2 y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_minimum : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reduced_epstein_minimum) (type_of% (realize zetaSignature
      (fun _ p y => epstein p.1 p.2 y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.reduced_epstein_minimum.information_unit,
  realizationName := `Reg.Support.EpsteinMellinMinimum.minimumRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨minimumArena⟩, objectArena := .source ⟨minimumArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source minimumArena ⟨minimumRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize zetaSignature
    (fun _ p y => epstein p.1 p.2 y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_basisMinimum : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@basis_epstein_minimum_isometry) (type_of% (realize basisZetaSignature
      (fun _ p s => basisEpstein s p.1 p.2)
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.basis_epstein_minimum_isometry.information_unit,
  realizationName := `Reg.Support.EpsteinMellinMinimum.basisMinimumRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨basisMinimumArena⟩, objectArena := .source ⟨basisMinimumArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source basisMinimumArena ⟨basisMinimumRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize basisZetaSignature
    (fun _ p s => basisEpstein s p.1 p.2)
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"],
      stateBinder := 3, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.EpsteinMellinMinimum

open Reg.Support.PlanarThetaFoundation
namespace Reg.D5.S3.Fourier.PlanarThetaFoundation
noncomputable section

def registration_temperatureContinuity : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuousOn_temperature) (type_of% (realize thetaSignature
      (fun _ p v => F v p.1 p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.continuousOn_temperature.information_unit,
  realizationName := `Reg.Support.PlanarThetaFoundation.temperatureContinuityRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨temperatureContinuityArena⟩,
  objectArena := .source ⟨temperatureContinuityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source temperatureContinuityArena ⟨temperatureContinuityRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize thetaSignature
    (fun _ p v => F v p.1 p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.EpsteinMellinMinimum, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := true,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.PlanarThetaFoundation

import Reg.Support.HexagonalTheta.Stability

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.HexagonalThetaStability
open Reg.Support.PlanarThetaFoundation

namespace Reg.D5.S3.Fourier.HexagonalThetaStability
noncomputable section

def registration_orbit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@orbitGap_lower) (type_of% (realize orbitSignature
      (fun _ h a => orbitGap h a)
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.orbitGap_lower.__information_unit,
  realizationName := `Reg.Support.HexagonalThetaStability.orbitRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨orbitArena⟩, objectArena := .source ⟨orbitArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source orbitArena ⟨orbitRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize orbitSignature
    (fun _ h a => orbitGap h a) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaStability, definition := none,
    coordinates := #[0], readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "body", "arg"],
      stateBinder := 2, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

def registration_stability : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hexagonal_theta_stability) (type_of% (realize thetaSignature
      (fun _ p t => F t p.1 p.2) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hexagonal_theta_stability.__information_unit,
  realizationName := `Reg.Support.HexagonalThetaStability.stabilityRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨stabilityArena⟩, objectArena := .source ⟨stabilityArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source stabilityArena ⟨stabilityRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize thetaSignature
    (fun _ p t => F t p.1 p.2) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.HexagonalThetaStability, definition := none,
    coordinates := #[1, 2], readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.HexagonalThetaStability

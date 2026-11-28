import Reg.Support.HexagonalTheta.Stability
import Reg.Support.ThetaVerticalPositive

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.ThetaVerticalPositive

namespace Reg.D5.S3.Fourier.ThetaVerticalPositive
noncomputable section

def registration_stationary : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hexagonal_height_stationary) (type_of% (realize heightSignature
      (fun _ y t => F t (1 / 2) y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hexagonal_height_stationary.information_unit,
  realizationName := `Reg.Support.ThetaVerticalPositive.stationaryRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨stationaryArena⟩, objectArena := .source ⟨stationaryArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source stationaryArena ⟨stationaryRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => F t (1 / 2) y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaVerticalPositive, definition := none,
    coordinates := #[2], readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }


def registration_positive : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@verticalPositive_lower) (type_of% (realize heightSignature
      (fun _ y t => verticalPositive t y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.verticalPositive_lower.information_unit,
  realizationName := `Reg.Support.ThetaVerticalPositive.positiveRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨positiveArena⟩, objectArena := .source ⟨positiveArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source positiveArena ⟨positiveRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => verticalPositive t y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaVerticalPositive, definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body", "body", "body", "body", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }


def registration_differential : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@vertical_differential_identity) (type_of% (realize heightSignature
      (fun _ y t => verticalPositive t y) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.vertical_differential_identity.information_unit,
  realizationName := `Reg.Support.ThetaVerticalPositive.differentialRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨differentialArena⟩, objectArena := .source ⟨differentialArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source differentialArena ⟨differentialRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize heightSignature
    (fun _ y t => verticalPositive t y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaVerticalPositive, definition := none,
    coordinates := #[1], readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaVerticalPositive

open Reg.Support.ThetaVerticalTail
namespace Reg.D5.S3.Fourier.ThetaVerticalTail
noncomputable section

def registration_weighted : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_gaussian_summable) (type_of% (realize weightedSignature
      (fun _ p v => (v.2 : ℝ) ^ 2 * Real.exp (-Real.pi * p.1 * Q (1 / 2) p.2 v))
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.weighted_gaussian_summable.information_unit,
  realizationName := `Reg.Support.ThetaVerticalTail.weightedRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨weightedArena⟩, objectArena := .source ⟨weightedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source weightedArena ⟨weightedRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize weightedSignature
    (fun _ p v => (v.2 : ℝ) ^ 2 * Real.exp (-Real.pi * p.1 * Q (1 / 2) p.2 v))
    (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaVerticalPositive, definition := none,
    coordinates := #[0, 1], readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body"],
      stateBinder := 4, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaVerticalTail

open Reg.Support.HexagonalThetaStability
namespace Reg.D5.S3.Fourier.ThetaVerticalPositive
noncomputable section

def registration_hex_turn : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hex_q_turn) (type_of% (realize hexFormSignature
      (fun _ _ v => Q (1 / 2) (Real.sqrt 3 / 2) v)
      (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Fourier.PlanarTheta.hex_q_turn.__information_unit,
  realizationName := `Reg.Support.HexagonalThetaStability.turnRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨turnArena⟩, objectArena := .source ⟨turnArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source turnArena ⟨turnRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize hexFormSignature
    (fun _ _ v => Q (1 / 2) (Real.sqrt 3 / 2) v) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Fourier.ThetaVerticalPositive, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "arg"], stateBinder := 0, functionOperand := false,
      stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Fourier.ThetaVerticalPositive

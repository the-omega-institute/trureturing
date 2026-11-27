import Reg.Support.DiagonalPadeWindow

open D5.S3.Analytic.Polynomial.DiagonalPadeWindow
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.DiagonalPadeWindow

namespace Reg.D5.S3.Analytic.Polynomial.DiagonalPadeWindow
noncomputable section

def registration_poisson : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gaussian_poisson) (type_of% (realize poissonSignature
      (fun _ _ z => Complex.exp z) (fun e => nomatch e))) Type Unit := {
  unitName := `D5.S3.Analytic.Polynomial.DiagonalPadeWindow.gaussian_poisson.information_unit,
  realizationName := `Reg.Support.DiagonalPadeWindow.poissonRegistration,
  realizationSource := none, generated := false,
  arena := .source ⟨poissonArena⟩, objectArena := .source ⟨poissonArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source poissonArena ⟨poissonRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize poissonSignature
    (fun _ _ z => Complex.exp z) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Analytic.Polynomial.DiagonalPadeWindow, definition := none,
    coordinates := #[], readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg", "body"],
      stateBinder := 0, functionOperand := false,
      stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

end
end Reg.D5.S3.Analytic.Polynomial.DiagonalPadeWindow

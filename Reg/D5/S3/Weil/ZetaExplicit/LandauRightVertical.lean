import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Weil.ZetaExplicit.LandauRightVertical

/-! Source-bound logarithm observation in the uniform right-edge estimate. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.LandauRightVertical

open Complex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaExplicit.LandauRightVertical
open _root_.Reg.Support
open LeanInformationAudit

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ => Real.log) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {x V : ℝ}, 1 < x → 1 < V →
    let c := 1 + (Real.log (3 * x))⁻¹
    ‖∫ t in 1..V, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) *
      (- deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) / riemannZeta ((c : ℂ) + (t : ℂ) * I))‖ ≤
        let logHeight := observation.readout () ()
        400 * (V * logHeight (2 * x) + x * (logHeight (2 * x))^2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have invalid := law (x := 2) (V := 3) (by norm_num) (by norm_num)
  dsimp [rejected, realize] at invalid
  have impossible : (0 : ℝ) ≤ 400 * (3 * (-1) + 2 * (-1)^2) := (norm_nonneg _).trans invalid
  norm_num at impossible

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (x := 2) (by norm_num)).ne

def evidence : Registration arena (type_of% @norm_right_vertical_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_right_vertical_integral, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@norm_right_vertical_integral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaExplicit.LandauRightVertical.norm_right_vertical_integral.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.LandauRightVertical.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => Real.log) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.LandauRightVertical
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.ZetaExplicit.LandauRightVertical

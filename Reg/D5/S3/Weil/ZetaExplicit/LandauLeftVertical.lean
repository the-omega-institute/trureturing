import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Weil.ZetaExplicit.LandauLeftVertical

/-! Source-bound base frequency in the oscillatory left-edge estimate. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.LandauLeftVertical

open Complex
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaExplicit.LandauLeftVertical
open _root_.Reg.Support
open LeanInformationAudit

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ => Real.log) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {x V : ℝ}, 1 < x → 1 ≤ V →
    ‖∫ t in 1..V, (x : ℂ) ^ ((-1 / 4 : ℂ) + t * I) *
      (-logDeriv riemannZeta ((-1 / 4 : ℂ) + t * I))‖ ≤
      let logBase := observation.readout () ()
      x ^ (-1 / 4 : ℝ) * (80 * (V - 1) + 20 * (1 + Real.log V) / logBase x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have invalid := law (x := 2) (V := 1) (by norm_num) (by norm_num)
  have hpow : 0 < (2 : ℝ) ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h := (norm_nonneg _).trans invalid
  dsimp [rejected, realize] at h
  rw [Real.log_one] at h
  norm_num at h
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 1, 2, ?_⟩
  change Real.log 1 ≠ Real.log 2
  rw [Real.log_one]
  exact (Real.log_pos (x := 2) (by norm_num)).ne

def evidence : Registration arena (type_of% @norm_left_vertical_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_left_vertical_integral, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@norm_left_vertical_integral) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaExplicit.LandauLeftVertical.norm_left_vertical_integral.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.LandauLeftVertical.evidence
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
    owner := `D5.S3.Weil.ZetaExplicit.LandauLeftVertical
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Weil.ZetaExplicit.LandauLeftVertical

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the norm of the centered remainder. -/

noncomputable section

namespace Reg.D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Zeta23.WeilEF
open LeanInformationAudit Metric

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ w => ‖w‖ + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {f : ℂ → ℂ} {B : ℝ}
    (_hfa : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1)) (_hf0 : f 0 = 1)
    (_hB2 : 2 ≤ B) (_hfB : ∀ w : ℂ, ‖w‖ ≤ 24 / 25 → ‖f w‖ ≤ B),
    ∃ Z : Finset ℂ, (↑Z : Set ℂ) = SetOfZeros (22 / 25) f ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 / 4 → f z ≠ 0 →
        R.readout () () ((logDeriv f z - logDeriv f 0) -
          ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) -
            ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (0 - ρ))) ≤
          179180000 * ‖z‖ * Real.log B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hB : ∀ w : ℂ, ‖w‖ ≤ 24 / 25 → ‖(1 : ℂ)‖ ≤ (2 : ℝ) := by
    intro _ _
    norm_num
  obtain ⟨_, _, hbound⟩ :=
    h (f := fun _ => (1 : ℂ)) (B := 2) analyticOnNhd_const rfl (by norm_num) hB
  have hzero := hbound 0 (by norm_num) one_ne_zero
  norm_num [rejected, realize] at hzero

def family : Registration arena (type_of% (@logDeriv_partial_fraction_unit_centered)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨logDeriv_partial_fraction_unit_centered, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    rw [norm_zero, norm_one]
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@logDeriv_partial_fraction_unit_centered) (Realization signature) Unit Unit where
  unitName := `Zeta23.WeilEF.logDeriv_partial_fraction_unit_centered.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaExplicit.CenteredDiskLogDeriv

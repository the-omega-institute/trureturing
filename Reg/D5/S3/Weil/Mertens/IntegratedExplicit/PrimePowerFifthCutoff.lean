import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
import Reg.Support.SingleDependentReadout

/-! Source readouts of the full-cutoff Chebyshev prime-power sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => psi t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ t =>
    theta t + psi (t ^ (1 / 2 : ℝ)) + psi (t ^ (1 / 3 : ℝ)) +
      psi (t ^ (1 / 5 : ℝ)) + (t + 100)) (fun e => nomatch e)

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change psi 1 ≠ psi 2
  rw [psi_one]
  exact (fun h => (not_lt_of_ge (le_refl (2 : ℝ))) (psi_eq_zero_iff.mp h.symm))

abbrev correctedArena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t →
    |V.readout () () t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) + theta (t ^ (1 / 6 : ℝ))| ≤
      4 * log t * t ^ (1 / 7 : ℝ)

private theorem corrected_rejected : ¬ correctedArena.Law rejected := by
  intro h
  have hbad := h (t := 2) (by norm_num)
  dsimp [rejected, realize] at hbad
  have hlarge : (102 : ℝ) ≤ |(2 + 100 : ℝ) + theta (2 ^ (1 / 6 : ℝ))| :=
    (by linarith [theta_nonneg ((2 : ℝ) ^ (1 / 6 : ℝ))] :
      (102 : ℝ) ≤ 2 + 100 + theta (2 ^ (1 / 6 : ℝ))).trans (le_abs_self _)
  have hbound : 4 * log 2 * (2 : ℝ) ^ (1 / 7 : ℝ) ≤ 8 := by
    have hlog : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (x := 2) (by norm_num)]
    have hpow : (2 : ℝ) ^ (1 / 7 : ℝ) ≤ 2 := rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc
      _ ≤ (4 : ℝ) * 1 * 2 := by gcongr
      _ = _ := by norm_num
  have hcancel :
      theta (2 : ℝ) + psi (2 ^ (1 / 2 : ℝ)) + psi (2 ^ (1 / 3 : ℝ)) +
        psi (2 ^ (1 / 5 : ℝ)) + (2 + 100) - theta 2 - psi (2 ^ (1 / 2 : ℝ)) -
        psi (2 ^ (1 / 3 : ℝ)) - psi (2 ^ (1 / 5 : ℝ)) + theta (2 ^ (1 / 6 : ℝ)) =
        2 + 100 + theta (2 ^ (1 / 6 : ℝ)) := by ring
  rw [hcancel] at hbad
  linarith [hlarge.trans (hbad.trans hbound)]

def correctedFamily : Registration correctedArena
    (type_of% @abs_psi_sub_roots_add_theta_sixth_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_psi_sub_roots_add_theta_sixth_le, rejected, corrected_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    correctedArena.Law actual rejected corrected_rejected
  dependence := actual_depends

abbrev uniformArena : Arena where
  signature := signature
  Law V := ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
    |V.readout () () t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ))| ≤ C * t ^ (1 / 6 : ℝ)

private theorem uniform_rejected : ¬ uniformArena.Law rejected := by
  rintro ⟨C, hC, h⟩
  let t : ℝ := (C + 2) ^ 2
  have ht : 2 ≤ t := by dsimp [t]; nlinarith
  have ht1 : 1 ≤ t := by linarith
  have hsqrt : Real.sqrt t = C + 2 := Real.sqrt_sq (by linarith)
  have hpow : t ^ (1 / 6 : ℝ) ≤ C + 2 := by
    rw [← hsqrt, Real.sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hbad := h t ht
  dsimp [rejected, realize] at hbad
  have hcancel :
      theta t + psi (t ^ (1 / 2 : ℝ)) + psi (t ^ (1 / 3 : ℝ)) +
        psi (t ^ (1 / 5 : ℝ)) + (t + 100) - theta t - psi (t ^ (1 / 2 : ℝ)) -
        psi (t ^ (1 / 3 : ℝ)) - psi (t ^ (1 / 5 : ℝ)) = t + 100 := by ring
  rw [hcancel, abs_of_nonneg (by linarith : 0 ≤ t + 100)] at hbad
  have hle := hbad.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  dsimp [t] at hle
  nlinarith

def uniformFamily : Registration uniformArena (type_of% @exists_abs_psi_sub_roots_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_abs_psi_sub_roots_le, rejected, uniform_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    uniformArena.Law actual rejected uniform_rejected
  dependence := actual_depends

def correctedRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_psi_sub_roots_add_theta_sixth_le) (Realization signature) Unit Unit where
  unitName := .str ``abs_psi_sub_roots_add_theta_sixth_le "__information_unit"
  realizationName := ``correctedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨correctedArena⟩
  objectArena := .source ⟨correctedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source correctedArena ⟨correctedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def uniformRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_abs_psi_sub_roots_le) (Realization signature) Unit Unit where
  unitName := .str ``exists_abs_psi_sub_roots_le "__information_unit"
  realizationName := ``uniformFamily
  realizationSource := none
  generated := false
  arena := .source ⟨uniformArena⟩
  objectArena := .source ⟨uniformArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source uniformArena ⟨uniformFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "fn", "arg", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev sumArena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t → ∀ {N : ℕ},
    ⌊log t / log 2⌋₊ ≤ N →
    V.readout () () t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) =
      ∑ k ∈ Finset.Icc 6 N, coefficient k * theta (t ^ (1 / (k : ℝ)))

private theorem sum_rejected : ¬ sumArena.Law rejected := by
  intro h
  have hN : ⌊log (2 : ℝ) / log 2⌋₊ ≤ 6 := by
    rw [div_self (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    norm_num
  have hbad := h (t := 2) (by norm_num) (N := 6) hN
  have hgood := psi_sub_roots_eq_sum (by norm_num : (2 : ℝ) ≤ 2) hN
  have hpsi : psi 2 = theta 2 := by
    have hb : ⌊log (2 : ℝ) / log 2⌋₊ ≤ 1 := by
      rw [div_self (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      norm_num
    simpa using psi_eq_theta_add_sum_theta' (by norm_num : (2 : ℝ) ≤ 2) hb
  have hz (d : ℝ) (hd : 0 < d) (hd' : d < 1) : psi ((2 : ℝ) ^ d) = 0 := by
    apply psi_eq_zero_iff.mpr
    simpa using rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hd'
  dsimp [rejected, realize] at hbad
  rw [hpsi, hz _ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num),
    hz _ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num),
    hz _ (by norm_num : (0 : ℝ) < 1 / 5) (by norm_num)] at hgood
  linarith only [hbad, hgood]

def sumFamily : Registration sumArena (type_of% @psi_sub_roots_eq_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@psi_sub_roots_eq_sum, rejected, sum_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sumArena.Law actual rejected sum_rejected
  dependence := correctedFamily.dependence

def sumRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psi_sub_roots_eq_sum) (Realization signature) Unit Unit where
  unitName := .str ``psi_sub_roots_eq_sum "__information_unit"
  realizationName := ``sumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
import Reg.Support.SingleDependentReadout

/-! Observational dependence and a rejected intervention for the Chebyshev root sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real
open LeanInformationAudit
open scoped ArithmeticFunction.Moebius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => theta t) (fun e => nomatch e)

def altered : Realization signature :=
  realize signature (fun _ _ t =>
    psi t + (∑ d ∈ Finset.Icc 2 2, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))) + 1000)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t → ∀ {m : ℕ}, 2 ≤ m →
    |V.readout () () t - psi t -
      ∑ d ∈ Finset.Icc 2 m, (μ d : ℝ) * psi (t ^ (1 / (d : ℝ)))| ≤
      (log 4 + 4) * 2 * (1 + (m + 1 : ℝ) / log 2) * t ^ (1 / (m + 1 : ℝ))

private theorem actual_depends : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 1, 2, ?_⟩
  change theta 1 ≠ theta 2
  rw [theta_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
  exact ne_of_lt (theta_pos le_rfl)

private theorem alteration_rejected : ¬ arena.Law altered := by
  intro h
  have hp : (2 : ℝ) ^ (1 / ((2 : ℝ) + 1)) ≤ 2 :=
    rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hlog : (1 / 2 : ℝ) ≤ log 2 := by
    linarith [log_two_gt_d9]
  have hlog₄ : log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow, Nat.cast_ofNat]
    linarith [log_le_sub_one_of_pos (x := 2) (by norm_num)]
  have hdiv : (3 : ℝ) / log 2 ≤ 6 := by
    apply (div_le_iff₀ (by linarith : 0 < log 2)).mpr
    linarith
  have hbad := h (t := 2) (by norm_num) (m := 2) (by norm_num)
  dsimp [altered, realize] at hbad
  have hc (a b : ℝ) : a + b + 1000 - a - b = 1000 := by ring
  rw [hc, abs_of_pos (by norm_num : (0 : ℝ) < 1000)] at hbad
  have hmax :
      (log 4 + 4) * 2 * (1 + (2 + 1 : ℝ) / log 2) * (2 : ℝ) ^ (1 / (2 + 1 : ℝ)) ≤
        (6 : ℝ) * 2 * 7 * 2 := by
    gcongr <;> linarith only [hlog₄, hdiv]
  norm_num at hmax hbad
  linarith

def family : Registration arena (type_of% @chebyshev_mobius_truncation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@chebyshev_mobius_truncation, altered, alteration_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual altered alteration_rejected
  dependence := actual_depends

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chebyshev_mobius_truncation) (Realization signature) Unit Unit where
  unitName := .str ``chebyshev_mobius_truncation "__information_unit"
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => theta t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg",
        "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

open MeasureTheory Set
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)

def tailActual : Realization signature :=
  realize signature (fun _ _ x => Q x) (fun e => nomatch e)

private def roots (m : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 m, (μ n : ℝ) * (∫ t in Ioi x, psi (t ^ (1 / (n : ℝ))) / t ^ 2)

def tailAltered : Realization signature :=
  realize signature (fun _ _ x => primeTail x - roots 2 x + 1000) (fun e => nomatch e)

abbrev tailArena : Arena where
  signature := signature
  Law V := ∀ {m : ℕ}, 2 ≤ m → ∀ {x : ℝ}, 2 ≤ x →
    |Real.sqrt x * (primeTail x - V.readout () () x - roots m x)| ≤
      ((Real.log 4 + 4) * 2 * (1 + (m + 1 : ℝ) / Real.log 2)) /
        (1 - 1 / (m + 1 : ℝ)) * x ^ (1 / (m + 1 : ℝ) - 1 / 2)

private theorem tail_actual_dependence : ObservationalDependence signature tailActual := by
  intro i
  cases i
  refine ⟨(), 1, 3 / 2, ?_⟩
  change Q 1 ≠ Q (3 / 2)
  have hi := intervalIntegral.integral_Ioi_sub_Ioi chebyshev_error_kernel_integrable
    (show (1 : ℝ) ≤ 3 / 2 by norm_num)
  change Q 1 - Q (3 / 2) =
    (∫ t in (1 : ℝ)..(3 / 2), (psi t - t) / t ^ 2) at hi
  have he : (∫ t in (1 : ℝ)..(3 / 2), (psi t - t) / t ^ 2) =
      ∫ t in (1 : ℝ)..(3 / 2), -(t⁻¹) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have htwo : t < 2 := lt_of_le_of_lt ht.2 (by norm_num)
    have ht₀ : 0 < t := zero_lt_one.trans_le ht.1
    change (psi t - t) / t ^ 2 = -(t⁻¹)
    rw [psi_eq_zero_of_lt_two htwo]
    field_simp [ht₀.ne']
    ring
  rw [he, intervalIntegral.integral_neg, integral_inv_of_pos (by norm_num) (by norm_num)] at hi
  have hl := Real.log_pos (show (1 : ℝ) < (3 / 2) / 1 by norm_num)
  exact ne_of_lt (by linarith)

private theorem tail_altered_rejects : ¬ tailArena.Law tailAltered := by
  intro h
  have hbad := h (m := 2) (by decide) (x := 2) (by norm_num)
  change |Real.sqrt 2 * (primeTail 2 - (primeTail 2 - roots 2 2 + 1000) - roots 2 2)| ≤
    ((Real.log 4 + 4) * 2 * (1 + (2 + 1 : ℝ) / Real.log 2)) /
      (1 - 1 / (2 + 1 : ℝ)) * (2 : ℝ) ^ (1 / (2 + 1 : ℝ) - 1 / 2) at hbad
  rw [show primeTail 2 - (primeTail 2 - roots 2 2 + 1000) - roots 2 2 = -1000 by ring,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1000)]
    at hbad
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog₄ : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (x := 2) (by norm_num)]
  have hdiv : (3 : ℝ) / Real.log 2 ≤ 6 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    linarith
  have hpow : (2 : ℝ) ^ (1 / (2 + 1 : ℝ) - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hmax :
      ((Real.log 4 + 4) * 2 * (1 + (2 + 1 : ℝ) / Real.log 2)) /
        (1 - 1 / (2 + 1 : ℝ)) * (2 : ℝ) ^ (1 / (2 + 1 : ℝ) - 1 / 2) ≤
        ((6 : ℝ) * 2 * 7) / (1 - 1 / (2 + 1 : ℝ)) * 1 := by
    gcongr <;> linarith only [hlog₄, hdiv]
  have hfloor : 1 ≤ Real.sqrt 2 := by
    simp
  have hle := hbad.trans hmax
  norm_num at hle
  linarith

def tailFamily : Registration tailArena (type_of% @integrated_mobius_truncation) where
  actual := tailActual
  bridge := Iff.rfl
  variation := ⟨@integrated_mobius_truncation, tailAltered, tail_altered_rejects⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    tailArena.Law tailActual tailAltered tail_altered_rejects
  dependence := tail_actual_dependence

def tailRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integrated_mobius_truncation) (Realization signature) Unit Unit where
  unitName := .str ``integrated_mobius_truncation "__information_unit"
  realizationName := ``tailFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tailArena⟩
  objectArena := .source ⟨tailArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tailArena ⟨tailFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Q x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg", "arg",
        "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.MobiusCutoff

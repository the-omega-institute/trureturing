/- GID: D5/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/FinitePowerExtrapolationRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable scalar powers have finite-horizon minimax risk of order min one eta H over T. -/

import D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk

open D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk (Data Compatible)
open scoped ENNReal

/-- Every deterministic scalar prediction rule is allowed. -/
abbrev Estimator (T : ℕ) := Data T → ℝ

/-- Worst-case prediction error at the single specified horizon, including infinite losses. -/
def risk (T H : ℕ) (η : ℝ) (Ψ : Estimator T) : ℝ≥0∞ :=
  ⨆ a : Set.Ioo (0 : ℝ) 1, ⨆ y : Data T, ⨆ (_ : Compatible T η a.val y),
    ENNReal.ofReal |Ψ y - a.val ^ H|

/-- The infimum ranges over all scalar estimators, without a boundedness restriction. -/
def minimaxRisk (T H : ℕ) (η : ℝ) : ℝ≥0∞ := ⨅ Ψ : Estimator T, risk T H η Ψ

/-- Clamp the last observation to the unit interval and extrapolate its power. -/
def endpointEstimator (T H : ℕ) : Estimator T :=
  fun y => (max 0 (min 1 (y ⟨T, Nat.lt_succ_self T⟩))) ^ ((H : ℝ) / T)

/-- Uniform two-sided bounds and absolute comparison constants for finite extrapolation
of strictly stable scalar responses under pointwise bounded observation error. -/
theorem finite_power_extrapolation_risk (T H : ℕ) (hT : 1 ≤ T) (hTH : T ≤ H)
    (η : ℝ) (hη : 0 < η) :
    (ENNReal.ofReal (min (η * H / (2 * T)) (1 / 16)) ≤ minimaxRisk T H η ∧
      minimaxRisk T H η ≤ ENNReal.ofReal (min (1 / 2) (η * H / T))) ∧
    (ENNReal.ofReal ((1 / 16) * min 1 (η * H / T)) ≤ minimaxRisk T H η ∧
      minimaxRisk T H η ≤ ENNReal.ofReal (min 1 (η * H / T))) := by
  classical
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast (hT.trans hTH)
  have hTHr : (T : ℝ) ≤ H := by exact_mod_cast hTH
  have lower : ENNReal.ofReal (min (η * H / (2 * T)) (1 / 16)) ≤
      minimaxRisk T H η := by
    let d : ℝ := min (2 * η / T) (1 / (4 * H))
    have hd : 0 < d := lt_min (div_pos (by positivity) hTr) (by positivity)
    have hdT : d * T ≤ 2 * η := (le_div_iff₀ hTr).mp (min_le_left _ _)
    have hdH : d * (4 * H) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * H)).mp (min_le_right _ _)
    have hdquarter : d ≤ 1 / 4 := by nlinarith
    let a : ℝ := 1 - d
    let b : ℝ := 1 - 2 * d
    have ha : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨by dsimp [a]; linarith, by dsimp [a]; linarith⟩
    have hb : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
    have hba : b ≤ a := by dsimp [a, b]; linarith
    have hab : a - b = d := by dsimp [a, b]; ring
    let y : Data T := fun k => (a ^ k.val + b ^ k.val) / 2
    have common : Compatible T η a y ∧ Compatible T η b y := by
      have close (k : Fin (T + 1)) : |a ^ k.val - b ^ k.val| ≤ 2 * η := by
        have hpow := abs_pow_sub_pow_le (a := a) (b := b) (n := k.val)
        have hmax : max |a| |b| ≤ 1 := max_le (by simpa [abs_of_pos ha.1] using ha.2.le)
          (by simpa [abs_of_pos hb.1] using hb.2.le)
        have hmax0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
        have hm := pow_le_one₀ hmax0 hmax (n := k.val - 1)
        have hk : (k.val : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt_succ k.isLt)
        rw [hab, abs_of_pos hd] at hpow
        calc
          |a ^ k.val - b ^ k.val| ≤ d * k.val * max |a| |b| ^ (k.val - 1) := hpow
          _ ≤ d * k.val := by nlinarith [mul_nonneg hd.le (Nat.cast_nonneg k.val)]
          _ ≤ 2 * η := (mul_le_mul_of_nonneg_left hk hd.le).trans hdT
      constructor <;> intro k
      · have hc := abs_le.mp (close k)
        apply abs_le.mpr
        dsimp [y]
        constructor <;> linarith
      · have hc := abs_le.mp (close k)
        apply abs_le.mpr
        dsimp [y]
        constructor <;> linarith
    have separation : H * d / 2 ≤ a ^ H - b ^ H := by
      have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith [hb.1]) (H - 1)
      have hHm : ((H - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast (Nat.sub_le H 1)
      have hhalf : (1 / 2 : ℝ) ≤ b ^ (H - 1) := by
        dsimp [b] at hbern
        nlinarith [mul_le_mul_of_nonneg_right hHm hd.le]
      have hs := (convex_Icc b a).mul_sub_le_image_sub_of_le_deriv
        (f := fun x : ℝ => x ^ H) (C := (H : ℝ) / 2)
        (continuous_pow H).continuousOn ((differentiable_id.pow H).differentiableOn) ?_
        b ⟨le_rfl, hba⟩ a ⟨hba, le_rfl⟩ hba
      · rw [hab] at hs
        nlinarith
      · intro x hx
        have hx' : x ∈ Set.Icc b a := interior_subset hx
        rw [deriv_pow_field]
        have hp := pow_le_pow_left₀ hb.1.le hx'.1 (H - 1)
        nlinarith
    have bound_id : H * d / 4 = min (η * H / (2 * T)) (1 / 16) := by
      dsimp [d]
      rw [mul_min_of_nonneg _ _ hHr.le, ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1 <;> field_simp [hTr.ne', hHr.ne'] <;> ring
    refine le_iInf fun Ψ => ?_
    by_contra hn
    obtain ⟨r, hr0, hrisk, hrbound⟩ :=
      ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have hb0 : 0 < min (η * H / (2 * T)) (1 / 16) := by positivity
    have hr : r < min (η * H / (2 * T)) (1 / 16) :=
      (ENNReal.ofReal_lt_ofReal_iff hb0).mp hrbound
    have err (c : Set.Ioo (0 : ℝ) 1) (hc : Compatible T η c.val y) :
        |Ψ y - c.val ^ H| ≤ r := by
      apply (ENNReal.ofReal_le_ofReal_iff hr0).mp
      have hle : ENNReal.ofReal |Ψ y - c.val ^ H| ≤ risk T H η Ψ :=
        le_iSup_of_le c (le_iSup_of_le y (le_iSup_of_le hc le_rfl))
      exact hle.trans hrisk.le
    have hea := err ⟨a, ha⟩ common.1
    have heb := err ⟨b, hb⟩ common.2
    have htriangle := abs_sub_le (a ^ H) (Ψ y) (b ^ H)
    rw [abs_sub_comm (a ^ H) (Ψ y)] at htriangle
    have hh := le_abs_self (a ^ H - b ^ H)
    rw [← bound_id] at hr
    linarith
  have upper_half : minimaxRisk T H η ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    refine (iInf_le (fun Ψ => risk T H η Ψ) (fun _ => 1 / 2)).trans ?_
    refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => ?_
    apply ENNReal.ofReal_le_ofReal
    have h0 := pow_nonneg a.property.1.le H
    have h1 := pow_le_one₀ a.property.1.le a.property.2.le (n := H)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have upper_rate : minimaxRisk T H η ≤ ENNReal.ofReal (η * H / T) := by
    refine (iInf_le (fun Ψ => risk T H η Ψ) (endpointEstimator T H)).trans ?_
    refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => ?_
    apply ENNReal.ofReal_le_ofReal
    let z : ℝ := max 0 (min 1 (y ⟨T, Nat.lt_succ_self T⟩))
    have hz0 : 0 ≤ z := le_max_left _ _
    have hz1 : z ≤ 1 := max_le (by norm_num) (min_le_left _ _)
    have ha0 : 0 ≤ a.val ^ T := pow_nonneg a.property.1.le T
    have ha1 : a.val ^ T ≤ 1 := pow_le_one₀ a.property.1.le a.property.2.le
    have hnoise := abs_le.mp (hy ⟨T, Nat.lt_succ_self T⟩)
    have hzerr : |z - a.val ^ T| ≤ η := by
      apply abs_le.mpr
      dsimp [z]
      constructor
      · have hlow : a.val ^ T - η ≤ min 1 (y ⟨T, Nat.lt_succ_self T⟩) :=
          le_min (by linarith) (by simpa using hnoise.1)
        have := hlow.trans (le_max_right 0 _)
        linarith
      · have hh : min 1 (y ⟨T, Nat.lt_succ_self T⟩) ≤ a.val ^ T + η :=
          (min_le_right _ _).trans (by linarith [hnoise.2])
        have := max_le (show 0 ≤ a.val ^ T + η by positivity) hh
        linarith
    have hp : (1 : ℝ) ≤ (H : ℝ) / T := (le_div_iff₀ hTr).mpr (by simpa using hTHr)
    have hlip := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := fun x : ℝ => x ^ ((H : ℝ) / T)) (C := (H : ℝ) / T)
      (fun x _ => (Real.hasDerivAt_rpow_const (Or.inr hp)).differentiableAt) ?_
      ⟨ha0, ha1⟩ ⟨hz0, hz1⟩
    · have he : (a.val ^ T) ^ ((H : ℝ) / T) = a.val ^ H := by
        rw [← Real.rpow_natCast_mul a.property.1.le, mul_div_cancel₀ _ hTr.ne', Real.rpow_natCast]
      rw [he, Real.norm_eq_abs, Real.norm_eq_abs] at hlip
      change |z ^ ((H : ℝ) / T) - a.val ^ H| ≤ _
      calc
        _ ≤ ((H : ℝ) / T) * |z - a.val ^ T| := hlip
        _ ≤ ((H : ℝ) / T) * η := mul_le_mul_of_nonneg_left hzerr (by positivity)
        _ = η * H / T := by ring
    · intro x hx
      rw [Real.deriv_rpow_const, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hx.1 _))]
      have hh := Real.rpow_le_one hx.1 hx.2 (sub_nonneg.mpr hp)
      nlinarith [Real.rpow_nonneg hx.1 ((H : ℝ) / T - 1)]
  have upper : minimaxRisk T H η ≤ ENNReal.ofReal (min (1 / 2) (η * H / T)) := by
    rw [ENNReal.ofReal_min]
    exact le_min upper_half upper_rate
  refine ⟨⟨lower, upper⟩, ?_, ?_⟩
  · refine (ENNReal.ofReal_le_ofReal ?_).trans lower
    have hx : 0 ≤ η * H / T := by positivity
    have hm0 := min_le_left (1 : ℝ) (η * H / T)
    have hm1 := min_le_right (1 : ℝ) (η * H / T)
    apply le_min
    · have he : η * H / (2 * T) = (η * H / T) / 2 := by ring
      rw [he]
      linarith
    · linarith
  · exact upper.trans (ENNReal.ofReal_le_ofReal (min_le_min (by norm_num) le_rfl))

#print axioms finite_power_extrapolation_risk

end D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk

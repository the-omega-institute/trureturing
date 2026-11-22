/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-term midpoint estimate for the exponentially weighted root spectrum. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHRootTailModulus
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusEvenCutoffShrinkingRate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! The flat midpoint pairing and the normalized exponential perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp (c)

private theorem integral_pair {f : ℝ → ℝ} (hf : Continuous f) (u L : ℝ) :
    (∫ t in (0 : ℝ)..L, f (u + t) - f (u + L / 2)) =
      ∫ h in (0 : ℝ)..(L / 2), f (u + L / 2 + h) + f (u + L / 2 - h) -
        2 * f (u + L / 2) := by
  let g : ℝ → ℝ := fun t => f (u + t) - f (u + L / 2)
  have hg : Continuous g := (hf.comp (continuous_const.add continuous_id)).sub continuous_const
  change (∫ t in (0 : ℝ)..L, g t) = _
  have hleft :
      (∫ h in (0 : ℝ)..(L / 2), g (L / 2 - h)) = ∫ t in (0 : ℝ)..(L / 2), g t := by
    rw [intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  have hright :
      (∫ h in (0 : ℝ)..(L / 2), g (L / 2 + h)) = ∫ t in (L / 2)..L, g t := by
    rw [intervalIntegral.integral_comp_add_left, add_zero, add_halves]
  have hplus : Continuous (fun h => g (L / 2 + h)) :=
    hg.comp (continuous_const.add continuous_id)
  have hminus : Continuous (fun h => g (L / 2 - h)) :=
    hg.comp (continuous_const.sub continuous_id)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable 0 (L / 2)) (hg.intervalIntegrable (L / 2) L),
    ← hright, ← hleft, add_comm (∫ h in (0 : ℝ)..(L / 2), g (L / 2 - h)),
    ← intervalIntegral.integral_add
      (hplus.intervalIntegrable 0 (L / 2)) (hminus.intervalIntegrable 0 (L / 2))]
  apply intervalIntegral.integral_congr
  intro h _
  dsimp [g]
  rw [show u + (L / 2 + h) = u + L / 2 + h by ring,
    show u + (L / 2 - h) = u + L / 2 - h by ring]
  ring

private theorem continuous_cusp_profile (s b : ℝ) :
    Continuous (fun h : ℝ => (h / s) * (Real.log (1 / h) + b)) := by
  simp_rw [one_div, Real.log_inv, div_mul_eq_mul_div, mul_add, mul_neg]
  exact (Real.continuous_mul_log.neg.add (continuous_id.mul continuous_const)).div_const _

private theorem integral_cusp_profile {L s : ℝ} (hL : 0 < L) (b : ℝ) :
    (∫ h in (0 : ℝ)..(L / 2), (h / s) * (Real.log (1 / h) + b)) =
      (L ^ 2 / (8 * s)) * (Real.log (1 / L) + Real.log 2 + b + 1 / 2) := by
  let F : ℝ → ℝ := fun h => h ^ 2 / (2 * s) * (-Real.log h + b + 1 / 2)
  have hF : Continuous F := by
    have heq : F = fun h => (-(h * (h * Real.log h)) + h ^ 2 * (b + 1 / 2)) / (2 * s) := by
      funext h
      dsimp [F]
      ring
    rw [heq]
    exact ((continuous_id.mul Real.continuous_mul_log).neg.add
      ((continuous_id.pow 2).mul continuous_const)).div_const _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith : 0 ≤ L / 2)
    hF.continuousOn _ ((continuous_cusp_profile s b).intervalIntegrable _ _)]
  · dsimp [F]
    rw [show (0 : ℝ) ^ 2 / (2 * s) * (-Real.log 0 + b + 1 / 2) = 0 by simp, sub_zero,
      Real.log_div hL.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [one_div, Real.log_inv]
    ring
  · intro h hh
    have hh0 : 0 < h := hh.1
    have hp := (((hasDerivAt_id h).pow 2).div_const (2 * s)).mul
      (((Real.hasDerivAt_log hh0.ne').neg.add_const b).add_const (1 / 2))
    change HasDerivAt F
      ((2 : ℕ) * h ^ (2 - 1 : ℕ) * 1 / (2 * s) * (-Real.log h + b + 1 / 2) +
        h ^ 2 / (2 * s) * (-h⁻¹)) h at hp
    convert hp using 1
    simp only [one_div, Real.log_inv]
    norm_num
    field_simp [hh0.ne']
    ring

private theorem exponential_average_perturbation {f : ℝ → ℝ} (hf : Continuous f)
    {s L B : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) (hL : 0 < L) (hL' : L ≤ 1 / 4)
    {u : ℝ} (hB : ∀ t ∈ Icc 0 L, |f (u + t) - f (u + L / 2)| ≤ B) :
    |((∫ t in (0 : ℝ)..L, Real.exp (-s * t) * f (u + t)) /
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - f (u + L / 2)) -
        (∫ t in (0 : ℝ)..L, f (u + t) - f (u + L / 2)) / L| ≤ B * L := by
  let w : ℝ → ℝ := fun t => Real.exp (-s * t)
  let W := ∫ t in (0 : ℝ)..L, w t
  let S : ℝ → ℝ := fun t => f (u + t)
  let q := f (u + L / 2)
  let D : ℝ → ℝ := fun t => S t - q
  have hw : Continuous w := by fun_prop
  have hS : Continuous S := hf.comp (continuous_const.add continuous_id)
  have hD : Continuous D := hS.sub continuous_const
  have hweight (t : ℝ) (ht : t ∈ Icc 0 L) : 1 - L / 2 ≤ w t ∧ w t ≤ 1 := by
    refine ⟨?_, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht.1)⟩
    have hst : s * t ≤ (1 / 2) * L := mul_le_mul hs' ht.2 ht.1 (by norm_num)
    dsimp [w]
    linarith [Real.add_one_le_exp (-s * t)]
  have hmassLower : L * (1 - L / 2) ≤ W := by
    calc
      _ = ∫ _ in (0 : ℝ)..L, 1 - L / 2 := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      _ ≤ W := intervalIntegral.integral_mono_on hL.le
        (continuous_const.intervalIntegrable 0 L) (hw.intervalIntegrable _ _) (fun t ht => (hweight t ht).1)
  have hmassUpper : W ≤ L := by
    calc
      W ≤ ∫ _ in (0 : ℝ)..L, (1 : ℝ) := intervalIntegral.integral_mono_on hL.le
        (hw.intervalIntegrable _ _) (continuous_const.intervalIntegrable 0 L) (fun t ht => (hweight t ht).2)
      _ = L := by simp
  have hhalf : L / 2 ≤ W := by
    have hh : L * (1 / 2) ≤ L * (1 - L / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hL.le
    linarith
  have hW : 0 < W := by linarith
  have hnormalized (t : ℝ) (ht : t ∈ Icc 0 L) : |w t / W - 1 / L| ≤ 1 := by
    obtain ⟨hl, hu⟩ := hweight t ht
    have hl' := mul_le_mul_of_nonneg_right hl hL.le
    have hu' := mul_le_mul_of_nonneg_right hu hL.le
    have hWL := mul_le_mul_of_nonneg_right hhalf hL.le
    rw [show w t / W - 1 / L = (w t * L - W) / (W * L) by field_simp,
      abs_div, abs_of_pos (mul_pos hW hL), div_le_iff₀ (mul_pos hW hL), one_mul, abs_le]
    constructor <;> nlinarith only [hl', hu', hWL, hmassLower, hmassUpper]
  have hcenter :
      (∫ t in (0 : ℝ)..L, w t * D t) = (∫ t in (0 : ℝ)..L, w t * S t) - W * q := by
    simp only [D, mul_sub]
    rw [intervalIntegral.integral_sub (f := fun t => w t * S t) (g := fun t => w t * q)
      ((hw.mul hS).intervalIntegrable 0 L) ((hw.mul continuous_const).intervalIntegrable 0 L),
      intervalIntegral.integral_mul_const]
  have hcompare :
      (∫ t in (0 : ℝ)..L, (w t / W - 1 / L) * D t) =
        (∫ t in (0 : ℝ)..L, w t * S t) / W - q - (∫ t in (0 : ℝ)..L, D t) / L := by
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub (f := fun t => w t / W * D t)
      (g := fun t => 1 / L * D t) (((hw.div_const W).mul hD).intervalIntegrable 0 L)
      ((continuous_const.mul hD).intervalIntegrable 0 L)]
    simp_rw [div_mul_eq_mul_div]
    simp only [one_mul, intervalIntegral.integral_div, hcenter]
    field_simp [hW.ne']
  change |(∫ t in (0 : ℝ)..L, w t * S t) / W - q - (∫ t in (0 : ℝ)..L, D t) / L| ≤ _
  rw [← hcompare, ← Real.norm_eq_abs]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => (w t / W - 1 / L) * D t) (a := 0) (b := L) (C := B) (by
      intro t ht
      rw [uIoc_of_le hL.le] at ht
      have ht' := Ioc_subset_Icc_self ht
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ 1 * |D t| := mul_le_mul_of_nonneg_right (hnormalized t ht') (abs_nonneg _)
        _ ≤ B := by simpa only [one_mul] using hB t ht')
  simpa only [sub_zero, abs_of_pos hL] using hnorm

/-- Under RH, the exponential root average has a uniform two-term midpoint bound.
The window centered at zero attains its leading profile from below with the same error. -/
theorem root_signal_exponential_midpoint (hRH : RiemannHypothesis) {r : ℝ} (hr : 1 < r) :
    let s : ℝ := 1 / 2 - (2 * r)⁻¹
    let G := fun L : ℝ => (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
    let M := fun u L : ℝ =>
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
        (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)
    ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
      (∀ u : ℝ, |M u L| ≤ G L + C * L ^ 2 * (1 + Real.log (1 / L)) ^ 2) ∧
      G L - C * L ^ 2 * (1 + Real.log (1 / L)) ^ 2 ≤ M (-L / 2) L := by
  dsimp only
  let s : ℝ := 1 / 2 - (2 * r)⁻¹
  let G := fun L : ℝ => (L / (8 * s)) * (Real.log (1 / L) + Real.log (2 * r) - 2 * c + 1 / 2)
  let M := fun u L : ℝ =>
    (∫ t in (0 : ℝ)..L, Real.exp (-s * t) * rootSignal r (u + t)) /
      (∫ t in (0 : ℝ)..L, Real.exp (-s * t)) - rootSignal r (u + L / 2)
  change ∃ C > 0, ∀ L : ℝ, 0 < L → L ≤ 1 / 4 →
    (∀ u : ℝ, |M u L| ≤ G L + C * L ^ 2 * (1 + Real.log (1 / L)) ^ 2) ∧
    G L - C * L ^ 2 * (1 + Real.log (1 / L)) ^ 2 ≤ M (-L / 2) L
  have hr0 : 0 < r := by linarith
  have hs : 0 < s := by
    dsimp [s]
    rw [inv_eq_one_div, sub_pos]
    exact (div_lt_iff₀ (by positivity)).2 (by linarith)
  have hs' : s ≤ 1 / 2 := sub_le_self _ (by positivity)
  obtain ⟨C₁, hC₁, hupper⟩ := root_signal_symmetric_tail_modulus hRH hr
  obtain ⟨C₂, hC₂, hlower⟩ := root_signal_symmetric_cusp hRH hr
  obtain ⟨C₃, hC₃, hmod⟩ := root_signal_increment_le hRH hr
  have hS := (root_signal_uniformContinuous hRH hr).continuous
  refine ⟨C₁ + C₂ + C₃, by positivity, fun L hL hL' => ?_⟩
  let D := fun u h : ℝ =>
    rootSignal r (u + h) + rootSignal r (u - h) - 2 * rootSignal r u
  let b := Real.log r - 2 * c
  let A := fun h : ℝ => (h / s) * (Real.log (1 / h) + b)
  let B := (1 + Real.log (1 / L)) ^ 2
  let F := fun u : ℝ => (∫ t in (0 : ℝ)..L, rootSignal r (u + t) - rootSignal r (u + L / 2)) / L
  have hB : 1 ≤ B := by
    have hlog := Real.log_nonneg ((le_div_iff₀ hL).2 (by linarith : 1 * L ≤ 1))
    dsimp [B]
    nlinarith [sq_nonneg (Real.log (1 / L))]
  have hD (u : ℝ) : Continuous (D u) := by
    exact ((hS.comp (continuous_const.add continuous_id)).add
      (hS.comp (continuous_const.sub continuous_id))).sub continuous_const
  have hA : Continuous A := continuous_cusp_profile s b
  have hintA : (∫ h in (0 : ℝ)..(L / 2), A h) = L * G L := by
    dsimp [A, G]
    rw [integral_cusp_profile hL, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr0.ne']
    dsimp [b]
    ring
  have hpair (u : ℝ) :
      F u = (∫ h in (0 : ℝ)..(L / 2), D (u + L / 2) h) / L := by
    exact congrArg (· / L) (integral_pair hS u L)
  have herror (u : ℝ) : |M u L - F u| ≤ C₃ * L ^ 2 * B := by
    have ht (t : ℝ) (ht' : t ∈ Icc 0 L) : |t - L / 2| ≤ L :=
      abs_le.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    have hm (t : ℝ) (ht' : t ∈ Icc 0 L) :
        |rootSignal r (u + t) - rootSignal r (u + L / 2)| ≤ C₃ * L * B := by
      have h := hmod (u + L / 2) (t - L / 2) L hL hL' (ht t ht')
      rw [show u + L / 2 + (t - L / 2) = u + t by ring] at h
      simpa only [B, one_div] using h
    have h := exponential_average_perturbation hS hs.le hs' hL hL' hm
    change |M u L - F u| ≤ C₃ * L * B * L at h
    convert h using 1 <;> ring
  have hquad (h : ℝ) (hh : h ∈ Ioo 0 (L / 2)) : h ^ 2 ≤ L ^ 2 := by
    exact (sq_le_sq₀ hh.1.le hL.le).2 (by linarith [hh.2])
  have hflatUpper (u : ℝ) : |F u| ≤ G L + C₁ * L ^ 2 / 2 := by
    rw [hpair, abs_div, abs_of_pos hL, div_le_iff₀ hL]
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (f := D (u + L / 2)) (μ := volume) (by linarith : 0 ≤ L / 2)
    simp only [Real.norm_eq_abs] at hnorm
    have hbound : (∫ h in (0 : ℝ)..(L / 2), |D (u + L / 2) h|) ≤
        ∫ h in (0 : ℝ)..(L / 2), A h + C₁ * L ^ 2 := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
        ((hD _).abs.intervalIntegrable _ _) ((hA.add continuous_const).intervalIntegrable _ _)
      intro h hh
      obtain ⟨_, hbounded, hsup⟩ := hupper (u + L / 2) h hh.1 (by linarith [hh.2])
      have hle : |D (u + L / 2) h| ≤ _ := le_csSup hbounded
        ⟨u + L / 2, mem_Ici.mpr le_rfl, rfl⟩
      have hprofile : |D (u + L / 2) h| ≤ A h + C₁ * h ^ 2 := by
        have hi := (abs_le.mp hsup).2
        dsimp [A, b]
        linarith
      exact hprofile.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (hquad h hh) hC₁.le) _)
    rw [intervalIntegral.integral_add (hA.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable 0 (L / 2)), hintA, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul] at hbound
    exact (hnorm.trans hbound).trans_eq (by ring)
  have hflatLower : G L - C₂ * L ^ 2 / 2 ≤ F (-L / 2) := by
    rw [hpair, le_div_iff₀ hL, show -L / 2 + L / 2 = 0 by ring]
    have hbound : (∫ h in (0 : ℝ)..(L / 2), A h - C₂ * L ^ 2) ≤
        ∫ h in (0 : ℝ)..(L / 2), D 0 h := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
        ((hA.sub continuous_const).intervalIntegrable _ _) ((hD 0).intervalIntegrable _ _)
      intro h hh
      have hc := (abs_le.mp (hlower h hh.1 (by linarith [hh.2]))).1
      have hq := mul_le_mul_of_nonneg_left (hquad h hh) hC₂.le
      simp only [D, zero_add, zero_sub]
      dsimp [A, b]
      linarith
    rw [intervalIntegral.integral_sub (hA.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable 0 (L / 2)), hintA, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul] at hbound
    exact (show (G L - C₂ * L ^ 2 / 2) * L = _ by ring).trans_le hbound
  have hscale₁ : C₁ * L ^ 2 / 2 ≤ C₁ * L ^ 2 * B := by
    nlinarith [mul_nonneg (mul_nonneg hC₁.le (sq_nonneg L)) (sub_nonneg.mpr hB)]
  have hscale₂ : C₂ * L ^ 2 / 2 ≤ C₂ * L ^ 2 * B := by
    nlinarith [mul_nonneg (mul_nonneg hC₂.le (sq_nonneg L)) (sub_nonneg.mpr hB)]
  have hbudget₁ : 0 ≤ C₁ * L ^ 2 * B := by positivity
  have hbudget₂ : 0 ≤ C₂ * L ^ 2 * B := by positivity
  change (∀ u, |M u L| ≤ G L + (C₁ + C₂ + C₃) * L ^ 2 * B) ∧
    G L - (C₁ + C₂ + C₃) * L ^ 2 * B ≤ M (-L / 2) L
  constructor
  · intro u
    have htriangle : |M u L| ≤ |M u L - F u| + |F u| := by
      simpa only [sub_add_cancel] using abs_add_le (M u L - F u) (F u)
    linarith only [htriangle, herror u, hflatUpper u, hscale₁, hbudget₂]
  · linarith only [(abs_le.mp (herror (-L / 2))).1, hflatLower, hscale₂, hbudget₁]

#print axioms root_signal_exponential_midpoint

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

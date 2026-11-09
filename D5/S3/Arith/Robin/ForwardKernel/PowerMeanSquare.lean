/- GID: D5/S3/Arith/Robin/ForwardKernel/PowerMeanSquare
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PowerMeanSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The forward response has power mean-square mass and absolute power excursions. -/

import D5.S3.Analytic.Oscillation.PairedLaplaceWindow
import D5.S3.Arith.Robin.ForwardKernel.GaussianLaplace
import D5.S3.Weil.ZeroData.ZetaSpectrumLocalCount

/-! Exponential windows and absolute power excursions of the original forward response. -/

namespace D5.S3.Arith.Robin.ForwardKernel

open Set MeasureTheory Filter
open scoped Topology
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Weil.ZeroData.PairedXiExpansion (PairedXiExpansion)
open D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth (VonKochBound)
open ForwardKernel.Transport (forwardResponse)

noncomputable section
set_option autoImplicit false

private lemma integral_square_exp {a b : ℝ} (hab : a ≤ b) (ha : Real.log 3 < a) :
    (∫ y in a..b, forwardLog 3 y ^ 2) =
      ∫ x in Real.exp a..Real.exp b, forwardResponse x ^ 2 / x := by
  rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab)]
  rw [← Real.image_exp_Ioc]
  have hsub := integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Ioc (a := a) (b := b))
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun x => forwardResponse x ^ 2 / x)
  rw [hsub]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro y hy
  dsimp only
  rw [abs_of_pos (Real.exp_pos y), smul_eq_mul, forwardLog,
    ite_eq_left (ha.trans hy.1)]
  field_simp

private lemma power_window_of_log_window {c : ℝ}
    (hmean : ∀ᶠ M : ℝ in atTop,
      c * M * (Real.log M) ^ 2 ≤
        ∫ y in (16 * Real.log M - 2)..(20 * Real.log M + 2), forwardLog 3 y ^ 2) :
    ∃ M₀ : ℝ, 1 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      c * M * (Real.log M) ^ 2 ≤
        ∫ x in (Real.exp (-2) * M ^ 16)..(Real.exp 2 * M ^ 20),
          forwardResponse x ^ 2 / x := by
  have hevent : ∀ᶠ M : ℝ in atTop,
      c * M * (Real.log M) ^ 2 ≤
        ∫ x in (Real.exp (-2) * M ^ 16)..(Real.exp 2 * M ^ 20),
          forwardResponse x ^ 2 / x := by
    filter_upwards [hmean, eventually_ge_atTop (Real.exp 1)] with M hm hM
    have hMp : 0 < M := (Real.exp_pos 1).trans_le hM
    have hL : 1 ≤ Real.log M := by
      simpa using Real.log_le_log (Real.exp_pos 1) hM
    have hlog3 : Real.log 3 < 2 := by
      convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≠ 1) using 1; norm_num
    have ha : Real.log 3 < 16 * Real.log M - 2 := by linarith
    have hab : 16 * Real.log M - 2 ≤ 20 * Real.log M + 2 := by linarith
    have hlo : Real.exp (16 * Real.log M - 2) = Real.exp (-2) * M ^ 16 := by
      rw [show 16 * Real.log M - 2 = -2 + (16 : ℕ) * Real.log M by ring,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log hMp]
    have hhi : Real.exp (20 * Real.log M + 2) = Real.exp 2 * M ^ 20 := by
      rw [show 20 * Real.log M + 2 = 2 + (20 : ℕ) * Real.log M by ring,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log hMp]
    rw [integral_square_exp hab ha, hlo, hhi] at hm
    exact hm
  obtain ⟨T, hT⟩ := hevent.exists_forall_of_atTop
  refine ⟨max T 2, by linarith [le_max_right T 2], ?_⟩
  intro M hM
  exact hT M ((le_max_left T 2).trans hM)

private lemma square_point_of_window {f : ℝ → ℝ} {c M L : ℝ}
    (hc : 0 < c) (hM : 0 < M) (hL : 1 ≤ L)
    (hmean : c * M * L ^ 2 ≤ ∫ y in (16 * L - 2)..(20 * L + 2), f y ^ 2) :
    ∃ y ∈ Ioc (16 * L - 2) (20 * L + 2), c / 16 * M * L ≤ f y ^ 2 := by
  by_contra hn
  push Not at hn
  have hbound : ∀ y ∈ Ioc (16 * L - 2) (20 * L + 2),
      ‖f y ^ 2‖ ≤ c / 16 * M * L := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hn y hy).le
  have hab : 16 * L - 2 ≤ 20 * L + 2 := by linarith
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 16 * L - 2) (b := 20 * L + 2)
    (f := fun y => f y ^ 2) (C := c / 16 * M * L)
    (by simpa [uIoc_of_le hab] using hbound)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  have hint : (∫ y in (16 * L - 2)..(20 * L + 2), f y ^ 2) ≤
      (20 * L + 2 - (16 * L - 2)) * (c / 16 * M * L) :=
    (le_abs_self _).trans (by simpa [mul_comm] using hnorm)
  have hML : 0 < c * M * L := by positivity
  have hLL : (4 * L + 4) * L ≤ 8 * L ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hLL (show 0 ≤ c * M by positivity)
  nlinarith

private lemma power_weight_le {c M y : ℝ} (hc : 0 < c) (hM : 0 < M)
    (hL : 1 ≤ Real.log M)
    (hy : y ∈ Ioc (16 * Real.log M - 2) (20 * Real.log M + 2)) :
    ((Real.sqrt (c / 352) / Real.exp 1) *
      (Real.exp y) ^ (1 / 40 : ℝ) * Real.sqrt (Real.log (Real.exp y))) ^ 2 ≤
      c / 16 * M * Real.log M := by
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hyp : y ≤ 22 * Real.log M := by linarith [hy.2]
  have he : Real.exp (y / 20) ≤ M * Real.exp 1 ^ 2 := by
    calc
      Real.exp (y / 20) ≤ Real.exp (Real.log M + 2) :=
        Real.exp_le_exp.mpr (by linarith [hy.2])
      _ = M * Real.exp 1 ^ 2 := by
        rw [Real.exp_add, Real.exp_log hM]
        congr 1
        rw [← Real.exp_nat_mul]
        norm_num
  have hpow : ((Real.exp y) ^ (1 / 40 : ℝ)) ^ 2 = Real.exp (y / 20) := by
    rw [← Real.exp_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by positivity),
    Real.log_exp, Real.sq_sqrt hy0, hpow]
  calc
    (c / 352 / Real.exp 1 ^ 2) * Real.exp (y / 20) * y ≤
        (c / 352 / Real.exp 1 ^ 2) * (M * Real.exp 1 ^ 2) * y := by
      gcongr
    _ = c / 352 * M * y := by field_simp
    _ ≤ c / 352 * M * (22 * Real.log M) := by gcongr
    _ = c / 16 * M * Real.log M := by ring

private lemma forward_omega_of_log_window {c : ℝ} (hc : 0 < c)
    (hmean : ∀ᶠ M : ℝ in atTop,
      c * M * (Real.log M) ^ 2 ≤
        ∫ y in (16 * Real.log M - 2)..(20 * Real.log M + 2), forwardLog 3 y ^ 2) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ X : ℝ, ∃ x : ℝ,
      X ≤ x ∧ 3 < x ∧
      c₁ * x ^ (1 / 40 : ℝ) * Real.sqrt (Real.log x) ≤ |forwardResponse x| := by
  refine ⟨Real.sqrt (c / 352) / Real.exp 1, by positivity, ?_⟩
  intro X
  obtain ⟨T, hT⟩ := hmean.exists_forall_of_atTop
  let L := max (max (Real.log (max T 1)) 1) (max (Real.log X) (Real.log 3) + 3)
  let M := Real.exp L
  have hL : 1 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hlogM : Real.log M = L := Real.log_exp L
  have hM : 0 < M := Real.exp_pos L
  have hMT : T ≤ M := by
    calc
      T ≤ max T 1 := le_max_left _ _
      _ = Real.exp (Real.log (max T 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ M := Real.exp_le_exp.mpr
        ((le_max_left _ _).trans (le_max_left _ _))
  have hLX : Real.log X + 3 ≤ L := by
    have h := le_max_left (Real.log X) (Real.log 3)
    have h' := le_max_right (max (Real.log (max T 1)) 1)
      (max (Real.log X) (Real.log 3) + 3)
    dsimp [L]
    linarith
  have hL3 : Real.log 3 + 3 ≤ L := by
    have h := le_max_right (Real.log X) (Real.log 3)
    have h' := le_max_right (max (Real.log (max T 1)) 1)
      (max (Real.log X) (Real.log 3) + 3)
    dsimp [L]
    linarith
  obtain ⟨y, hy, hfy⟩ := square_point_of_window hc hM hL (by simpa [hlogM] using hT M hMT)
  have hyX : Real.log X ≤ y := by linarith [hy.1]
  have hy3 : Real.log 3 < y := by linarith [hy.1]
  have hxX : X ≤ Real.exp y := by
    by_cases hX : 0 < X
    · exact (Real.exp_log hX).symm ▸ Real.exp_le_exp.mpr hyX
    · exact (le_of_not_gt hX).trans (Real.exp_pos y).le
  have hx3 : (3 : ℝ) < Real.exp y := by
    calc
      (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp y := Real.exp_lt_exp.mpr hy3
  have hweight := power_weight_le hc hM (by simpa [hlogM] using hL)
    (by simpa [hlogM] using hy)
  have hforward : forwardLog 3 y = forwardResponse (Real.exp y) := by
    rw [forwardLog, ite_eq_left hy3]
  refine ⟨Real.exp y, hxX, hx3, ?_⟩
  have hsquare :
      ((Real.sqrt (c / 352) / Real.exp 1) *
        (Real.exp y) ^ (1 / 40 : ℝ) * Real.sqrt (Real.log (Real.exp y))) ^ 2 ≤
      |forwardResponse (Real.exp y)| ^ 2 := by
    rw [sq_abs]
    exact hweight.trans (by simpa [hlogM, hforward] using hfy)
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp hsquare

theorem forward_kernel_power_window_mean_square
    (hRH : RiemannHypothesis) (hVK : VonKochBound)
    (hXi : PairedXiExpansion hRH)
    (hMont : D5.S3.Analytic.Oscillation.MontgomeryWindow.AveragedMontgomeryLower
      (zetaSpectrum hRH)) :
    ∃ c M₀ : ℝ, 0 < c ∧ 1 < M₀ ∧
      ∀ M : ℝ, M₀ ≤ M →
        c * M * (Real.log M) ^ 2 ≤
          ∫ x in (Real.exp (-2) * M ^ 16)..(Real.exp 2 * M ^ 20),
            forwardResponse x ^ 2 / x := by
  obtain ⟨c, hc, hm⟩ :=
    D5.S3.Analytic.Oscillation.PairedLaplaceWindow.paired_laplace_window_lower
      (zetaSpectrum hRH)
      (D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic hRH)
      (D5.S3.Weil.ZeroData.ZetaSpectrumLocalCount.zetaSpectrum_localCount hRH) hMont
      (forwardPairedLaplaceData hRH hVK hXi (x0 := 3) (by norm_num))
      (forwardPairedLaplaceData_gaussianStrip hRH hVK hXi)
  obtain ⟨M₀, hM₀, hbound⟩ := power_window_of_log_window hm
  exact ⟨c, M₀, hc, hM₀, hbound⟩

theorem forward_kernel_omega_abs_power
    (hRH : RiemannHypothesis) (hVK : VonKochBound)
    (hXi : PairedXiExpansion hRH)
    (hMont : D5.S3.Analytic.Oscillation.MontgomeryWindow.AveragedMontgomeryLower
      (zetaSpectrum hRH)) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∀ X : ℝ, ∃ x : ℝ,
        X ≤ x ∧ 3 < x ∧
        c₁ * x ^ (1 / 40 : ℝ) * Real.sqrt (Real.log x) ≤ |forwardResponse x| := by
  obtain ⟨c, hc, hm⟩ :=
    D5.S3.Analytic.Oscillation.PairedLaplaceWindow.paired_laplace_window_lower
      (zetaSpectrum hRH)
      (D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic hRH)
      (D5.S3.Weil.ZeroData.ZetaSpectrumLocalCount.zetaSpectrum_localCount hRH) hMont
      (forwardPairedLaplaceData hRH hVK hXi (x0 := 3) (by norm_num))
      (forwardPairedLaplaceData_gaussianStrip hRH hVK hXi)
  exact forward_omega_of_log_window hc hm

end
end D5.S3.Arith.Robin.ForwardKernel

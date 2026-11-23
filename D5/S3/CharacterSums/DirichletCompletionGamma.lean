/- GID: D5/S3/CharacterSums/DirichletCompletionGamma
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletCompletionGamma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euler's integral and convexity bound Gamma on a right half-plane. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-! # Gamma bounds for Dirichlet completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set MeasureTheory

namespace D5.S3.CharacterSums.DirichletCompletionGamma

/-- Euler's integral bounds the complex Gamma function by its real counterpart. -/
theorem norm_Gamma_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Convexity reduces the real Gamma estimate to a fixed point and an integer factorial. -/
theorem Gamma_le_max_factorial {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ max (Real.Gamma (1 / 4)) (Nat.factorial ⌈u⌉₊ : ℝ) := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0)
    (show ((⌈u⌉₊ : ℝ) + 1) ∈ Ioi 0 by
      change 0 < (⌈u⌉₊ : ℝ) + 1
      positivity)
    (show u ∈ Icc (1 / 4) ((⌈u⌉₊ : ℝ) + 1) from
      ⟨hu, (Nat.le_ceil u).trans (by linarith)⟩)
  simpa only [Real.Gamma_nat_eq_factorial] using h

/-- A logarithmic-exponential bound with an explicit constant. -/
theorem Gamma_le_exp_bound {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ max 1 (Real.Gamma (1 / 4)) *
      Real.exp ((u + 1) * Real.log (u + 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hup : 0 < u + 1 := by linarith
  have hn : (⌈u⌉₊ : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one hu0).le
  have hl : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
  have he : 1 ≤ Real.exp ((u + 1) * Real.log (u + 1)) :=
    Real.one_le_exp (mul_nonneg hup.le hl)
  have hfac : (Nat.factorial ⌈u⌉₊ : ℝ) ≤
      Real.exp ((u + 1) * Real.log (u + 1)) := by
    calc
      _ ≤ (⌈u⌉₊ : ℝ) ^ ⌈u⌉₊ := by exact_mod_cast Nat.factorial_le_pow ⌈u⌉₊
      _ ≤ (u + 1) ^ ⌈u⌉₊ := pow_le_pow_left₀ (by positivity) hn _
      _ = Real.exp (Real.log (u + 1) * (⌈u⌉₊ : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hup]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  refine (Gamma_le_max_factorial hu).trans (max_le ?_ ?_)
  · calc
      Real.Gamma (1 / 4) ≤ max 1 (Real.Gamma (1 / 4)) := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he
  · exact hfac.trans (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _))

/-- The real-part bound for Deligne's real archimedean factor. -/
theorem norm_GammaReal_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [div_ofNat_re, neg_re]
  have hg := norm_Gamma_le (z := s / 2) (by simpa using div_pos hs two_pos)
  simpa only [div_ofNat_re] using mul_le_mul_of_nonneg_left hg
    (Real.rpow_nonneg Real.pi_pos.le _)

end D5.S3.CharacterSums.DirichletCompletionGamma

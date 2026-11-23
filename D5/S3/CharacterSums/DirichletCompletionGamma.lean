/- GID: D5/S3/CharacterSums/DirichletCompletionGamma
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletCompletionGamma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gamma products, convexity and integral tests bound completion factors. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Convex.Jensen
import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
import D5.S3.Weil.Mertens.Estimates
import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet.Foundation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Gamma and Dirichlet-series bounds for completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology
open ConjectureMachines.Semantics.Riemann.DigammaBinet

namespace D5.S3.CharacterSums.DirichletCompletionGamma

open private norm_Gamma_sq_eq one_le_gammaVertProd from
  D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds

/-- The vertical Gamma product bounds Gamma by its real value. -/
theorem norm_Gamma_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have he := norm_Gamma_sq_eq hz z.im
  have hp := one_le_gammaVertProd z.re z.im
  have hz' : (z.re : ℂ) + I * z.im = z := by
    apply Complex.ext <;> simp
  rw [hz'] at he
  have hb : ‖Complex.Gamma z‖ ^ 2 ≤ Real.Gamma z.re ^ 2 := by
    rw [he]
    exact div_le_self (sq_nonneg _) hp
  nlinarith [norm_nonneg (Complex.Gamma z), Real.Gamma_pos_of_pos hz]

/-- Convexity reduces the real Gamma estimate to a fixed point and an integer factorial. -/
theorem Gamma_le_max_factorial {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ max (Real.Gamma (1 / 4)) (Nat.factorial (⌈u⌉₊ - 1) : ℝ) := by
  have hn : 0 < ⌈u⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc
    (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0)
    (show (⌈u⌉₊ : ℝ) ∈ Ioi 0 by
      change 0 < (⌈u⌉₊ : ℝ)
      exact_mod_cast hn)
    (show u ∈ Icc (1 / 4) (⌈u⌉₊ : ℝ) from ⟨hu, Nat.le_ceil u⟩)
  have he : (⌈u⌉₊ : ℝ) = ((⌈u⌉₊ - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hn).symm
  simpa only [he, Real.Gamma_nat_eq_factorial] using h

/-- The factorial contribution is strictly below an elementary exponential. -/
theorem Gamma_le_exp_bound {u : ℝ} (hu : 1 / 4 ≤ u) :
    Real.Gamma u ≤ max (Real.Gamma (1 / 4))
      (Real.exp ((u + 1) * Real.log (u + 1))) := by
  have hu0 : 0 ≤ u := by linarith
  have hup : 0 < u + 1 := by linarith
  have hn : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu0
  have hl : 0 < Real.log (u + 1) := Real.log_pos (by linarith)
  have hfac : (Nat.factorial (⌈u⌉₊ - 1) : ℝ) <
      Real.exp ((u + 1) * Real.log (u + 1)) := by
    calc
      _ ≤ (Nat.factorial ⌈u⌉₊ : ℝ) := by
        exact_mod_cast Nat.factorial_le (Nat.sub_le ⌈u⌉₊ 1)
      _ ≤ (⌈u⌉₊ : ℝ) ^ ⌈u⌉₊ := by exact_mod_cast Nat.factorial_le_pow ⌈u⌉₊
      _ ≤ (u + 1) ^ ⌈u⌉₊ := pow_le_pow_left₀ (by positivity) hn.le _
      _ = Real.exp (Real.log (u + 1) * (⌈u⌉₊ : ℝ)) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hup]
      _ < _ := Real.exp_lt_exp.mpr (by nlinarith)
  exact (Gamma_le_max_factorial hu).trans (max_le_max le_rfl hfac.le)

/-- The real-part bound for Deligne's real archimedean factor. -/
theorem norm_GammaReal_le {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.pi ^ (-s.re / 2) * Real.Gamma (s.re / 2) := by
  rw [Complex.Gammaℝ_def, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp only [div_ofNat_re, neg_re]
  have hg := norm_Gamma_le (z := s / 2) (by simpa using div_pos hs two_pos)
  simpa only [div_ofNat_re] using mul_le_mul_of_nonneg_left hg
    (Real.rpow_nonneg Real.pi_pos.le _)

/-- An explicit integral-test bound for the logarithmic Dirichlet series at two. -/
theorem logarithmic_series_bound :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) ∧
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 ∧
    Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 < 1 := by
  let f : ℝ → ℝ := fun x => Real.log (x + 2) / (x + 2) ^ 2
  open private antitoneOn_log_div_sq log_div_sq_is_deriv
    tendsto_antideriv_log_div_sq summable_log_div_sq from D5.S3.Weil.Mertens.Estimates in
  have htail : Summable (fun n : ℕ => Real.log (n + 3) / (n + 3) ^ 2) :=
    Mertens.summable_log_div_sq
  have hall : Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ 2) := by
    apply (summable_nat_add_iff 3).mp
    simpa only [Nat.cast_add, Nat.cast_ofNat] using htail
  open private antitoneOn_log_div_sq log_div_sq_is_deriv
    tendsto_antideriv_log_div_sq from D5.S3.Weil.Mertens.Estimates in
  have hb : (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + Real.log 3 / 9 + (Real.log 3 + 1) / 3 := by
    have hd (x : ℝ) (hx : 1 ≤ x) := Mertens.log_div_sq_is_deriv x (by linarith)
    have hn (x : ℝ) (hx : 1 < x) : 0 ≤ f x :=
      div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)
    have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn
      Mertens.tendsto_antideriv_log_div_sq
    have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn
      Mertens.tendsto_antideriv_log_div_sq
    have hanti : AntitoneOn f (Ici (1 : ℝ)) :=
      Mertens.antitoneOn_log_div_sq.mono (by intro x hx; simp only [mem_Ici] at *; linarith)
    have htbound := hanti.tsum_comp_add_le_integral 1 hi hn
    have hh : (∫ x : ℝ in Ioi 1, f x) = (Real.log 3 + 1) / 3 := by
      convert he using 1 <;> norm_num <;> ring
    rw [hh] at htbound
    have hsplit := hall.sum_add_tsum_nat_add 4
    norm_num [Finset.sum_range_succ] at hsplit
    dsimp [f] at htbound
    norm_num [Nat.cast_add, add_assoc] at htbound
    linarith
  refine ⟨hall, ?_, ?_⟩
  · linarith [hb]
  · have h2 : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
    have h3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
    linarith

/-- Binet's remainder gives a uniform logarithmic bound on a Gamma strip. -/
theorem digamma_re_lt_log_height {z : ℂ} (hz : 1 ≤ z.re) (hz' : z.re ≤ 3 / 2) :
    (Complex.digamma z).re < Real.log (2 * |z.im| + 3) := by
  have hp : 0 < z.re := by linarith
  have hb := norm_digamma_sub_log_add_half_inv_le_re hp
  have hrep := (Complex.re_le_norm _).trans hb
  have hi : 0 ≤ (1 / (2 * z)).re := by
    rw [one_div, Complex.inv_re]
    exact div_nonneg (by simpa using hp.le) (Complex.normSq_nonneg _)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by intro h; simp [h] at hp)
  have hhalf : 1 / (2 * z.re) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hnorm : 2 * ‖z‖ ≤ 2 * |z.im| + 3 := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hp] at hh
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * ‖z‖) hnorm
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn.ne'] at hlog
  simp only [add_re, sub_re, Complex.log_re] at hrep
  linarith [Real.log_two_gt_d9]

end D5.S3.CharacterSums.DirichletCompletionGamma

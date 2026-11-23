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
import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Mertens.Cryptids.DigammaBinet.Foundation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Gamma bounds for Dirichlet completions -/

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
    (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ≤
      Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 ∧
    Real.log 2 / 4 + 4 * Real.log 3 / 9 + 1 / 3 < 1 := by
  let f : ℝ → ℝ := fun x => Real.log x / x ^ 2
  let g : ℝ → ℝ := fun x => -(Real.log x + 1) / x
  have hd (x : ℝ) (hx : 3 ≤ x) : HasDerivAt g (f x) x := by
    have hx0 : x ≠ 0 := by linarith
    have hh := (((Real.hasDerivAt_log hx0).add_const 1).neg.div
      (hasDerivAt_id x) hx0)
    convert hh using 1
    · rfl
    · dsimp [f]
      field_simp [hx0]
      <;> ring
  have hn (x : ℝ) (hx : 3 < x) : 0 ≤ f x :=
    div_nonneg (Real.log_nonneg (by linarith)) (sq_nonneg _)
  have ht : Tendsto g atTop (𝓝 0) := by
    have hlog := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop
      tendsto_id
    convert (hlog.add hinv).neg using 1
    · funext x
      simp [g, add_div, div_eq_mul_inv, mul_add, add_mul]
    · norm_num
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn ht
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn ht
  have hanti : AntitoneOn f (Ici (3 : ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) ?_ ?_ ?_
    · intro x hx
      have hx3 : 3 ≤ x := hx
      have hx0 : x ≠ 0 := by linarith
      exact ((Real.continuousAt_log hx0).div
        ((continuous_id.pow 2).continuousAt) (pow_ne_zero _ hx0)).continuousWithinAt
    · intro x hx
      have hx0 : x ≠ 0 := by simp only [interior_Ici, mem_Ioi] at hx; linarith
      exact (((Real.differentiableAt_log hx0).div
        (differentiableAt_id.pow 2) (pow_ne_zero _ hx0))).differentiableWithinAt
    · intro x hx
      have hx3 : 3 < x := by simpa only [interior_Ici, mem_Ioi] using hx
      have hx0 : x ≠ 0 := by linarith
      have hfd := (Real.hasDerivAt_log hx0).div ((hasDerivAt_id x).pow 2)
        (pow_ne_zero _ hx0)
      rw [show deriv f x = _ from hfd.deriv]
      have hl : 1 / 2 ≤ Real.log x := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ x)
        linarith [Real.log_two_gt_d9]
      dsimp only [Pi.pow_apply, id_eq]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp [hx0]
      nlinarith
  have hs := hanti.summable_of_integrableOn_Ioi (N := 3) hi hn
  have htbound := hanti.tsum_comp_add_le_integral 3 hi hn
  have hall : Summable (fun n : ℕ => f n) := hs
  have hsplit := hall.sum_add_tsum_nat_add 4
  have hb : (∑' n : ℕ, f n) ≤ f 2 + f 3 + (Real.log 3 + 1) / 3 := by
    dsimp [g] at he
    have hh : (∫ x : ℝ in Ioi 3, f x) = (Real.log 3 + 1) / 3 := by
      convert he using 1 <;> ring
    norm_num only [Nat.cast_ofNat] at htbound
    rw [hh] at htbound
    norm_num [Finset.sum_range_succ, f] at hsplit
    change (∑' n : ℕ, f n) ≤ _
    dsimp [f] at htbound ⊢
    norm_num [Nat.cast_add, add_assoc] at htbound ⊢
    linarith
  constructor
  · convert hb using 1 <;> dsimp [f] <;> ring
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

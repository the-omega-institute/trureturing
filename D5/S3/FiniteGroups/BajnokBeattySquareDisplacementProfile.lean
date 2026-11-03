/- GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementProfile
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementProfile
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Rational tail bounds for square-displacement profiles and scaling limits. -/

import D5.S0.Tower.DBonacci.PerronRoot
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

/-! The logarithm lower bound reuses the fixed order-nine Perron instance.
The quantitative input retains a real rational tail bound with decay, consumed
by both the uniform slope and the coefficient scaling limits. -/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile

open Filter Set
open D5.S0.Tower.DBonacci.PerronRoot

private noncomputable def nu (q : ℕ) : ℝ := (q : ℝ)^2
private noncomputable def beta (q : ℕ) : ℝ := dbonacciPerronRoot (q^2)
private noncomputable def sigma (q : ℕ) : ℝ := Real.log (beta q)
private noncomputable def gaussian (q : ℕ) (s : ℝ) : ℝ :=
  Real.exp s + Real.exp (-nu q * s)
private noncomputable def tail (q : ℕ) : ℝ := Real.exp (-nu q * sigma q)
private noncomputable def coefficient (q : ℕ) : ℝ :=
  (((q : ℝ)^2 + 1) * sigma q / (6 * (q : ℝ) * ((q : ℝ)^2 - 1))) *
    ((((q : ℝ)^4 + 1) * beta q - 2 * (q : ℝ)^4) /
      (((q : ℝ)^2 + 1) * beta q - 2 * (q : ℝ)^2))
private noncomputable def correction (q : ℕ) : ℝ :=
  coefficient q - 1 / (2 * (q : ℝ))

/-- The unsimplified cubic-plus-quartic factor supplies decay, not just a constant bound. -/
private theorem real_rational_tail {v : ℝ} (hv : 9 ≤ v) :
    0 < v^2 * Real.exp (-2 * v / 3) ∧
      v^2 * Real.exp (-2 * v / 3) < 243 / (2 * v * (v + 6)) ∧
      243 / (2 * v * (v + 6)) ≤ (9 / 10 : ℝ) := by
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have hden : 0 < 2 * v * (v + 6) := by positivity
  have ht := Real.sum_le_exp_of_nonneg (x := 2 * v / 3)
    (by positivity : 0 ≤ 2 * v / 3) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have hfactor : (2 * v / 3)^3 / 6 + (2 * v / 3)^4 / 24 =
      v^2 * (4 * v / 81 + 2 * v^2 / 243) := by ring
  have hpositive : 0 < 1 + 2 * v / 3 + (2 * v / 3)^2 / 2 := by positivity
  have hstrict : v^2 * (4 * v / 81 + 2 * v^2 / 243) <
      Real.exp (2 * v / 3) := by
    rw [← hfactor]
    linarith only [ht, hpositive]
  refine ⟨mul_pos (pow_pos hvpos 2) (Real.exp_pos _), ?_, ?_⟩
  · rw [show -2 * v / 3 = -(2 * v / 3) by ring, Real.exp_neg,
      ← div_eq_mul_inv]
    apply (div_lt_div_iff₀ (Real.exp_pos _) hden).2
    nlinarith only [hstrict]
  · apply (div_le_iff₀ hden).2
    have hproduct : 0 ≤ (v - 9) * (v + 15) :=
      mul_nonneg (sub_nonneg.mpr hv) (by linarith only [hv])
    nlinarith only [hproduct]

theorem real_rational_tail_on_ray {v s : ℝ}
    (hv : 9 ≤ v) (hs : (2 / 3 : ℝ) ≤ s) :
    0 < v^2 * Real.exp (-v * s) ∧
      v^2 * Real.exp (-v * s) < 243 / (2 * v * (v + 6)) ∧
      v^2 * Real.exp (-v * s) < (9 / 10 : ℝ) := by
  have hvpos : 0 < v := lt_of_lt_of_le (by norm_num) hv
  have he : Real.exp (-v * s) ≤ Real.exp (-2 * v / 3) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hs hvpos.le
    linarith only [h]
  have h := real_rational_tail hv
  have hsmall := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left he (sq_nonneg v)) h.2.1
  exact ⟨mul_pos (pow_pos hvpos 2) (Real.exp_pos _),
    hsmall, hsmall.trans_le h.2.2⟩

private theorem order_ge_nine {q : ℕ} (hq : 3 ≤ q) : 9 ≤ q^2 := by
  simpa only [pow_two] using Nat.mul_le_mul hq hq

private theorem nu_ge_nine {q : ℕ} (hq : 3 ≤ q) : (9 : ℝ) ≤ nu q := by
  have h := order_ge_nine hq
  dsimp [nu]
  exact_mod_cast h

theorem sigma_gt_two_thirds {q : ℕ} (hq : 3 ≤ q) :
    (2 / 3 : ℝ) < sigma q := by
  have hn := order_ge_nine hq
  have hmono : dbonacciPerronRoot 9 ≤ beta q :=
    dbonacciPerronRoot_strictMonoOn.monotoneOn (by norm_num)
      (show 2 ≤ q^2 by omega) hn
  have hb : 0 < beta q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot (q^2) (by omega))
  have hlog := Real.strictMonoOn_log.monotoneOn
    (lt_trans zero_lt_one (one_lt_dbonacciPerronRoot 9 (by norm_num))) hb hmono
  have h9 : (2 / 3 : ℝ) < Real.log (dbonacciPerronRoot 9) := by
    simpa only [D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.s_star] using
      D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.two_thirds_lt_s_star
  exact lt_of_lt_of_le h9 hlog

private theorem tail_eq_two_sub {q : ℕ} (hq : 3 ≤ q) : tail q = 2 - beta q := by
  have hn := order_ge_nine hq
  have hb : 0 < beta q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot (q^2) (by omega))
  have hm : Real.exp (nu q * sigma q) = beta q ^ (q^2) := by
    have h := Real.exp_nat_mul (Real.log (beta q)) (q^2)
    rw [Nat.cast_pow, Real.exp_log hb] at h
    exact h
  unfold tail
  rw [neg_mul, Real.exp_neg, hm, ← inv_pow]
  exact (two_sub_dbonacciPerronRoot_eq_inv_pow (q^2) (by omega)).symm

private theorem gaussian_sigma {q : ℕ} (hq : 3 ≤ q) :
    gaussian q (sigma q) = 2 := by
  have hn := order_ge_nine hq
  have hb : 0 < beta q :=
    lt_trans zero_lt_one (one_lt_dbonacciPerronRoot (q^2) (by omega))
  change Real.exp (sigma q) + tail q = 2
  rw [sigma, Real.exp_log hb, tail_eq_two_sub hq]
  ring

private theorem hasDerivAt_gaussian (q : ℕ) (s : ℝ) :
    HasDerivAt (gaussian q) (Real.exp s - nu q * Real.exp (-nu q * s)) s := by
  have hlinear : HasDerivAt (fun x : ℝ => -nu q * x) (-nu q) s :=
    hasDerivAt_const_mul (x := s) (-nu q)
  convert (Real.hasDerivAt_exp s).add hlinear.exp using 1 <;>
    (try funext x) <;> (try simp only [gaussian, Pi.add_apply]) <;> ring

private theorem gaussian_deriv_gt {q : ℕ} (hq : 3 ≤ q) {s : ℝ}
    (hs : (2 / 3 : ℝ) ≤ s) : (161 / 90 : ℝ) < deriv (gaussian q) s := by
  have hn := nu_ge_nine hq
  have ht := (real_rational_tail_on_ray hn hs).2.2
  have hmult : 0 ≤ (nu q * (nu q - 9)) * Real.exp (-nu q * s) :=
    mul_nonneg (mul_nonneg (by linarith only [hn]) (sub_nonneg.mpr hn))
      (Real.exp_pos _).le
  have hsmall : nu q * Real.exp (-nu q * s) < (1 / 10 : ℝ) := by
    nlinarith only [ht, hmult]
  have he := Real.sum_le_exp_of_nonneg (x := s)
    (by linarith only [hs] : 0 ≤ s) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hpoly : (17 / 9 : ℝ) ≤ 1 + s + s^2 / 2 := by
    nlinarith only [hs, sq_nonneg (s - 2 / 3)]
  rw [(hasDerivAt_gaussian q s).deriv]
  linarith only [hsmall, he, hpoly]

private theorem gaussian_secant_strict {q : ℕ} (hq : 3 ≤ q) {a b : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hab : a < b) :
    (161 / 90 : ℝ) * (b - a) < gaussian q b - gaussian q a := by
  have hd : Differentiable ℝ (gaussian q) :=
    fun s => (hasDerivAt_gaussian q s).differentiableAt
  exact (convex_Ici (2 / 3 : ℝ)).mul_sub_lt_image_sub_of_lt_deriv
    hd.continuous.continuousOn hd.differentiableOn
    (fun s hs => gaussian_deriv_gt hq (interior_subset hs))
    a ha b (ha.trans hab.le) hab

private theorem gaussian_secant {q : ℕ} (hq : 3 ≤ q) {a b : ℝ}
    (ha : (2 / 3 : ℝ) ≤ a) (hab : a ≤ b) :
    (161 / 90 : ℝ) * (b - a) ≤ gaussian q b - gaussian q a ∧
      (a < b → (161 / 90 : ℝ) * (b - a) < gaussian q b - gaussian q a) := by
  refine ⟨?_, fun h => gaussian_secant_strict hq ha h⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · exact (gaussian_secant_strict hq ha hlt).le

private theorem gaussian_root_iff {q : ℕ} (hq : 3 ≤ q) {s : ℝ}
    (hs : (2 / 3 : ℝ) ≤ s) : gaussian q s = 2 ↔ s = sigma q := by
  have hroot := gaussian_sigma hq
  have hσ := sigma_gt_two_thirds hq
  constructor
  · intro h
    rcases lt_trichotomy s (sigma q) with hlt | heq | hgt
    · have hsec := gaussian_secant_strict hq hs hlt
      rw [hroot, h] at hsec
      have hp : 0 < (161 / 90 : ℝ) * (sigma q - s) :=
        mul_pos (by norm_num) (sub_pos.mpr hlt)
      linarith only [hsec, hp]
    · exact heq
    · have hsec := gaussian_secant_strict hq hσ.le hgt
      rw [hroot, h] at hsec
      have hp : 0 < (161 / 90 : ℝ) * (s - sigma q) :=
        mul_pos (by norm_num) (sub_pos.mpr hgt)
      linarith only [hsec, hp]
  · rintro rfl
    exact hroot

private theorem nu_tendsto : Tendsto nu atTop atTop := by
  exact (tendsto_pow_atTop (α := ℝ) (by decide : 2 ≠ 0)).comp
    tendsto_natCast_atTop_atTop

private theorem beta_tendsto : Tendsto beta atTop (nhds 2) := by
  exact dbonacciPerronRoot_tendsto_two.comp
    (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0))

private theorem sigma_tendsto : Tendsto sigma atTop (nhds (Real.log 2)) :=
  beta_tendsto.log (by norm_num)

private theorem tail_moments_tendsto :
    Tendsto (fun q : ℕ => nu q ^ 2 * tail q) atTop (nhds 0) ∧
      Tendsto (fun q : ℕ => nu q * tail q) atTop (nhds 0) := by
  have hi : Tendsto (fun q : ℕ => (nu q)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp nu_tendsto
  have hi6 : Tendsto (fun q : ℕ => (nu q + 6)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (6 : ℝ) nu_tendsto)
  have hr : Tendsto (fun q : ℕ => 243 / (2 * nu q * (nu q + 6)))
      atTop (nhds 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (243 / 2 : ℝ))
      atTop (nhds (243 / 2))).mul hi).mul hi6
    simpa only [div_eq_mul_inv, mul_inv_rev, mul_zero, zero_mul,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hm2 : Tendsto (fun q : ℕ => nu q ^ 2 * tail q) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun q : ℕ => 243 / (2 * nu q * (nu q + 6)))
    · filter_upwards [eventually_ge_atTop 3] with q hq
      exact (real_rational_tail_on_ray (nu_ge_nine hq)
        (sigma_gt_two_thirds hq).le).1.le
    · filter_upwards [eventually_ge_atTop 3] with q hq
      exact (real_rational_tail_on_ray (nu_ge_nine hq)
        (sigma_gt_two_thirds hq).le).2.1.le
    · exact hr
  refine ⟨hm2, ?_⟩
  apply squeeze_zero' (g := fun q : ℕ => nu q ^ 2 * tail q)
  · filter_upwards [eventually_ge_atTop 3] with q hq
    exact mul_nonneg (by linarith [nu_ge_nine hq]) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 3] with q hq
    have hn : 0 ≤ nu q * (nu q - 1) :=
      mul_nonneg (by linarith [nu_ge_nine hq]) (by linarith [nu_ge_nine hq])
    have h := mul_nonneg hn (show 0 ≤ tail q from (Real.exp_pos _).le)
    nlinarith only [h]
  · exact hm2

private theorem order_ratio_tendsto :
    Tendsto (fun q : ℕ => (nu q + 1) / (nu q - 1)) atTop (nhds 1) := by
  have hn : Tendsto (fun q : ℕ => nu q - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) nu_tendsto
  have hi : Tendsto (fun q : ℕ => (nu q - 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hn
  have h : Tendsto (fun q : ℕ => 1 + 2 * (nu q - 1)⁻¹) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (nhds 1)).add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (nhds 2)).mul hi)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hn0 : nu q - 1 ≠ 0 := by linarith [nu_ge_nine hq]
  field_simp [hn0] <;> ring

private theorem coefficient_factorization {q : ℕ} (hq : 3 ≤ q) :
    (q : ℝ) * coefficient q = (sigma q / 6) * ((nu q + 1) / (nu q - 1)) *
      ((beta q - nu q ^ 2 * tail q) / (beta q - nu q * tail q)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hn0 : nu q - 1 ≠ 0 := by linarith [nu_ge_nine hq]
  have hden : ((q : ℝ)^2 + 1) * beta q - 2 * (q : ℝ)^2 =
      beta q - nu q * tail q := by rw [tail_eq_two_sub hq]; dsimp [nu]; ring
  have hnum : ((q : ℝ)^4 + 1) * beta q - 2 * (q : ℝ)^4 =
      beta q - nu q ^ 2 * tail q := by rw [tail_eq_two_sub hq]; dsimp [nu]; ring
  unfold coefficient
  rw [hnum, hden]
  have hpref : (q : ℝ) *
      (((q : ℝ)^2 + 1) * sigma q / (6 * (q : ℝ) * ((q : ℝ)^2 - 1))) =
      (sigma q / 6) * ((nu q + 1) / (nu q - 1)) := by
    dsimp [nu] at hn0 ⊢
    field_simp [hq0, hn0]
  rw [← mul_assoc, hpref]

private theorem coefficient_limits :
    Tendsto (fun q : ℕ => (q : ℝ) * coefficient q) atTop (nhds (Real.log 2 / 6)) ∧
      Tendsto (fun q : ℕ => (q : ℝ) * correction q) atTop
        (nhds (Real.log 2 / 6 - 1 / 2)) := by
  have hm := tail_moments_tendsto
  have hratio : Tendsto
      (fun q : ℕ => (beta q - nu q ^ 2 * tail q) / (beta q - nu q * tail q))
      atTop (nhds 1) := by
    have h := (beta_tendsto.sub hm.1).div (beta_tendsto.sub hm.2) (by norm_num)
    convert h using 1 <;> norm_num
  have hprod : Tendsto
      (fun q : ℕ => (sigma q / 6) * ((nu q + 1) / (nu q - 1)) *
        ((beta q - nu q ^ 2 * tail q) / (beta q - nu q * tail q)))
      atTop (nhds (Real.log 2 / 6)) := by
    simpa using ((sigma_tendsto.div_const 6).mul order_ratio_tendsto).mul hratio
  have hd : Tendsto (fun q : ℕ => (q : ℝ) * coefficient q)
      atTop (nhds (Real.log 2 / 6)) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 3] with q hq
    exact (coefficient_factorization hq).symm
  refine ⟨hd, ?_⟩
  have hb := hd.sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)))
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 3] with q hq
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  dsimp [correction]
  field_simp [hq0] <;> ring

/-- One uniform profile theorem, with total coefficients and the full natural limit domain. -/
theorem square_displacement_profile :
    let beta : ℕ → ℝ := fun q => dbonacciPerronRoot (q^2)
    let sigma : ℕ → ℝ := fun q => Real.log (beta q)
    let G : ℕ → ℝ → ℝ := fun q s => Real.exp s + Real.exp (-(q : ℝ)^2 * s)
    let d : ℕ → ℝ := fun q =>
      (((q : ℝ)^2 + 1) * sigma q / (6 * (q : ℝ) * ((q : ℝ)^2 - 1))) *
        ((((q : ℝ)^4 + 1) * beta q - 2 * (q : ℝ)^4) /
          (((q : ℝ)^2 + 1) * beta q - 2 * (q : ℝ)^2))
    let b : ℕ → ℝ := fun q => d q - 1 / (2 * (q : ℝ))
    (∀ (q : ℕ), 3 ≤ q → ∀ (s : ℝ), (2 / 3 : ℝ) ≤ s →
      (161 / 90 : ℝ) < deriv (G q) s) ∧
    (∀ (q : ℕ), 3 ≤ q → ∀ (a b : ℝ), (2 / 3 : ℝ) ≤ a → a ≤ b →
      (161 / 90 : ℝ) * (b - a) ≤ G q b - G q a ∧
        (a < b → (161 / 90 : ℝ) * (b - a) < G q b - G q a)) ∧
    (∀ (q : ℕ), 3 ≤ q → ∀ (s : ℝ), (2 / 3 : ℝ) ≤ s →
      (G q s = 2 ↔ s = sigma q)) ∧
    Tendsto (fun q : ℕ => (q : ℝ) * d q) atTop (nhds (Real.log 2 / 6)) ∧
    Tendsto (fun q : ℕ => (q : ℝ) * b q) atTop (nhds (Real.log 2 / 6 - 1 / 2)) := by
  change
    (∀ q : ℕ, 3 ≤ q → ∀ s : ℝ, (2 / 3 : ℝ) ≤ s →
      (161 / 90 : ℝ) < deriv (gaussian q) s) ∧
    (∀ q : ℕ, 3 ≤ q → ∀ a b : ℝ, (2 / 3 : ℝ) ≤ a → a ≤ b →
      (161 / 90 : ℝ) * (b - a) ≤ gaussian q b - gaussian q a ∧
        (a < b → (161 / 90 : ℝ) * (b - a) < gaussian q b - gaussian q a)) ∧
    (∀ q : ℕ, 3 ≤ q → ∀ s : ℝ, (2 / 3 : ℝ) ≤ s →
      (gaussian q s = 2 ↔ s = sigma q)) ∧
    Tendsto (fun q : ℕ => (q : ℝ) * coefficient q) atTop (nhds (Real.log 2 / 6)) ∧
    Tendsto (fun q : ℕ => (q : ℝ) * correction q) atTop (nhds (Real.log 2 / 6 - 1 / 2))
  exact ⟨fun _ hq _ hs => gaussian_deriv_gt hq hs,
    fun _ hq _ _ ha hab => gaussian_secant hq ha hab,
    fun _ hq _ hs => gaussian_root_iff hq hs,
    coefficient_limits.1, coefficient_limits.2⟩

end D5.S3.FiniteGroups.BajnokBeattySquareDisplacementProfile

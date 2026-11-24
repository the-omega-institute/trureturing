/- GID: D5/S3/CharacterSums/DirichletTriangleBound
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletTriangleBound
   mirror-E: none(waiver:conditional-finite-height-estimate)
   anchors: []
   utility: none
   digest: Finite-height exclusion controls triangular Dirichlet character sums. -/

import D5.S3.CharacterSums.DirichletCompletion
import D5.S3.CharacterSums.DirichletTriangleExplicit
import D5.S3.Analytic.Resolvent.PoissonKernelTail

/-! The strict high tail is complementary to the closed low-height region. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory
open scoped BigOperators ComplexConjugate
open D5.S3.Analytic.Resolvent.PoissonKernelTail
open D5.S3.CharacterSums.DirichletCompletion
open D5.S3.CharacterSums.DirichletTrianglePerron
open D5.S3.CharacterSums.DirichletTriangleExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit

namespace D5.S3.CharacterSums.DirichletTriangleBound

private theorem windowMass_lower : (11 / 4 : ℝ) < 2 * Real.arctan 8 := by
  linarith [windowMass_gt, Real.pi_gt_three]

private theorem log_lower {x : ℝ} (hx : 10000 ≤ x) : 9 ≤ Real.log x := by
  have hh : Real.log (10000 : ℝ) = 4 * Real.log 10 := by
    rw [show (10000 : ℝ) = 10 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 10000) hx
  rw [hh, Real.log_ten_eq] at hl
  linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]

private theorem root_lower {x : ℝ} (hx : 10000 ≤ x) : 100 ≤ Real.sqrt x := by
  exact (Real.le_sqrt (by norm_num) (by linarith)).mpr (by norm_num; exact hx)

private theorem tail_budget {x : ℝ} (hx : 10000 ≤ x) :
    tailBound x (4 * Real.sqrt x) ≤
      (10 / (99 * Real.sqrt x)) * (17 / 9 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hr := root_lower hx
  have hr0 : 0 < Real.sqrt x := by positivity
  have hL := log_lower hx
  have hmass := windowMass_lower
  have hmass0 : 0 < 2 * Real.arctan 8 := by linarith
  have hT : 0 < 4 * Real.sqrt x - 32 := by linarith
  have h13 : 0 < 4 * Real.sqrt x - 13 := by linarith
  have hlog : Real.log (x * (4 * Real.sqrt x - 13)) + 2 ≤
      17 / 9 * Real.log x := by
    have hcomp := Real.log_le_log (mul_pos hx0 h13)
      (mul_le_mul_of_nonneg_left (show 4 * Real.sqrt x - 13 ≤ 4 * Real.sqrt x by
        linarith) hx0.le)
    rw [Real.log_mul hx0.ne' (by positivity : 4 * Real.sqrt x ≠ 0),
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hr0.ne', Real.log_sqrt hx0.le,
      Real.log_four_eq] at hcomp
    linarith [Real.log_two_lt_d9]
  have hden : 99 / 10 * Real.sqrt x ≤
      (2 * Real.arctan 8) * (4 * Real.sqrt x - 32) := by
    have h1 : 18 / 5 * Real.sqrt x ≤ 4 * Real.sqrt x - 32 := by linarith
    have h2 := mul_le_mul hmass.le h1 (by positivity : 0 ≤ 18 / 5 * Real.sqrt x)
      hmass0.le
    nlinarith
  have hnum : 0 ≤ 17 / 9 * Real.log x := by positivity
  unfold tailBound
  rw [ite_eq_right hx0.ne']
  calc
    _ = (Real.log (x * (4 * Real.sqrt x - 13)) + 2) /
        ((2 * Real.arctan 8) * (4 * Real.sqrt x - 32)) := by field_simp
    _ ≤ (17 / 9 * Real.log x) /
        ((2 * Real.arctan 8) * (4 * Real.sqrt x - 32)) :=
      div_le_div_of_nonneg_right hlog (mul_nonneg hmass0.le hT.le)
    _ ≤ (17 / 9 * Real.log x) / (99 / 10 * Real.sqrt x) :=
      div_le_div_of_nonneg_left hnum (by positivity) hden
    _ = _ := by ring

private theorem numerical_budget {x : ℝ} (hx : 10000 ≤ x) :
    (2 * Real.sqrt x + 4 + 2 / x) * ((Real.log (3 * x) + 1) / 2) +
      (x + 2 + 3 / x) * tailBound x (4 * Real.sqrt x) + Real.log x + 1 ≤
        (165458 / 111375 : ℝ) * Real.sqrt x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hr := root_lower hx
  have hr0 : 0 < Real.sqrt x := by positivity
  have hL := log_lower hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have hsq := Real.sq_sqrt hx0.le
  have hinv : 1 / x ≤ 1 / 10000 :=
    one_div_le_one_div_of_le (by norm_num) hx
  have ha : Real.sqrt x + 2 + 1 / x ≤ 103 / 100 * Real.sqrt x := by linarith
  have hb : Real.log (3 * x) + 1 ≤ 56 / 45 * Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith [Real.log_three_lt_d9]
  have hfirst : (2 * Real.sqrt x + 4 + 2 / x) *
      ((Real.log (3 * x) + 1) / 2) ≤
      (103 / 100 * (56 / 45)) * Real.sqrt x * Real.log x := by
    calc
      _ = (Real.sqrt x + 2 + 1 / x) * (Real.log (3 * x) + 1) := by ring
      _ ≤ (Real.sqrt x + 2 + 1 / x) * (56 / 45 * Real.log x) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (103 / 100 * Real.sqrt x) * (56 / 45 * Real.log x) :=
        mul_le_mul_of_nonneg_right ha (by positivity)
      _ = _ := by ring
  have hinv3 : 3 / x ≤ 3 / 10000 := by
    convert mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 3) using 1 <;> ring
  have hc : x + 2 + 3 / x ≤ 101 / 100 * x := by linarith
  have hsecond : (x + 2 + 3 / x) * tailBound x (4 * Real.sqrt x) ≤
      (101 / 100 * (10 / 99) * (17 / 9)) * Real.sqrt x * Real.log x := by
    calc
      _ ≤ (x + 2 + 3 / x) *
          ((10 / (99 * Real.sqrt x)) * (17 / 9 * Real.log x)) :=
        mul_le_mul_of_nonneg_left (tail_budget hx) (by positivity)
      _ ≤ (101 / 100 * x) *
          ((10 / (99 * Real.sqrt x)) * (17 / 9 * Real.log x)) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp; nlinarith [hsq]
  have hthird : Real.log x + 1 ≤ 1 / 90 * Real.sqrt x * Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hr hL0
    nlinarith
  have he : (103 / 100 : ℝ) * (56 / 45) +
      101 / 100 * (10 / 99) * (17 / 9) + 1 / 90 = 165458 / 111375 := by norm_num
  nlinarith

private theorem completion_standard_envelope {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (logDeriv (completion χ) (2 + t * I)).re ≤
      (Real.log ((q : ℝ) * (|t| + 3)) + 1) / 2 := by
  classical
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hp : Real.log 3 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_three
  have hs : (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) < 1 :=
    DirichletCompletionGamma.logarithmic_series_bound.2.1.trans_lt
      DirichletCompletionGamma.logarithmic_series_bound.2.2
  have hi : 0 ≤ (1 / ((2 + (t : ℂ) * I) + (if χ.Even then 0 else 1))).re := by
    split_ifs <;> rw [one_div, Complex.inv_re] <;>
      exact div_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hb := (completion_vertical_bound χ t).1
  rw [Real.log_mul hq.ne' (by positivity : |t| + 3 ≠ 0)]
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem completion_zero_LFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {ρ : ℂ}
    (hρ : completion χ ρ = 0) : χ.LFunction ρ = 0 := by
  have hp := (completion_zero_strip hχ hρ).1
  have hc : χ.completedLFunction ρ = 0 := by
    exact (mul_eq_zero.mp hρ).resolve_left (Complex.exp_ne_zero _)
  rw [χ.LFunction_eq_completed_div_gammaFactor ρ (.inl (by
    intro he; simp [he] at hp)), hc, zero_div]

private theorem low_zero_on_line {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) {T : ℝ}
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0)
    {ρ : ℂ} (hρ : completion χ ρ = 0) (hT : |ρ.im| ≤ T) : ρ.re = 1 / 2 := by
  have hright : ρ.re ≤ 1 / 2 := by
    by_contra! hh
    exact hfree ρ hh hT (completion_zero_LFunction hχ hρ)
  have hleft : 1 / 2 ≤ ρ.re := by
    by_contra! hh
    have hr : completion χ (1 - conj ρ) = 0 := by
      rw [completion_reflect hχ, hρ, map_zero, mul_zero]
    have hf := hfree (1 - conj ρ) (by simp; linarith) (by simpa using hT)
    exact hf (completion_zero_LFunction hχ hr)
  exact le_antisymm hright hleft

private theorem actual_reciprocal_tail {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 32 < T) :
    Summable (fun ρ : {z : ℂ // completion χ z = 0} =>
      if T < |ρ.1.im| then
        (analyticOrderNatAt (completion χ) ρ.1 : ℝ) / ρ.1.im ^ 2 else 0) ∧
      (∑' ρ : {z : ℂ // completion χ z = 0},
        if T < |ρ.1.im| then
          (analyticOrderNatAt (completion χ) ρ.1 : ℝ) / ρ.1.im ^ 2 else 0) ≤
          tailBound q T := by
  let Z := {z : ℂ // completion χ z = 0}
  let u := fun ρ : Z => 2 - ρ.1.re
  let g := fun ρ : Z => ρ.1.im
  let w := fun ρ : Z => (analyticOrderNatAt (completion χ) ρ.1 : ℝ)
  have hu (ρ : Z) : 0 < u ρ ∧ u ρ ≤ 2 := by
    have hs := completion_zero_strip hχ ρ.2
    dsimp [u]
    constructor <;> linarith
  have hnonneg (ρ : Z) (t : ℝ) : 0 ≤ w ρ * kernel (u ρ) (g ρ) t := by
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hu ρ).1.le (by positivity))
  have hfinite (t : ℝ) (J : Finset Z) :
      (∑ ρ ∈ J, w ρ * kernel (u ρ) (g ρ) t) ≤
        (Real.log ((q : ℝ) * (|t| + 3)) + 1) / 2 := by
    have hs := completion_vertical_resolvent hχ hne 2 t (by norm_num)
    have he : HasSum (fun ρ : Z => w ρ * kernel (u ρ) (g ρ) t)
        (logDeriv (completion χ) (2 + t * I)).re := by
      simpa [w, u, g, kernel, cauchyKernel, mul_div_assoc] using hs
    exact (he.summable.sum_le_tsum J (fun ρ _ => hnonneg ρ t)).trans
      (he.tsum_eq.trans_le (completion_standard_envelope χ t))
  have hb := reciprocalSquare_tail_bound u g q T w
    (fun ρ _ => Nat.cast_nonneg _) (fun ρ _ _ => (hu ρ).1.le) hT (by
      intro s hs t ht J _
      have ht0 : 0 ≤ t := by linarith
      have he : |s * t| = t := by
        rcases hs with rfl | rfl <;> simp [abs_of_nonneg ht0]
      simpa only [he] using hfinite (s * t) J)
  have ho := hb.2.2.2.2 (fun ρ _ _ => hu ρ)
  exact ⟨ho.2.1, ho.2.2.1⟩

private theorem low_denominators {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / (‖ρ‖ * ‖ρ + 1‖) ≤ 3 / (9 / 4 + ρ.im ^ 2) ∧
      ‖2 - ρ‖ = ‖ρ + 1‖ ∧ ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
  have h0 : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hρ]
    ring
  have h1 : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, add_zero, hρ]
    ring
  have hn0 : 0 < ‖ρ‖ := by nlinarith [norm_nonneg ρ, sq_nonneg ρ.im]
  have hn1 : 0 < ‖ρ + 1‖ := by nlinarith [norm_nonneg (ρ + 1), sq_nonneg ρ.im]
  have hc : ‖ρ + 1‖ ≤ 3 * ‖ρ‖ := by nlinarith [sq_nonneg ρ.im]
  refine ⟨?_, ?_, h1⟩
  · apply (div_le_div_iff₀ (mul_pos hn0 hn1) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hc hn1.le
    nlinarith
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.one_re, Complex.one_im, zero_sub, add_zero, hρ]
    ring

private theorem low_kernel_norm {ρ : ℂ} {x : ℝ} (hx : 0 < x)
    (hρ : ρ.re = 1 / 2) :
    ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) +
      3 / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ ≤
        (2 * Real.sqrt x + 4 + 2 / x) *
          ((3 / 2) / (9 / 4 + ρ.im ^ 2)) := by
  have hd := low_denominators hρ
  have hD : 0 < 9 / 4 + ρ.im ^ 2 := by positivity
  have hn : ‖(x : ℂ) ^ ρ‖ = Real.sqrt x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hρ, Real.sqrt_eq_rpow]
  have hfirst : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ ≤
      Real.sqrt x * (3 / (9 / 4 + ρ.im ^ 2)) := by
    rw [norm_div, norm_mul, hn, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hd.1 (Real.sqrt_nonneg _)
  have hsecond : ‖(2 : ℂ) / (ρ * (2 - ρ))‖ ≤
      6 / (9 / 4 + ρ.im ^ 2) := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, hd.2.1]
    have hh := mul_le_mul_of_nonneg_left hd.1 (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1 <;> ring
  have hthird : ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ =
      3 / (x * (9 / 4 + ρ.im ^ 2)) := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx, hd.2.1,
      show x * ‖ρ + 1‖ * ‖ρ + 1‖ = x * ‖ρ + 1‖ ^ 2 by ring, hd.2.2]
  calc
    _ ≤ ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))‖ +
        ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ := norm_add_le _ _
    _ ≤ (‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ +
        ‖(2 : ℂ) / (ρ * (2 - ρ))‖) +
        ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ Real.sqrt x * (3 / (9 / 4 + ρ.im ^ 2)) +
        6 / (9 / 4 + ρ.im ^ 2) + 3 / (x * (9 / 4 + ρ.im ^ 2)) := by
      rw [hthird]
      linarith
    _ = _ := by field_simp; ring

private theorem high_kernel_norm {ρ : ℂ} {x : ℝ} (hx : 1 ≤ x)
    (hρ : ρ.re ≤ 1) (hγ : 0 < |ρ.im|) :
    ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ)) +
      3 / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ ≤
        (x + 2 + 3 / x) / ρ.im ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hγ2 : 0 < ρ.im ^ 2 := by nlinarith [sq_abs ρ.im]
  have hn0 := Complex.abs_im_le_norm ρ
  have hn1 : |ρ.im| ≤ ‖ρ + 1‖ := by
    simpa using Complex.abs_im_le_norm (ρ + 1)
  have hn2 : |ρ.im| ≤ ‖2 - ρ‖ := by
    simpa using Complex.abs_im_le_norm (2 - ρ)
  have habs : |ρ.im| * |ρ.im| = ρ.im ^ 2 := by rw [← sq, sq_abs]
  have hd01 : ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ + 1‖ := by
    simpa only [habs] using mul_le_mul hn0 hn1 (abs_nonneg _) (norm_nonneg _)
  have hd02 : ρ.im ^ 2 ≤ ‖ρ‖ * ‖2 - ρ‖ := by
    simpa only [habs] using mul_le_mul hn0 hn2 (abs_nonneg _) (norm_nonneg _)
  have hd12 : ρ.im ^ 2 ≤ ‖ρ + 1‖ * ‖2 - ρ‖ := by
    simpa only [habs] using mul_le_mul hn1 hn2 (abs_nonneg _) (norm_nonneg _)
  have hn : ‖(x : ℂ) ^ ρ‖ ≤ x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    simpa using Real.rpow_le_rpow_of_exponent_le hx hρ
  have hfirst : ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ ≤ x / ρ.im ^ 2 := by
    rw [norm_div, norm_mul]
    exact (div_le_div_of_nonneg_right hn (by positivity)).trans
      (div_le_div_of_nonneg_left hx0.le hγ2 hd01)
  have hsecond : ‖(2 : ℂ) / (ρ * (2 - ρ))‖ ≤ 2 / ρ.im ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) hγ2 hd02
  have hthird : ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ ≤
      (3 / x) / ρ.im ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx0]
    calc
      _ = (3 / x) / (‖ρ + 1‖ * ‖2 - ρ‖) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hγ2 hd12
  calc
    _ ≤ ‖(x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 2 / (ρ * (2 - ρ))‖ +
        ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ := norm_add_le _ _
    _ ≤ (‖(x : ℂ) ^ ρ / (ρ * (ρ + 1))‖ +
        ‖(2 : ℂ) / (ρ * (2 - ρ))‖) +
        ‖(3 : ℂ) / ((x : ℂ) * (ρ + 1) * (2 - ρ))‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ x / ρ.im ^ 2 + 2 / ρ.im ^ 2 + (3 / x) / ρ.im ^ 2 := by linarith
    _ = _ := by ring

private theorem zero_sum_bound {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {x T : ℝ} (hx : 1 ≤ x) (hT : 32 < T)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) :
    ‖∑' ρ : {z : ℂ // completion χ z = 0},
      (analyticOrderNatAt (completion χ) ρ.1 : ℂ) *
        ((x : ℂ) ^ ρ.1 / (ρ.1 * (ρ.1 + 1)) - 2 / (ρ.1 * (2 - ρ.1)) +
          3 / ((x : ℂ) * (ρ.1 + 1) * (2 - ρ.1)))‖ ≤
      (2 * Real.sqrt x + 4 + 2 / x) * (logDeriv (completion χ) 2).re +
        (x + 2 + 3 / x) * tailBound q T := by
  classical
  let Z := {z : ℂ // completion χ z = 0}
  let w := fun ρ : Z => (analyticOrderNatAt (completion χ) ρ.1 : ℝ)
  let P := fun ρ : Z => w ρ * (2 - ρ.1.re) /
    ((2 - ρ.1.re) ^ 2 + ρ.1.im ^ 2)
  let H := fun ρ : Z => if T < |ρ.1.im| then w ρ / ρ.1.im ^ 2 else 0
  let A := 2 * Real.sqrt x + 4 + 2 / x
  let B := x + 2 + 3 / x
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hP : HasSum P (logDeriv (completion χ) 2).re := by
    simpa [P, w] using completion_vertical_resolvent hχ hne 2 0 (by norm_num)
  have hH := actual_reciprocal_tail hχ hne hT
  have hsum : HasSum (fun ρ : Z => A * P ρ + B * H ρ)
      (A * (logDeriv (completion χ) 2).re + B * ∑' ρ : Z, H ρ) :=
    (hP.mul_left A).add (hH.1.hasSum.mul_left B)
  have hPn (ρ : Z) : 0 ≤ P ρ := by
    have hr := completion_zero_strip hχ ρ.2
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
  have hmajor (ρ : Z) :
      ‖(analyticOrderNatAt (completion χ) ρ.1 : ℂ) *
        ((x : ℂ) ^ ρ.1 / (ρ.1 * (ρ.1 + 1)) - 2 / (ρ.1 * (2 - ρ.1)) +
          3 / ((x : ℂ) * (ρ.1 + 1) * (2 - ρ.1)))‖ ≤ A * P ρ + B * H ρ := by
    rw [norm_mul, Complex.norm_natCast]
    by_cases hh : T < |ρ.1.im|
    · have hb := high_kernel_norm hx (completion_zero_strip hχ ρ.2).2.le
        (by linarith : 0 < |ρ.1.im|)
      have hw := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg
        (α := ℝ) (analyticOrderNatAt (completion χ) ρ.1))
      have he : (analyticOrderNatAt (completion χ) ρ.1 : ℝ) *
          ((x + 2 + 3 / x) / ρ.1.im ^ 2) = B * H ρ := by
        simp only [H, ite_eq_left hh, w, B]
        ring
      rw [he] at hw
      exact hw.trans (le_add_of_nonneg_left (mul_nonneg (by dsimp [A]; positivity) (hPn ρ)))
    · have hl := low_zero_on_line hχ hfree ρ.2 (le_of_not_gt hh)
      have hb := low_kernel_norm hx0 hl
      have hw := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg
        (α := ℝ) (analyticOrderNatAt (completion χ) ρ.1))
      have he : (analyticOrderNatAt (completion χ) ρ.1 : ℝ) *
          ((2 * Real.sqrt x + 4 + 2 / x) * ((3 / 2) / (9 / 4 + ρ.1.im ^ 2))) =
          A * P ρ + B * H ρ := by
        simp only [A, P, H, ite_eq_right hh, mul_zero, add_zero, w, hl]
        ring
      exact he ▸ hw
  have ht : B * (∑' ρ : Z, H ρ) ≤ B * tailBound q T :=
    mul_le_mul_of_nonneg_left hH.2 (show 0 ≤ B by dsimp [B]; positivity)
  exact (tsum_of_norm_bounded hsum hmajor).trans (by linarith)

private theorem parityCorrection_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 3 ≤ x) : ‖parityCorrection χ x‖ ≤ Real.log x := by
  classical
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL : 1 ≤ Real.log x := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx
    linarith [Real.log_three_gt_d9]
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h21 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  by_cases heven : χ.Even
  · have hTn := evenT_nonneg (Real.log x)
    have hTm := (evenT_le_mass (Real.log_nonneg hx1)).2.2
    have hquot : (1 - Real.log 2) / x ≤ 1 - Real.log 2 :=
      div_le_self (by linarith) hx1
    have hquotn : 0 ≤ (1 - Real.log 2) / x := div_nonneg (by linarith) hx0.le
    have hq : (Real.log 2 - 1) / x = -((1 - Real.log 2) / x) := by ring
    simp only [parityCorrection, ite_eq_left heven, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> rw [hq] <;> linarith
  · have hTn := trivialT_nonneg (Real.log_nonneg hx1)
    have hTm := trivialT_le_mass (Real.log_nonneg hx1)
    have hll := Real.log_le_sub_one_of_pos hx0
    have hquot : 0 ≤ (Real.log x + 2 - Real.log 2 - trivialT (Real.log x)) / x :=
      div_nonneg (by linarith) hx0.le
    have hqu : (Real.log x + 2 - Real.log 2 - trivialT (Real.log x)) / x ≤ 2 := by
      apply (div_le_iff₀ hx0).mpr
      linarith
    have he : -1 + (Real.log x + 2 - Real.log 2) / x - trivialT (Real.log x) / x =
        -1 + (Real.log x + 2 - Real.log 2 - trivialT (Real.log x)) / x := by ring
    simp only [parityCorrection, ite_eq_right heven, Complex.norm_real, Real.norm_eq_abs, he]
    exact (abs_le.mpr ⟨by linarith, by linarith⟩ :
      |(-1 : ℝ) + (Real.log x + 2 - Real.log 2 - trivialT (Real.log x)) / x| ≤ 1).trans hL

/-- Finite-height exclusion gives a quantitative bound retaining the actual endpoint terms. -/
theorem characterTriangle_finite_height {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {x T : ℝ} (hx : 1 ≤ x) (hT : 32 < T)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) :
    ‖characterTriangle χ x‖ ≤
      (2 * Real.sqrt x + 4 + 2 / x) * (logDeriv (completion χ) 2).re +
        (x + 2 + 3 / x) * tailBound q T +
          (1 - 1 / x) * ‖logDeriv χ.LFunction 2‖ + ‖parityCorrection χ x‖ := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hz := zero_sum_bound hχ hne hx hT hfree
  change ‖zeroTriangle χ x‖ ≤ _ at hz
  have hinv : 1 / x ≤ 1 := (div_le_one hx0).mpr hx
  have hscalar : ‖(1 : ℂ) - (x : ℂ)⁻¹‖ = 1 - 1 / x := by
    have he : (1 : ℂ) - (x : ℂ)⁻¹ = ((1 - 1 / x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [(characterTriangle_explicit hχ hne hx).2]
  calc
    _ ≤ ‖-zeroTriangle χ x - (1 - (x : ℂ)⁻¹) * logDeriv χ.LFunction 2‖ +
        ‖parityCorrection χ x‖ := norm_add_le _ _
    _ ≤ ‖zeroTriangle χ x‖ +
        (1 - 1 / x) * ‖logDeriv χ.LFunction 2‖ + ‖parityCorrection χ x‖ := by
      have hh := norm_sub_le (-zeroTriangle χ x)
        ((1 - (x : ℂ)⁻¹) * logDeriv χ.LFunction 2)
      simp only [norm_neg, norm_mul, hscalar] at hh
      linarith
    _ ≤ _ := by linarith

/-- The explicit rational budget is strictly smaller than the three-halves coefficient. -/
theorem characterTriangle_prime_bound (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) (hp : 10000 ≤ p)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    ‖characterTriangle χ p‖ ≤
      (165458 / 111375 : ℝ) * Real.sqrt p * Real.log p := by
  have hpR : (10000 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp3 : (3 : ℝ) ≤ p := by linarith
  have hprim : χ.IsPrimitive := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd χ.conductor
      χ.conductor_dvd_level with hc | hc
    · exact (hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)).elim
    · exact hc
  have hT : 32 < 4 * Real.sqrt (p : ℝ) := by linarith [root_lower hpR]
  have hb := characterTriangle_finite_height hprim hne (by linarith : (1 : ℝ) ≤ p) hT hfree
  have hP : (logDeriv (completion χ) 2).re ≤
      (Real.log (3 * (p : ℝ)) + 1) / 2 := by
    simpa [mul_comm] using completion_standard_envelope χ 0
  have hL : ‖logDeriv χ.LFunction 2‖ ≤ 1 := by
    have hh := (norm_logDeriv_LFunction_two χ 0).trans
      (DirichletCompletionGamma.logarithmic_series_bound.2.1.trans
        DirichletCompletionGamma.logarithmic_series_bound.2.2.le)
    simpa using hh
  have hinv : 0 ≤ 1 - 1 / (p : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hp0).mpr (by linarith)
  have hcoef : 1 - 1 / (p : ℝ) ≤ 1 := by
    have hh : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hpar := parityCorrection_norm χ hp3
  have hendpoint : (1 - 1 / (p : ℝ)) * ‖logDeriv χ.LFunction 2‖ +
      ‖parityCorrection χ p‖ ≤ Real.log p + 1 := by
    have hh := mul_le_mul_of_nonneg_left hL hinv
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hP
    (show 0 ≤ 2 * Real.sqrt (p : ℝ) + 4 + 2 / (p : ℝ) by positivity)
  calc
    _ ≤ (2 * Real.sqrt (p : ℝ) + 4 + 2 / (p : ℝ)) *
        ((Real.log (3 * (p : ℝ)) + 1) / 2) +
        ((p : ℝ) + 2 + 3 / (p : ℝ)) * tailBound p (4 * Real.sqrt p) +
          Real.log p + 1 := by linarith
    _ ≤ _ := numerical_budget hpR

#print axioms characterTriangle_finite_height
#print axioms characterTriangle_prime_bound

end D5.S3.CharacterSums.DirichletTriangleBound

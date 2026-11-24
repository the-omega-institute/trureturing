/- GID: D5/S3/CharacterSums/DirichletTriangleBound
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletTriangleBound
   mirror-E: none(waiver:conditional-finite-height-estimate)
   anchors: []
   utility: none
   digest: Finite-height exclusion controls triangular Dirichlet character sums. -/

import D5.S3.CharacterSums.DirichletCompletion
import D5.S3.Analytic.Resolvent.PoissonKernelTail

/-! The strict high tail is complementary to the closed low-height region. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory
open scoped BigOperators ComplexConjugate
open D5.S3.Analytic.Resolvent.PoissonKernelTail
open D5.S3.CharacterSums.DirichletCompletion

namespace D5.S3.CharacterSums.DirichletTriangleBound

private theorem windowMass_lower : (11 / 4 : ℝ) < 2 * Real.arctan 8 := by
  have hi := Real.arctan_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 8)
  norm_num only [one_div, inv_inv] at hi
  have hb := Real.arctan_lt_self (by norm_num : (0 : ℝ) < 1 / 8)
  linarith [Real.pi_gt_three]

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
  rw [if_neg hx0.ne']
  calc
    _ = (Real.log (x * (4 * Real.sqrt x - 13)) + 2) /
        ((2 * Real.arctan 8) * (4 * Real.sqrt x - 32)) := by ring
    _ ≤ (17 / 9 * Real.log x) /
        ((2 * Real.arctan 8) * (4 * Real.sqrt x - 32)) :=
      div_le_div_of_nonneg_right hlog (mul_nonneg hmass0.le hT.le)
    _ ≤ (17 / 9 * Real.log x) / (99 / 10 * Real.sqrt x) :=
      div_le_div_of_nonneg_left hnum (by positivity) hden
    _ = _ := by ring

private theorem numerical_budget {x : ℝ} (hx : 10000 ≤ x) :
    (2 * Real.sqrt x + 4 + 2 / x) * ((Real.log (3 * x) + 1) / 2) +
      (x + 2 + 3 / x) * tailBound x (4 * Real.sqrt x) + Real.log x + 3 ≤
        (331411 / 222750 : ℝ) * Real.sqrt x * Real.log x := by
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
      _ ≤ (103 / 100 * Real.sqrt x) * (56 / 45 * Real.log x) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := by ring
  have hc : x + 2 + 3 / x ≤ 101 / 100 * x := by linarith
  have hsecond : (x + 2 + 3 / x) * tailBound x (4 * Real.sqrt x) ≤
      (101 / 100 * (10 / 99) * (17 / 9)) * Real.sqrt x * Real.log x := by
    calc
      _ ≤ (101 / 100 * x) *
          ((10 / (99 * Real.sqrt x)) * (17 / 9 * Real.log x)) :=
        mul_le_mul hc (tail_budget hx) (by positivity) (by positivity)
      _ = _ := by field_simp; nlinarith [hsq]
  have hthird : Real.log x + 3 ≤ 1 / 75 * Real.sqrt x * Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hr hL0
    nlinarith
  have he : (103 / 100 : ℝ) * (56 / 45) +
      101 / 100 * (10 / 99) * (17 / 9) + 1 / 75 = 331411 / 222750 := by norm_num
  nlinarith

private theorem completion_standard_envelope {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (logDeriv (completion χ) (2 + t * I)).re ≤
      (Real.log ((q : ℝ) * (|t| + 3)) + 1) / 2 := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hp : Real.log 3 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_three
  have hs : (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) < 1 :=
    DirichletCompletionGamma.logarithmic_series_bound.2.1.trans_lt
      DirichletCompletionGamma.logarithmic_series_bound.2.2
  have hi : 0 ≤ (1 / ((2 + (t : ℂ) * I) + (if χ.Even then 0 else 1))).re := by
    split_ifs <;> simp [Complex.div_re, Complex.normSq_apply] <;> positivity
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
      simpa only [w, u, g, kernel, cauchyKernel, mul_div_assoc] using hs
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

end D5.S3.CharacterSums.DirichletTriangleBound

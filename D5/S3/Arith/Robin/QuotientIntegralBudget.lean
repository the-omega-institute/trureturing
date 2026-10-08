/- GID: D5/S3/Arith/Robin/QuotientIntegralBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/QuotientIntegralBudget
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Actual quotient residual blocks have explicit absolute integral and strict logarithmic tail budgets. -/

import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import D5.S3.Arith.Robin.MellinWeightedVariation

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)

namespace D5.S3.Arith.Robin.QuotientIntegralBudget

def arithmeticPrefix (k : ℕ → ℝ) (y : ℝ) : ℝ := ∑ i ∈ Finset.range ⌊y⌋₊, k (i + 1)

def mainTerm (A D y : ℝ) : ℝ := A * (y * Real.log y) - D * y

def residual (k : ℕ → ℝ) (A D y : ℝ) : ℝ := arithmeticPrefix k y - mainTerm A D y

def weightEnvelope (x : ℝ) : ℝ := (1 + Real.log x) / (Real.log x) ^ 2

def block (k : ℕ → ℝ) (A D : ℝ) (m : ℕ) (t : ℝ) : ℝ := residual k A D (t / m) - residual k A D (t / (m + 1))

def blockIntegral (k : ℕ → ℝ) (A D x : ℝ) (m : ℕ) : ℝ := ∫ t in Ioi x, |block k A D m t| * weight t

structure KernelData where
  k : ℕ → ℝ
  C : ℝ
  mu : ℝ
  A : ℝ
  D : ℝ
  C_nonneg : 0 ≤ C
  mu_nonneg : 0 ≤ mu
  coefficient_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ k n
  coefficient_le : ∀ n : ℕ, 1 ≤ n → k n ≤ C * Real.log n
  residual_high : ∀ y : ℝ, 1 ≤ y →
    |residual k A D y| ≤ mu * (1 + Real.log y)

def quadratic (d : KernelData) : ℝ := d.C + |d.A|

def linear (d : KernelData) : ℝ := d.C + 2 * |d.A| * (1 + Real.log 2) + 2 * |d.D| + 2 * d.mu

def constant (d : KernelData) : ℝ := 4 * d.mu

def firstConstant (d : KernelData) : ℝ := d.mu * (3 + 2 * Real.log 2) + |d.D| + |d.A| * Real.log 2

def envelope (d : KernelData) (x : ℝ) (m : ℕ) : ℝ := weightEnvelope x / (m : ℝ) ^ 2 * (quadratic d * (Real.log m) ^ 2 + linear d * Real.log m +
    constant d)

private theorem coefficient_one (d : KernelData) : d.k 1 = 0 := by
  apply le_antisymm
  · simpa using d.coefficient_le 1 (by omega)
  · exact d.coefficient_nonneg 1 (by omega)
private theorem measurable_prefix (k : ℕ → ℝ) : Measurable (arithmeticPrefix k) := by
  exact (measurable_of_countable (fun N : ℕ => ∑ i ∈ Finset.range N, k (i + 1))).comp Nat.measurable_floor
private theorem prefix_nonneg (k : ℕ → ℝ) (hk : ∀ n : ℕ, 1 ≤ n → 0 ≤ k n) (y : ℝ) : 0 ≤ arithmeticPrefix k y := by
  unfold arithmeticPrefix
  exact Finset.sum_nonneg fun i _ => hk (i + 1) (Nat.succ_pos i)
private theorem prefix_monotone (k : ℕ → ℝ) (hk : ∀ n : ℕ, 1 ≤ n → 0 ≤ k n) : Monotone (arithmeticPrefix k) := by
  intro y z hyz
  unfold arithmeticPrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.floor_mono hyz)) (fun i _ _ => hk (i + 1) (Nat.succ_pos i))
private theorem prefix_as_finite_sum (k : ℕ → ℝ) {N : ℕ} {y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) : arithmeticPrefix k y = ∑ i ∈ Finset.range N, if ((i
    + 1 : ℕ) : ℝ) ≤ y then k (i + 1) else 0 := by
  have hfloor : ⌊y⌋₊ ≤ N := by
    simpa using Nat.floor_mono hyN
  unfold arithmeticPrefix
  calc
    (∑ i ∈ Finset.range ⌊y⌋₊, k (i + 1)) = ∑ i ∈ Finset.range ⌊y⌋₊, if ((i + 1 : ℕ) : ℝ) ≤ y then k (i + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i + 1 ≤ ⌊y⌋₊ := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
      simp only [if_pos ((Nat.le_floor_iff hy).mp hi')]
    _ = ∑ i ∈ Finset.range N,
          if ((i + 1 : ℕ) : ℝ) ≤ y then k (i + 1) else 0 := by
      apply Finset.sum_subset (Finset.range_mono hfloor)
      intro i _ hi
      have hnot : ¬ ((i + 1 : ℕ) : ℝ) ≤ y := by
        intro h
        have h' : i + 1 ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).mpr h
        exact hi (Finset.mem_range.mpr (Nat.lt_of_succ_le h'))
      simp only [if_neg hnot]

private theorem prefix_difference_finite (k : ℕ → ℝ) {N : ℕ} {c y : ℝ} (hy : 0 ≤ y) (hcy : 0 ≤ c * y) (hcyle : c * y ≤ y) (hyN : y ≤ N) :
    arithmeticPrefix k y - arithmeticPrefix k (c * y) = ∑ i ∈ Finset.range N, if c * y < ((i + 1 : ℕ) : ℝ) ∧ ((i + 1 : ℕ) : ℝ) ≤ y then k (i + 1)
    else 0 := by
  rw [prefix_as_finite_sum k hy hyN, prefix_as_finite_sum k hcy (hcyle.trans hyN), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ((i + 1 : ℕ) : ℝ) ≤ c * y
  · have hy' : ((i + 1 : ℕ) : ℝ) ≤ y := h.trans hcyle
    simp only [h, hy', not_lt.mpr h, true_and, false_and, ite_true, ite_false, sub_self]
  · simp only [h, lt_of_not_ge h, true_and, ite_false, sub_zero]
private theorem jump_fiber {c y d : ℝ} (hc : 0 < c) : (c * y < d ∧ d ≤ y) ↔ y ∈ Ico d (d / c) := by
  constructor
  · rintro ⟨hcy, hdy⟩
    exact ⟨hdy, (lt_div_iff₀ hc).mpr (by simpa [mul_comm] using hcy)⟩
  · rintro ⟨hdy, hyc⟩
    exact ⟨by simpa [mul_comm] using (lt_div_iff₀ hc).mp hyc, hdy⟩
private theorem log_weighted_prefix_le (k : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hk : ∀ n : ℕ, 1 ≤ n → k n ≤ C * Real.log n) {N : ℕ} (hN : 1 ≤ N) : (∑ n
    ∈ Finset.Icc 1 N, k n / (n : ℝ)) ≤ C * Real.log N * (1 + Real.log N) := by
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNreal
  have hHarm : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹) ≤ 1 + Real.log N := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log N
  calc
    (∑ n ∈ Finset.Icc 1 N, k n / (n : ℝ)) ≤ ∑ n ∈ Finset.Icc 1 N, (C * Real.log N) / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hlog : Real.log n ≤ Real.log N := Real.log_le_log hnpos (by exact_mod_cast hnN)
      exact div_le_div_of_nonneg_right ((hk n hn1).trans (mul_le_mul_of_nonneg_left hlog hC)) hnpos.le
    _ = C * Real.log N * ∑ n ∈ Finset.Icc 1 N, (n : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp [div_eq_mul_inv]
    _ ≤ C * Real.log N * (1 + Real.log N) := mul_le_mul_of_nonneg_left hHarm (mul_nonneg hC hlogN)
private theorem residual_high_difference (d : KernelData) {m y : ℝ} (hm : 2 ≤ m) (hym : m ≤ y) : |residual d.k d.A d.D y - residual d.k d.A d.D
    (m / (m + 1) * y)| ≤ 2 * d.mu * (1 + Real.log y) := by
  have hmpos : 0 < m := by linarith
  have hden : 0 < m + 1 := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hcy1 : 1 ≤ m / (m + 1) * y := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    have hmy : m * m ≤ m * y := mul_le_mul_of_nonneg_left hym hmpos.le
    nlinarith [sq_nonneg (m - 2)]
  have hc : m / (m + 1) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
  have hcyle : m / (m + 1) * y ≤ y := by
    calc
      m / (m + 1) * y ≤ 1 * y := mul_le_mul_of_nonneg_right hc (by linarith)
      _ = y := one_mul y
  have hlog : Real.log (m / (m + 1) * y) ≤ Real.log y := Real.log_le_log (lt_of_lt_of_le zero_lt_one hcy1) hcyle
  calc
    |residual d.k d.A d.D y -
        residual d.k d.A d.D (m / (m + 1) * y)| ≤
        |residual d.k d.A d.D y| + |residual d.k d.A d.D (m / (m + 1) * y)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (residual d.k d.A d.D y)
          (-residual d.k d.A d.D (m / (m + 1) * y))
    _ ≤ d.mu * (1 + Real.log y) + d.mu * (1 + Real.log (m / (m + 1) * y)) := add_le_add (d.residual_high y hy1) (d.residual_high _ hcy1)
    _ ≤ d.mu * (1 + Real.log y) + d.mu * (1 + Real.log y) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) d.mu_nonneg)
    _ = 2 * d.mu * (1 + Real.log y) := by ring
private theorem weightEnvelope_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ weightEnvelope x := by
  unfold weightEnvelope
  have := Real.log_pos hx
  positivity

private theorem weight_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ weight t := by
  unfold weight
  have := Real.log_pos ht
  positivity
private theorem weight_le {x t : ℝ} (hx : 1 < x) (hxt : x ≤ t) : weight t ≤ weightEnvelope x / t ^ 2 := by
  have hxlog : 0 < Real.log x := Real.log_pos hx
  have htlog : 0 < Real.log t := Real.log_pos (hx.trans_le hxt)
  have hlog : Real.log x ≤ Real.log t := Real.log_le_log (by linarith) hxt
  have hW : (1 + Real.log t) / (Real.log t) ^ 2 ≤ (1 + Real.log x) / (Real.log x) ^ 2 := by
    calc
      (1 + Real.log t) / (Real.log t) ^ 2 = 1 / Real.log t + 1 / (Real.log t) ^ 2 := by
        field_simp [ne_of_gt htlog]
        <;> ring
      _ ≤ 1 / Real.log x + 1 / (Real.log x) ^ 2 := by gcongr
      _ = (1 + Real.log x) / (Real.log x) ^ 2 := by
        field_simp [ne_of_gt hxlog]
        <;> ring
  calc
    weight t = ((1 + Real.log t) / (Real.log t) ^ 2) / t ^ 2 := by
      simp only [weight, div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ weightEnvelope x / t ^ 2 := div_le_div_of_nonneg_right hW (sq_nonneg t)
private def logMoment (rho t : ℝ) : ℝ := t⁻¹ * (Real.log t) ^ (-rho)
private def natLogMoment (j : ℕ) (t : ℝ) : ℝ := 1 / (t * (Real.log t) ^ j)
private theorem natLogMoment_eq (j : ℕ) (t : ℝ) : natLogMoment j t = logMoment j t := by
  simp [natLogMoment, logMoment, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div, mul_inv_rev, mul_comm]

private theorem integrableOn_logMoment {rho a : ℝ} (hrho : 1 < rho) (ha : 1 < a) : IntegrableOn (logMoment rho) (Ioi a) := by
  change IntegrableOn (fun t : ℝ => t⁻¹ • ((Real.log t) ^ (-rho))) (Ioi a)
  exact (integrableOn_comp_log_Ioi (fun u : ℝ => u ^ (-rho)) (a := a) (by linarith)).mpr
      (integrableOn_Ioi_rpow_of_lt (a := -rho) (c := Real.log a)
        (by linarith) (Real.log_pos ha))
private theorem integral_logMoment {rho a : ℝ} (hrho : 1 < rho) (ha : 1 < a) : (∫ t in Ioi a, logMoment rho t) = (Real.log a) ^ (1 - rho) / (rho
    - 1) := by
  change (∫ t in Ioi a, t⁻¹ • ((Real.log t) ^ (-rho))) = _
  rw [integral_comp_log_Ioi (fun u : ℝ => u ^ (-rho)) (by linarith),
    integral_Ioi_rpow_of_lt (by linarith) (Real.log_pos ha)]
  rw [show (-rho + 1 : ℝ) = 1 - rho by ring]
  have hden : rho - 1 ≠ 0 := by linarith
  have hden' : 1 - rho ≠ 0 := by linarith
  field_simp
  <;> ring
private theorem integrableOn_natLogMoment {j : ℕ} (hj : 2 ≤ j) {a : ℝ} (ha : 1 < a) : IntegrableOn (natLogMoment j) (Ioi a) := by
  have hjreal : 1 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hj)
  have heq : natLogMoment j = logMoment (j : ℝ) := by
    funext t
    exact natLogMoment_eq j t
  rw [heq]
  exact integrableOn_logMoment hjreal ha
private theorem antitoneOn_natLogMoment (j : ℕ) {a : ℝ} (ha : 1 < a) : AntitoneOn (natLogMoment j) (Ici a) := by
  intro u hu v hv huv
  have hu1 : 1 < u := ha.trans_le hu
  have hv1 : 1 < v := ha.trans_le hv
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hulog : 0 < Real.log u := Real.log_pos hu1
  have hvlog : 0 < Real.log v := Real.log_pos hv1
  have hlog : Real.log u ≤ Real.log v := Real.log_le_log hu0 huv
  unfold natLogMoment
  apply one_div_le_one_div_of_le (by positivity)
  gcongr
private theorem summable_natLogMoment {j : ℕ} (hj : 2 ≤ j) : Summable (fun n : ℕ => natLogMoment j n) := by
  exact AntitoneOn.summable_of_integrableOn_Ioi (N := 2) (antitoneOn_natLogMoment j (by norm_num : (1 : ℝ) < 2))
      (integrableOn_natLogMoment hj (by norm_num))
      (by
        intro t ht
        change (2 : ℝ) < t at ht
        unfold natLogMoment
        have htpos : 0 < t := by linarith
        have hlog := Real.log_pos (by linarith : 1 < t)
        positivity)

private theorem logarithmic_product_le {B W a2 a1 a0 M L H q : ℝ} (hB : 0 ≤ B) (hM : 0 < M) (hL : 0 < L) (hq : 0 ≤ q) (hH : |H| ≤ B * M / L ^ 4)
    (hbound : q ≤ W / M ^ 2 * (a2 * L ^ 2 + a1 * L + a0)) : |H| * q ≤ B * W * (a2 / (M * L ^ 2) + a1 / (M * L ^ 3) + a0 / (M * L ^ 4)) := by
  calc
    |H| * q ≤ (B * M / L ^ 4) * (W / M ^ 2 * (a2 * L ^ 2 + a1 * L + a0)) := mul_le_mul hH hbound hq (by positivity)
    _ = _ := by
      field_simp
      <;> ring
private theorem summable_logarithmic_consumer (H q : ℕ → ℝ) {B W a2 a1 a0 : ℝ} (hB : 0 ≤ B) (hq : ∀ m : ℕ, 2 ≤ m → 0 ≤ q m) (hH : ∀ m : ℕ, 2 ≤ m
    → |H m| ≤ B * (m : ℝ) / (Real.log m) ^ 4) (hQ : ∀ m : ℕ, 2 ≤ m → q m ≤ W / (m : ℝ) ^ 2 * (a2 * (Real.log m) ^ 2 + a1 * Real.log m + a0)) :
    Summable (fun n : ℕ => |H (n + 2)| * q (n + 2)) := by
  have hs (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => natLogMoment j (n + 2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).mpr (summable_natLogMoment hj)
  have hmajor : Summable (fun n : ℕ => B * W * (a2 * natLogMoment 2 (n + 2) + a1 * natLogMoment 3 (n + 2) + a0 * natLogMoment 4 (n + 2))) := by
    exact ((((hs 2 (by omega)).mul_left a2).add
      ((hs 3 (by omega)).mul_left a1)).add
        ((hs 4 (by omega)).mul_left a0)).mul_left (B * W)
  apply hmajor.of_nonneg_of_le
  · intro n
    exact mul_nonneg (abs_nonneg _) (hq (n + 2) (by omega))
  · intro n
    have hm : 2 ≤ n + 2 := by omega
    have hm1 : 1 < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
    simpa [natLogMoment, div_eq_mul_inv, mul_assoc, Nat.cast_add] using logarithmic_product_le hB (by exact_mod_cast (by omega : 0 < n + 2))
        (Real.log_pos hm1)
        (hq _ hm) (hH _ hm) (hQ _ hm)

private theorem integrableOn_inv_sq_Icc {a b : ℝ} (ha : 0 < a) : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  intro y hy
  have hypos : 0 < y := ha.trans_le hy.1
  exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hypos.ne')).continuousWithinAt
private theorem integral_inv_sq_Ico {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (hc1 : c ≤ 1) : (∫ y in Ico d (d / c), 1 / y ^ 2) = (1 - c) / d := by
  have hdc : d ≤ d / c := by
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc1 hd.le
  have hint : IntervalIntegrable (fun y : ℝ => 1 / y ^ 2) volume d (d / c) := (intervalIntegrable_iff_integrableOn_Icc_of_le hdc).mpr
      (integrableOn_inv_sq_Icc hd)
  have hderiv : ∀ y ∈ uIcc d (d / c), HasDerivAt (fun z : ℝ => -z⁻¹) (1 / y ^ 2) y := by
    intro y hy
    rw [uIcc_of_le hdc] at hy
    have hypos : 0 < y := hd.trans_le hy.1
    simpa only [neg_one_mul, neg_neg, one_div] using (hasDerivAt_inv hypos.ne').const_mul (-1 : ℝ)
  have hFTC : (∫ y in d..d / c, 1 / y ^ 2) = -(d / c)⁻¹ - (-d⁻¹) := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdc, hFTC]
  field_simp [hd.ne', hc.ne']
  <;> ring
private theorem hasDerivAt_log_tail_primitive {y : ℝ} (hy : 0 < y) : HasDerivAt (fun z : ℝ => -(Real.log z + 2) / z) ((1 + Real.log y) / y ^ 2) y
    := by
  have h := (((Real.hasDerivAt_log hy.ne').add_const 2).neg.div (hasDerivAt_id y) hy.ne')
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq]
  field_simp [hy.ne']
  <;> ring

private theorem tendsto_log_tail_primitive : Tendsto (fun y : ℝ => -(Real.log y + 2) / y) atTop (𝓝 0) := by
  have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hconst : Tendsto (fun y : ℝ => 2 / y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).const_mul (2 : ℝ)
  simpa only [add_div, neg_div, add_zero, neg_zero] using (hlog.add hconst).neg
theorem integrableOn_log_tail {a : ℝ} (ha : 1 ≤ a) : IntegrableOn (fun y : ℝ => (1 + Real.log y) / y ^ 2) (Ioi a) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (fun y hy => hasDerivAt_log_tail_primitive (zero_lt_one.trans_le (ha.trans hy))) ?_
      tendsto_log_tail_primitive
  intro y hy
  exact div_nonneg (add_nonneg zero_le_one (Real.log_nonneg (ha.trans hy.le))) (sq_nonneg y)
theorem integral_log_tail {a : ℝ} (ha : 1 ≤ a) : (∫ y in Ioi a, (1 + Real.log y) / y ^ 2) = (Real.log a + 2) / a := by
  have hderiv : ∀ y ∈ Ici a, HasDerivAt (fun z : ℝ => -(Real.log z + 2) / z) ((1 + Real.log y) / y ^ 2) y := by
    intro y hy
    exact hasDerivAt_log_tail_primitive (zero_lt_one.trans_le (ha.trans hy))
  simpa only [zero_sub, neg_div, neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_log_tail ha)
      tendsto_log_tail_primitive
private theorem integrableOn_low_smooth (A D : ℝ) {m : ℝ} (hm : 1 ≤ m) : IntegrableOn (fun y : ℝ => (|A| * (1 + |Real.log y|) + |D|) / y) (Icc (1
    / m) m) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hminvpos : 0 < 1 / m := one_div_pos.mpr hmpos
  apply ContinuousOn.integrableOn_Icc
  intro y hy
  have hypos : 0 < y := hminvpos.trans_le hy.1
  have hlog : ContinuousAt Real.log y := Real.continuousAt_log hypos.ne'
  exact (((continuousAt_const.mul (continuousAt_const.add hlog.abs)).add continuousAt_const).div continuousAt_id hypos.ne').continuousWithinAt
private theorem integral_affine_log_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (P Q : ℝ) : (∫ y in a..b, (P + Q * Real.log y) / y) = P * (Real.log
    b - Real.log a) + (Q / 2) * ((Real.log b) ^ 2 - (Real.log a) ^ 2) := by
  have hcont : ContinuousOn (fun y : ℝ => (P + Q * Real.log y) / y) (Icc a b) := by
    intro y hy
    have hypos : 0 < y := ha.trans_le hy.1
    exact ((continuousAt_const.add (continuousAt_const.mul (Real.continuousAt_log hypos.ne'))).div continuousAt_id hypos.ne').continuousWithinAt
  have hint : IntervalIntegrable (fun y : ℝ => (P + Q * Real.log y) / y) volume a b := hcont.intervalIntegrable_of_Icc hab
  have hderiv : ∀ y ∈ uIcc a b, HasDerivAt (fun z : ℝ => P * Real.log z + (Q / 2) * (Real.log z) ^ 2) ((P + Q * Real.log y) / y) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hypos : 0 < y := ha.trans_le hy.1
    have h := ((Real.hasDerivAt_log hypos.ne').const_mul P).add (((Real.hasDerivAt_log hypos.ne').pow 2).const_mul (Q / 2))
    exact h.congr_deriv (by
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv]
      ring)
  calc
    (∫ y in a..b, (P + Q * Real.log y) / y) = (P * Real.log b + (Q / 2) * (Real.log b) ^ 2) - (P * Real.log a + (Q / 2) * (Real.log a) ^ 2) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = P * (Real.log b - Real.log a) + (Q / 2) * ((Real.log b) ^ 2 - (Real.log a) ^ 2) := by ring

private theorem integral_low_smooth (A D : ℝ) {m : ℝ} (hm : 1 ≤ m) : (∫ y in Icc (1 / m) m, (|A| * (1 + |Real.log y|) + |D|) / y) = |A| *
    (Real.log m) ^ 2 + 2 * (|A| + |D|) * Real.log m := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hminvpos : 0 < 1 / m := one_div_pos.mpr hmpos
  have hminv1 : 1 / m ≤ 1 := by
    exact (div_le_iff₀ hmpos).mpr (by simpa only [one_mul] using hm)
  have hminvm : 1 / m ≤ m := hminv1.trans hm
  have hloginv : Real.log (1 / m) = -Real.log m := by
    rw [one_div, Real.log_inv]
  let f : ℝ → ℝ := fun y => (|A| * (1 + |Real.log y|) + |D|) / y
  have hint : IntervalIntegrable f volume (1 / m) m := (intervalIntegrable_iff_integrableOn_Icc_of_le hminvm).mpr (integrableOn_low_smooth A D
      hm)
  have hleftint : IntervalIntegrable f volume (1 / m) 1 := by
    apply hint.mono_set
    rw [uIcc_of_le hminv1, uIcc_of_le hminvm]
    exact fun y hy => ⟨hy.1, hy.2.trans hm⟩
  have hrightint : IntervalIntegrable f volume 1 m := by
    apply hint.mono_set
    rw [uIcc_of_le hm, uIcc_of_le hminvm]
    exact fun y hy => ⟨hminv1.trans hy.1, hy.2⟩
  have hleft : (∫ y in (1 / m)..1, f y) = (|A| + |D|) * Real.log m + (|A| / 2) * (Real.log m) ^ 2 := by
    calc
      (∫ y in (1 / m)..1, f y) = ∫ y in (1 / m)..1, ((|A| + |D|) + (-|A|) * Real.log y) / y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hminv1] at hy
        have hypos : 0 < y := hminvpos.trans_le hy.1
        have hlog : Real.log y ≤ 0 := Real.log_nonpos hypos.le hy.2
        dsimp only [f]
        rw [abs_of_nonpos hlog]
        ring
      _ = (|A| + |D|) * Real.log m + (|A| / 2) * (Real.log m) ^ 2 := by
        rw [integral_affine_log_div hminvpos hminv1 (|A| + |D|) (-|A|)]
        simp only [Real.log_one, hloginv]
        ring
  have hright : (∫ y in (1 : ℝ)..m, f y) = (|A| + |D|) * Real.log m + (|A| / 2) * (Real.log m) ^ 2 := by
    calc
      (∫ y in (1 : ℝ)..m, f y) = ∫ y in (1 : ℝ)..m, ((|A| + |D|) + |A| * Real.log y) / y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hm] at hy
        dsimp only [f]
        rw [abs_of_nonneg (Real.log_nonneg hy.1)]
        ring
      _ = (|A| + |D|) * Real.log m + (|A| / 2) * (Real.log m) ^ 2 := by
        rw [integral_affine_log_div zero_lt_one hm (|A| + |D|) |A|]
        simp only [Real.log_one]
        ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hminvm]
  change (∫ y in (1 / m)..m, f y) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftint hrightint, hleft, hright]
  ring
private theorem mainTerm_difference_le (A D : ℝ) {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : 0 < y) : |mainTerm A D y - mainTerm A D (c * y)| ≤ (1
    - c) * y * (|A| * (1 + |Real.log y|) + |D|) := by
  have hlogc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hclog : c * |Real.log c| ≤ 1 - c := by
    have hlog : Real.log (1 / c) ≤ 1 / c - 1 := Real.log_le_sub_one_of_pos (one_div_pos.mpr hc)
    have hloginv : Real.log (1 / c) = -Real.log c := by
      rw [one_div, Real.log_inv]
    rw [hloginv] at hlog
    rw [abs_of_nonpos hlogc]
    calc
      c * (-Real.log c) ≤ c * (1 / c - 1) := mul_le_mul_of_nonneg_left hlog hc.le
      _ = 1 - c := by
        field_simp [hc.ne']
        <;> ring
  have hdiff : mainTerm A D y - mainTerm A D (c * y) = (1 - c) * y * (A * Real.log y - D) - A * c * y * Real.log c := by
    simp only [mainTerm, Real.log_mul hc.ne' hy.ne']
    ring
  have hinner : |A * Real.log y - D| ≤ |A| * |Real.log y| + |D| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_mul] using abs_add_le (A * Real.log y) (-D)
  have hscale : 0 ≤ (1 - c) * y := mul_nonneg (sub_nonneg.mpr hc1) hy.le
  have hAscale : 0 ≤ |A| * y := mul_nonneg (abs_nonneg A) hy.le
  rw [hdiff]
  calc
    |(1 - c) * y * (A * Real.log y - D) - A * c * y * Real.log c| ≤
        |(1 - c) * y * (A * Real.log y - D)| + |A * c * y * Real.log c| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((1 - c) * y * (A * Real.log y - D))
          (-(A * c * y * Real.log c))
    _ = (1 - c) * y * |A * Real.log y - D| + |A| * y * (c * |Real.log c|) := by
      simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1), abs_of_pos hy, abs_of_pos hc]
      ring
    _ ≤ (1 - c) * y * (|A| * |Real.log y| + |D|) + |A| * y * (1 - c) := add_le_add (mul_le_mul_of_nonneg_left hinner hscale)
        (mul_le_mul_of_nonneg_left hclog hAscale)
    _ = (1 - c) * y * (|A| * (1 + |Real.log y|) + |D|) := by ring

private def quotientRatio (m : ℕ) : ℝ := (m : ℝ) / ((m : ℝ) + 1)
private def normalizedKernel (d : KernelData) (m : ℕ) (y : ℝ) : ℝ := |residual d.k d.A d.D y - residual d.k d.A d.D (quotientRatio m * y)| / y ^
    2
private def jumpTerm (k : ℕ → ℝ) (i : ℕ) (c y : ℝ) : ℝ := (Ico ((i + 1 : ℕ) : ℝ) (((i + 1 : ℕ) : ℝ) / c)).indicator (fun y => k (i + 1) / y ^ 2)
    y

private def jumpEnvelope (k : ℕ → ℝ) (N : ℕ) (c y : ℝ) : ℝ := ∑ i ∈ Finset.range N, jumpTerm k i c y
private def smoothDensity (A D y : ℝ) : ℝ := (|A| * (1 + |Real.log y|) + |D|) / y
theorem measurable_residual (k : ℕ → ℝ) (A D : ℝ) : Measurable (residual k A D) := by
  exact (measurable_prefix k).sub (by unfold mainTerm; fun_prop)
private theorem measurable_normalizedKernel (d : KernelData) (m : ℕ) : Measurable (normalizedKernel d m) := by
  unfold normalizedKernel
  have hdiff : Measurable (fun y : ℝ => residual d.k d.A d.D y - residual d.k d.A d.D (quotientRatio m * y)) := (measurable_residual d.k d.A
      d.D).sub ((measurable_residual d.k d.A d.D).comp (measurable_const.mul measurable_id))
  have habs : Measurable (fun y : ℝ => |residual d.k d.A d.D y - residual d.k d.A d.D (quotientRatio m * y)|) := by
    simpa only [Real.norm_eq_abs] using hdiff.norm
  exact habs.div (by fun_prop)
private theorem normalizedKernel_nonneg (d : KernelData) (m : ℕ) (y : ℝ) : 0 ≤ normalizedKernel d m y := div_nonneg (abs_nonneg _) (sq_nonneg _)

private theorem quotientRatio_pos {m : ℕ} (hm : 1 ≤ m) : 0 < quotientRatio m := by
  unfold quotientRatio
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  positivity
private theorem quotientRatio_le_one (m : ℕ) : quotientRatio m ≤ 1 := by
  unfold quotientRatio
  exact (div_le_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr (by linarith)
private theorem one_sub_quotientRatio (m : ℕ) : 1 - quotientRatio m = 1 / ((m : ℝ) + 1) := by
  unfold quotientRatio
  field_simp
  <;> ring
private theorem jumpTerm_nonneg (d : KernelData) (i : ℕ) (c y : ℝ) : 0 ≤ jumpTerm d.k i c y := by
  unfold jumpTerm
  by_cases hy : y ∈ Ico ((i + 1 : ℕ) : ℝ) (((i + 1 : ℕ) : ℝ) / c)
  · simp only [indicator_of_mem hy]
    exact div_nonneg (d.coefficient_nonneg _ (by omega)) (sq_nonneg _)
  · simp only [indicator_of_notMem hy, le_refl]
private theorem jumpEnvelope_nonneg (d : KernelData) (N : ℕ) (c y : ℝ) : 0 ≤ jumpEnvelope d.k N c y := by
  exact Finset.sum_nonneg fun i _ => jumpTerm_nonneg d i c y

private theorem integrable_jumpTerm (k : ℕ → ℝ) (i : ℕ) {c : ℝ} (hc : 0 < c) : Integrable (jumpTerm k i c) := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  have hi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
  have hbase := (integrableOn_inv_sq_Icc (b := ((i + 1 : ℕ) : ℝ) / c) hi).mono_set Ico_subset_Icc_self
  simpa only [IntegrableOn, div_eq_mul_inv, one_mul] using hbase.const_mul (k (i + 1))
private theorem integral_jumpTerm (k : ℕ → ℝ) (i : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : (∫ y, jumpTerm k i c y) = (1 - c) * (k (i + 1) / ((i +
    1 : ℕ) : ℝ)) := by
  simp only [jumpTerm]
  rw [integral_indicator measurableSet_Ico]
  simp_rw [div_eq_mul_inv]
  rw [integral_const_mul]
  have hi : 0 < ((i + 1 : ℕ) : ℝ) := by positivity
  have heval := integral_inv_sq_Ico hi hc hc1
  simp only [div_eq_mul_inv, one_mul] at heval
  rw [heval]
  ring
private theorem integrable_jumpEnvelope (k : ℕ → ℝ) (N : ℕ) {c : ℝ} (hc : 0 < c) : Integrable (jumpEnvelope k N c) := by
  exact integrable_finsetSum (Finset.range N) fun i _ => integrable_jumpTerm k i hc
private theorem integral_jumpEnvelope (k : ℕ → ℝ) (N : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : (∫ y, jumpEnvelope k N c y) = (1 - c) * ∑ n ∈
    Finset.Icc 1 N, k n / (n : ℝ) := by
  simp only [jumpEnvelope]
  rw [integral_finsetSum _ (fun i _ => integrable_jumpTerm k i hc)]
  simp_rw [integral_jumpTerm k _ hc hc1]
  rw [← Finset.mul_sum]
  congr 1
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hi; omega⟩
  · intro i hi j hj hij
    omega
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnN⟩
    exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl
private theorem low_prefix_density_eq (k : ℕ → ℝ) {N : ℕ} {c y : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hy : 0 ≤ y) (hyN : y ≤ N) : (arithmeticPrefix k y
    - arithmeticPrefix k (c * y)) / y ^ 2 = jumpEnvelope k N c y := by
  have hcy : 0 ≤ c * y := mul_nonneg hc.le hy
  have hcyle : c * y ≤ y := by nlinarith
  rw [prefix_difference_finite k hy hcy hcyle hyN, Finset.sum_div, jumpEnvelope]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : c * y < ((i + 1 : ℕ) : ℝ) ∧ ((i + 1 : ℕ) : ℝ) ≤ y
  · simp only [if_pos h, jumpTerm, indicator_of_mem ((jump_fiber hc).mp h)]
  · have hn : y ∉ Ico ((i + 1 : ℕ) : ℝ) (((i + 1 : ℕ) : ℝ) / c) := fun hy' => h ((jump_fiber hc).mpr hy')
    simp only [if_neg h, jumpTerm, indicator_of_notMem hn, zero_div]

private theorem low_normalizedKernel_le (d : KernelData) {m : ℕ} (hm : 2 ≤ m) {y : ℝ} (hy : y ∈ Icc (1 / (m : ℝ)) (m : ℝ)) : normalizedKernel d m
    y ≤ jumpEnvelope d.k m (quotientRatio m) y + (1 - quotientRatio m) * smoothDensity d.A d.D y := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hypos : 0 < y := lt_of_lt_of_le (one_div_pos.mpr hmpos) hy.1
  have hc := quotientRatio_pos (by omega : 1 ≤ m)
  have hc1 := quotientRatio_le_one m
  have hcyle : quotientRatio m * y ≤ y := by nlinarith
  have hprefix : 0 ≤ arithmeticPrefix d.k y - arithmeticPrefix d.k (quotientRatio m * y) := sub_nonneg.mpr (prefix_monotone d.k
      d.coefficient_nonneg hcyle)
  have habs :
      |residual d.k d.A d.D y - residual d.k d.A d.D (quotientRatio m * y)| ≤ (arithmeticPrefix d.k y - arithmeticPrefix d.k (quotientRatio m *
          y)) +
          |mainTerm d.A d.D y - mainTerm d.A d.D (quotientRatio m * y)| := by
    have heq : residual d.k d.A d.D y - residual d.k d.A d.D (quotientRatio m * y) = (arithmeticPrefix d.k y - arithmeticPrefix d.k
        (quotientRatio m * y)) - (mainTerm d.A d.D y - mainTerm d.A d.D (quotientRatio m * y)) := by
      unfold residual
      ring
    rw [heq]
    have h := abs_add_le (arithmeticPrefix d.k y - arithmeticPrefix d.k (quotientRatio m * y)) (-(mainTerm d.A d.D y - mainTerm d.A d.D
        (quotientRatio m * y)))
    rw [abs_neg, abs_of_nonneg hprefix] at h
    simpa only [sub_eq_add_neg] using h
  have hsmooth := mainTerm_difference_le d.A d.D hc hc1 hypos
  calc
    normalizedKernel d m y ≤ ((arithmeticPrefix d.k y - arithmeticPrefix d.k (quotientRatio m * y)) + (1 - quotientRatio m) * y * (|d.A| * (1 +
        |Real.log y|) + |d.D|)) / y ^ 2 := div_le_div_of_nonneg_right (habs.trans (add_le_add le_rfl hsmooth)) (sq_nonneg _)
    _ = jumpEnvelope d.k m (quotientRatio m) y + (1 - quotientRatio m) * smoothDensity d.A d.D y := by
      rw [add_div, low_prefix_density_eq d.k hc hc1 hypos.le hy.2]
      unfold smoothDensity
      field_simp [hypos.ne']
      <;> ring
private theorem normalizedKernel_low (d : KernelData) {m : ℕ} (hm : 2 ≤ m) : IntegrableOn (normalizedKernel d m) (Icc (1 / (m : ℝ)) (m : ℝ)) ∧ (∫
    y in Icc (1 / (m : ℝ)) (m : ℝ), normalizedKernel d m y) ≤ (1 - quotientRatio m) * ((d.C + |d.A|) * (Real.log m) ^ 2 + (d.C + 2 * |d.A| + 2 *
    |d.D|) * Real.log m) := by
  have hc := quotientRatio_pos (by omega : 1 ≤ m)
  have hc1 := quotientRatio_le_one m
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hJ := integrable_jumpEnvelope d.k m hc
  have hS : IntegrableOn (smoothDensity d.A d.D) (Icc (1 / (m : ℝ)) (m : ℝ)) := integrableOn_low_smooth d.A d.D hmreal
  have hmajor := hJ.integrableOn.add (hS.const_mul (1 - quotientRatio m))
  have hInt : IntegrableOn (normalizedKernel d m) (Icc (1 / (m : ℝ)) (m : ℝ)) := by
    apply hmajor.mono_nonneg (measurable_normalizedKernel d m).aestronglyMeasurable
    · exact ae_of_all _ (normalizedKernel_nonneg d m)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact low_normalizedKernel_le d hm hy
  refine ⟨hInt, ?_⟩
  calc
    (∫ y in Icc (1 / (m : ℝ)) (m : ℝ), normalizedKernel d m y) ≤ ∫ y in Icc (1 / (m : ℝ)) (m : ℝ), jumpEnvelope d.k m (quotientRatio m) y + (1 -
        quotientRatio m) * smoothDensity d.A d.D y := setIntegral_mono_on hInt hmajor measurableSet_Icc fun y hy => low_normalizedKernel_le d hm
        hy
    _ = (∫ y in Icc (1 / (m : ℝ)) (m : ℝ), jumpEnvelope d.k m (quotientRatio m) y) + (1 - quotientRatio m) * (|d.A| * (Real.log m) ^ 2 + 2 *
        (|d.A| + |d.D|) * Real.log m) := by
      rw [integral_add hJ.integrableOn (hS.const_mul _), integral_const_mul]
      rw [show (∫ y in Icc (1 / (m : ℝ)) (m : ℝ), smoothDensity d.A d.D y) = _ from integral_low_smooth d.A d.D hmreal]
    _ ≤ (1 - quotientRatio m) * (d.C * Real.log m * (1 + Real.log m)) + (1 - quotientRatio m) * (|d.A| * (Real.log m) ^ 2 + 2 * (|d.A| + |d.D|) *
        Real.log m) := by
      refine add_le_add ?_ le_rfl
      calc
        _ ≤ ∫ y, jumpEnvelope d.k m (quotientRatio m) y := setIntegral_le_integral hJ (ae_of_all _ (jumpEnvelope_nonneg d m _))
        _ = (1 - quotientRatio m) * ∑ n ∈ Finset.Icc 1 m, d.k n / (n : ℝ) := integral_jumpEnvelope d.k m hc hc1
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (log_weighted_prefix_le d.k d.C_nonneg d.coefficient_le (by omega))
          (sub_nonneg.mpr hc1)
    _ = _ := by ring
private theorem normalizedKernel_high (d : KernelData) {m : ℕ} (hm : 2 ≤ m) : IntegrableOn (normalizedKernel d m) (Ioi (m : ℝ)) ∧ (∫ y in Ioi (m
    : ℝ), normalizedKernel d m y) ≤ 2 * d.mu * (Real.log m + 2) / (m : ℝ) := by
  have hmreal : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  have htail := integrableOn_log_tail (by linarith : 1 ≤ (m : ℝ))
  have hmajor := htail.const_mul (2 * d.mu)
  have hpoint : ∀ y ∈ Ioi (m : ℝ), normalizedKernel d m y ≤ 2 * d.mu * ((1 + Real.log y) / y ^ 2) := by
    intro y hy
    have h := residual_high_difference d hmreal hy.le
    simpa [normalizedKernel, quotientRatio, mul_div_assoc] using div_le_div_of_nonneg_right h (sq_nonneg y)
  have hInt : IntegrableOn (normalizedKernel d m) (Ioi (m : ℝ)) := by
    apply hmajor.mono_nonneg (measurable_normalizedKernel d m).aestronglyMeasurable
    · exact ae_of_all _ (normalizedKernel_nonneg d m)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hpoint y hy
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ y in Ioi (m : ℝ), 2 * d.mu * ((1 + Real.log y) / y ^ 2) := setIntegral_mono_on hInt hmajor measurableSet_Ioi hpoint
    _ = _ := by rw [integral_const_mul, integral_log_tail (by linarith)]; ring
private def budgetPolynomial (d : KernelData) (m : ℕ) : ℝ := quadratic d * (Real.log m) ^ 2 + linear d * Real.log m + constant d
private theorem normalizedKernel_budget (d : KernelData) {m : ℕ} (hm : 2 ≤ m) : IntegrableOn (normalizedKernel d m) (Ioi (1 / (m : ℝ))) ∧ (∫ y in
    Ioi (1 / (m : ℝ)), normalizedKernel d m y) ≤ budgetPolynomial d m / (m : ℝ) := by
  obtain ⟨hLowInt, hLow⟩ := normalizedKernel_low d hm
  obtain ⟨hHighInt, hHigh⟩ := normalizedKernel_high d hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hC := d.C_nonneg
  have hL : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
  have hU := hLowInt.union hHighInt
  have hsub : Ioi (1 / (m : ℝ)) ⊆ Icc (1 / (m : ℝ)) (m : ℝ) ∪ Ioi (m : ℝ) := by
    intro y hy
    by_cases hym : y ≤ (m : ℝ)
    · exact Or.inl ⟨hy.le, hym⟩
    · exact Or.inr (lt_of_not_ge hym)
  refine ⟨hU.mono_set hsub, ?_⟩
  have hcoef : 1 - quotientRatio m ≤ 1 / (m : ℝ) := by
    rw [one_sub_quotientRatio]
    exact one_div_le_one_div_of_le hmpos (by linarith)
  have hbase : 0 ≤ (d.C + |d.A|) * (Real.log m) ^ 2 + (d.C + 2 * |d.A| + 2 * |d.D|) * Real.log m := by
    positivity
  have hbasepay : (1 - quotientRatio m) * ((d.C + |d.A|) * (Real.log m) ^ 2 + (d.C + 2 * |d.A| + 2 * |d.D|) * Real.log m) ≤ ((d.C + |d.A|) *
      (Real.log m) ^ 2 + (d.C + 2 * |d.A| + 2 * |d.D|) * Real.log m) / (m : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_right hcoef hbase
  calc
    _ ≤ ∫ y in Icc (1 / (m : ℝ)) (m : ℝ) ∪ Ioi (m : ℝ), normalizedKernel d m y := setIntegral_mono_set hU (ae_of_all _ (normalizedKernel_nonneg d
        m)) (ae_of_all _ hsub)
    _ = (∫ y in Icc (1 / (m : ℝ)) (m : ℝ), normalizedKernel d m y) + (∫ y in Ioi (m : ℝ), normalizedKernel d m y) := by
      apply setIntegral_union
      · exact disjoint_left.mpr fun y hy hz => not_lt_of_ge hy.2 hz
      · exact measurableSet_Ioi
      · exact hLowInt
      · exact hHighInt
    _ ≤ ((d.C + |d.A|) * (Real.log m) ^ 2 + (d.C + 2 * |d.A| + 2 * |d.D|) * Real.log m) / (m : ℝ) + 2 * d.mu * (Real.log m + 2) / (m : ℝ) :=
        add_le_add (hLow.trans hbasepay) hHigh
    _ ≤ budgetPolynomial d m / (m : ℝ) := by
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hmpos.le
      unfold budgetPolynomial quadratic linear constant
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hextra : 0 ≤ 2 * |d.A| * Real.log 2 * Real.log m := by positivity
      nlinarith

private theorem prefix_at_most_one (d : KernelData) {y : ℝ} (hy : y ≤ 1) : arithmeticPrefix d.k y = 0 := by
  apply le_antisymm
  · calc
      arithmeticPrefix d.k y ≤ arithmeticPrefix d.k 1 := prefix_monotone d.k d.coefficient_nonneg hy
      _ = 0 := by simp [arithmeticPrefix, coefficient_one d]
  · exact prefix_nonneg d.k d.coefficient_nonneg y
theorem residual_at_most_one (d : KernelData) {y : ℝ} (hy : y ≤ 1) : residual d.k d.A d.D y = d.D * y - d.A * (y * Real.log y) := by
  rw [residual, prefix_at_most_one d hy, mainTerm]
  ring
private theorem residual_difference_high (d : KernelData) {y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) : |residual d.k d.A d.D y - residual d.k d.A d.D
    z| ≤ 2 * d.mu * (1 + Real.log y) := by
  have hy : 1 ≤ y := hz.trans hzy
  have hlog : Real.log z ≤ Real.log y := Real.log_le_log (lt_of_lt_of_le zero_lt_one hz) hzy
  calc
    _ ≤ |residual d.k d.A d.D y| + |residual d.k d.A d.D z| := by
      simpa [sub_eq_add_neg] using abs_add_le (residual d.k d.A d.D y) (-residual d.k d.A d.D z)
    _ ≤ d.mu * (1 + Real.log y) + d.mu * (1 + Real.log z) := add_le_add (d.residual_high y hy) (d.residual_high z hz)
    _ ≤ d.mu * (1 + Real.log y) + d.mu * (1 + Real.log y) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log z ≤ 1 +
        Real.log y) d.mu_nonneg)
    _ = _ := by ring
private def firstLowConstant (d : KernelData) : ℝ := d.mu * (1 + Real.log 2) + |d.D| + |d.A| * Real.log 2
private theorem first_low_pointwise (d : KernelData) {y : ℝ} (hy : y ∈ Icc 1 2) : normalizedKernel d 1 y ≤ firstLowConstant d := by
  have hypos : 0 < y := by linarith [hy.1]
  have hhalfpos : 0 < y / 2 := by positivity
  have hhalfone : y / 2 ≤ 1 := by linarith [hy.2]
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy.1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogyle : Real.log y ≤ Real.log 2 := Real.log_le_log hypos hy.2
  have hloghalf : |Real.log (y / 2)| ≤ Real.log 2 := by
    rw [abs_of_nonpos (Real.log_nonpos hhalfpos.le hhalfone), Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  have hRhalf : |residual d.k d.A d.D (y / 2)| ≤ |d.D| + |d.A| * Real.log 2 := by
    rw [residual_at_most_one d hhalfone]
    calc
      _ ≤ |d.D * (y / 2)| + |d.A * (y / 2 * Real.log (y / 2))| := by
        simpa [sub_eq_add_neg] using abs_add_le (d.D * (y / 2)) (-(d.A * (y / 2 * Real.log (y / 2))))
      _ = (y / 2) * (|d.D| + |d.A| * |Real.log (y / 2)|) := by
        simp only [abs_mul, abs_of_pos hhalfpos]
        ring
      _ ≤ (y / 2) * (|d.D| + |d.A| * Real.log 2) := by gcongr
      _ ≤ |d.D| + |d.A| * Real.log 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hhalfone (by positivity : 0 ≤ |d.D| + |d.A| * Real.log 2)
  have hRy : |residual d.k d.A d.D y| ≤ d.mu * (1 + Real.log 2) := (d.residual_high y hy.1).trans (mul_le_mul_of_nonneg_left (by linarith)
      d.mu_nonneg)
  have hdiff : |residual d.k d.A d.D y - residual d.k d.A d.D (y / 2)| ≤ firstLowConstant d := by
    calc
      _ ≤ |residual d.k d.A d.D y| + |residual d.k d.A d.D (y / 2)| := by
        simpa [sub_eq_add_neg] using abs_add_le (residual d.k d.A d.D y) (-residual d.k d.A d.D (y / 2))
      _ ≤ _ := by simpa [firstLowConstant, add_assoc] using add_le_add hRy hRhalf
  have hmu := d.mu_nonneg
  have hB : 0 ≤ firstLowConstant d := by unfold firstLowConstant; positivity
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [hy.1, sq_nonneg (y - 1)]
  have hprod : firstLowConstant d ≤ firstLowConstant d * y ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left hy2 hB
  have hratio : quotientRatio 1 * y = y / 2 := by norm_num [quotientRatio]; ring
  unfold normalizedKernel
  rw [hratio]
  exact (div_le_iff₀ (sq_pos_of_pos hypos)).mpr (hdiff.trans hprod)

private theorem normalizedKernel_first (d : KernelData) : IntegrableOn (normalizedKernel d 1) (Ioi 1) ∧ (∫ y in Ioi 1, normalizedKernel d 1 y) ≤
    firstConstant d := by
  have hLowMajor : IntegrableOn (fun _ : ℝ => firstLowConstant d) (Icc 1 2) := integrableOn_const (measure_Icc_lt_top (μ := volume) (a := (1 :
      ℝ)) (b := 2)).ne
  have hLowInt : IntegrableOn (normalizedKernel d 1) (Icc 1 2) := by
    apply hLowMajor.mono_nonneg (measurable_normalizedKernel d 1).aestronglyMeasurable
    · exact ae_of_all _ (normalizedKernel_nonneg d 1)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact first_low_pointwise d hy
  have hLow : (∫ y in Icc 1 2, normalizedKernel d 1 y) ≤ firstLowConstant d := by
    calc
      _ ≤ ∫ _ : ℝ in Icc 1 2, firstLowConstant d := setIntegral_mono_on hLowInt hLowMajor measurableSet_Icc fun y hy => first_low_pointwise d hy
      _ = _ := by norm_num [setIntegral_const, Real.volume_real_Icc]
  have hHighMajor := (integrableOn_log_tail (by norm_num : (1 : ℝ) ≤ 2)).const_mul (2 * d.mu)
  have hpoint : ∀ y ∈ Ioi (2 : ℝ), normalizedKernel d 1 y ≤ 2 * d.mu * ((1 + Real.log y) / y ^ 2) := by
    intro y hy
    change (2 : ℝ) < y at hy
    have h := residual_difference_high d (by linarith : 1 ≤ y / 2) (by linarith : y / 2 ≤ y)
    have hdiv := div_le_div_of_nonneg_right h (sq_nonneg y)
    have hratio : quotientRatio 1 * y = y / 2 := by norm_num [quotientRatio]; ring
    unfold normalizedKernel
    rw [hratio]
    simpa only [mul_div_assoc] using hdiv
  have hHighInt : IntegrableOn (normalizedKernel d 1) (Ioi 2) := by
    apply hHighMajor.mono_nonneg (measurable_normalizedKernel d 1).aestronglyMeasurable
    · exact ae_of_all _ (normalizedKernel_nonneg d 1)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact hpoint y hy
  have hHigh : (∫ y in Ioi 2, normalizedKernel d 1 y) ≤ d.mu * (Real.log 2 + 2) := by
    calc
      _ ≤ ∫ y in Ioi (2 : ℝ), 2 * d.mu * ((1 + Real.log y) / y ^ 2) := setIntegral_mono_on hHighInt hHighMajor measurableSet_Ioi hpoint
      _ = _ := by rw [integral_const_mul, integral_log_tail (by norm_num)]; ring
  have hU := hLowInt.union hHighInt
  have hsub : Ioi (1 : ℝ) ⊆ Icc 1 2 ∪ Ioi 2 := by
    intro y hy
    by_cases h : y ≤ 2
    · exact Or.inl ⟨hy.le, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine ⟨hU.mono_set hsub, ?_⟩
  calc
    _ ≤ ∫ y in Icc 1 2 ∪ Ioi 2, normalizedKernel d 1 y := setIntegral_mono_set hU (ae_of_all _ (normalizedKernel_nonneg d 1)) (ae_of_all _ hsub)
    _ = (∫ y in Icc 1 2, normalizedKernel d 1 y) + (∫ y in Ioi 2, normalizedKernel d 1 y) := by
      exact setIntegral_union (disjoint_left.mpr fun y hy hz => not_lt_of_ge hy.2 hz) measurableSet_Ioi hLowInt hHighInt
    _ ≤ firstLowConstant d + d.mu * (Real.log 2 + 2) := add_le_add hLow hHigh
    _ = firstConstant d := by unfold firstLowConstant firstConstant; ring
private def inverseSquareBlock (d : KernelData) (m : ℕ) (t : ℝ) : ℝ := |block d.k d.A d.D m t| / t ^ 2
private theorem inverseSquareBlock_dilate (d : KernelData) {m : ℕ} (hm : 1 ≤ m) (t : ℝ) : inverseSquareBlock d m t = (1 / (m : ℝ) ^ 2) *
    normalizedKernel d m ((1 / (m : ℝ)) * t) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden : (m : ℝ) + 1 ≠ 0 := by positivity
  have harg : quotientRatio m * ((1 / (m : ℝ)) * t) = t / ((m : ℝ) + 1) := by
    unfold quotientRatio
    field_simp [hmpos.ne', hden]
    <;> ring
  unfold inverseSquareBlock normalizedKernel block
  rw [harg]
  rw [show (1 / (m : ℝ)) * t = t / (m : ℝ) by ring]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp [hmpos.ne', ht]
    <;> ring
private theorem transport_normalized_budget (d : KernelData) {m : ℕ} (hm : 1 ≤ m) {x N : ℝ} (hx : 1 < x) (hInt : IntegrableOn (normalizedKernel d
    m) (Ioi (1 / (m : ℝ)))) (hBudget : (∫ y in Ioi (1 / (m : ℝ)), normalizedKernel d m y) ≤ N) : IntegrableOn (fun t => |block d.k d.A d.D m t| *
    weight t) (Ioi x) ∧ blockIntegral d.k d.A d.D x m ≤ weightEnvelope x / (m : ℝ) * N := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hspos : 0 < 1 / (m : ℝ) := one_div_pos.mpr hmpos
  have hstart : 1 / (m : ℝ) ≤ (1 / (m : ℝ)) * x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.le hspos.le
  have hsub : Ioi ((1 / (m : ℝ)) * x) ⊆ Ioi (1 / (m : ℝ)) := fun _ hy => lt_of_le_of_lt hstart hy
  have hscaled := (integrableOn_Ioi_comp_mul_left_iff (normalizedKernel d m) x hspos).mpr (hInt.mono_set hsub)
  have hDensity : IntegrableOn (inverseSquareBlock d m) (Ioi x) := by
    exact IntegrableOn.congr_fun (hscaled.const_mul (1 / (m : ℝ) ^ 2)) (fun t _ => (inverseSquareBlock_dilate d hm t).symm) measurableSet_Ioi
  have hDensityBudget : (∫ t in Ioi x, inverseSquareBlock d m t) ≤ N / (m : ℝ) := by
    calc
      _ = (1 / (m : ℝ) ^ 2) * (∫ t in Ioi x, normalizedKernel d m ((1 / (m : ℝ)) * t)) := by
        simp_rw [inverseSquareBlock_dilate d hm]
        rw [integral_const_mul]
      _ = (1 / (m : ℝ)) * (∫ y in Ioi ((1 / (m : ℝ)) * x), normalizedKernel d m y) := by
        rw [integral_comp_mul_left_Ioi _ _ hspos, smul_eq_mul]
        field_simp [hmpos.ne']
        <;> ring
      _ ≤ (1 / (m : ℝ)) * (∫ y in Ioi (1 / (m : ℝ)), normalizedKernel d m y) := mul_le_mul_of_nonneg_left (setIntegral_mono_set hInt (ae_of_all _
          (normalizedKernel_nonneg d m)) (ae_of_all _ hsub)) hspos.le
      _ ≤ N / (m : ℝ) := by
        simpa [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hBudget hspos.le
  have hMajor := hDensity.const_mul (weightEnvelope x)
  have hpoint : ∀ t ∈ Ioi x, |block d.k d.A d.D m t| * weight t ≤ weightEnvelope x * inverseSquareBlock d m t := by
    intro t ht
    simpa [inverseSquareBlock, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left (weight_le hx ht.le)
        (abs_nonneg (block d.k d.A d.D m t))
  have hMeas : Measurable (fun t => |block d.k d.A d.D m t| * weight t) := by
    have h1 : Measurable (fun t : ℝ => residual d.k d.A d.D (t / (m : ℝ))) := (measurable_residual d.k d.A d.D).comp (by fun_prop)
    have h2 : Measurable (fun t : ℝ => residual d.k d.A d.D (t / ((m : ℝ) + 1))) := (measurable_residual d.k d.A d.D).comp (by fun_prop)
    simpa only [block, Nat.cast_add, Nat.cast_one, Real.norm_eq_abs, Pi.sub_apply] using ((h1.sub h2).norm).fun_mul (show Measurable weight by
        unfold weight; fun_prop)
  have hWeighted : IntegrableOn (fun t => |block d.k d.A d.D m t| * weight t) (Ioi x) := by
    apply hMajor.mono_nonneg hMeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (weight_nonneg (hx.trans ht))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpoint t ht
  refine ⟨hWeighted, ?_⟩
  unfold blockIntegral
  calc
    _ ≤ ∫ t in Ioi x, weightEnvelope x * inverseSquareBlock d m t := setIntegral_mono_on hWeighted hMajor measurableSet_Ioi hpoint
    _ = weightEnvelope x * (∫ t in Ioi x, inverseSquareBlock d m t) := integral_const_mul _ _
    _ ≤ weightEnvelope x * (N / (m : ℝ)) := mul_le_mul_of_nonneg_left hDensityBudget (weightEnvelope_nonneg hx)
    _ = _ := by ring

theorem quotientIntegralProducer (d : KernelData) : ∀ x : ℝ, 1 < x → (∀ m : ℕ, 1 ≤ m → IntegrableOn (fun t => |block d.k d.A d.D m t| * weight t)
    (Ioi x)) ∧ blockIntegral d.k d.A d.D x 1 ≤ weightEnvelope x * firstConstant d ∧ (∀ m : ℕ, 2 ≤ m → blockIntegral d.k d.A d.D x m ≤ envelope d
    x m) := by
  intro x hx
  have hfirst := transport_normalized_budget d (by omega : 1 ≤ (1 : ℕ)) hx
    (by simpa using (normalizedKernel_first d).1) (by simpa using (normalizedKernel_first d).2)
  have hlarge (m : ℕ) (hm : 2 ≤ m) := transport_normalized_budget d (by omega : 1 ≤ m) hx
      (normalizedKernel_budget d hm).1 (normalizedKernel_budget d hm).2
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    by_cases hm1 : m = 1
    · simpa [hm1] using hfirst.1
    · exact (hlarge m (by omega)).1
  · simpa using hfirst.2
  · intro m hm
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have heq : weightEnvelope x / (m : ℝ) * (budgetPolynomial d m / (m : ℝ)) = envelope d x m := by
      unfold envelope budgetPolynomial
      field_simp [hmpos.ne']
      <;> ring
    simpa only [heq] using (hlarge m hm).2

private theorem integral_natLogMoment {j : ℕ} (hj : 2 ≤ j) {a : ℝ} (ha : 1 < a) : (∫ t in Ioi a, natLogMoment j t) = 1 / (((j - 1 : ℕ) : ℝ) *
    (Real.log a) ^ (j - 1)) := by
  have hj1 : 1 ≤ j := by omega
  have hjreal : 1 < (j : ℝ) := by exact_mod_cast (by omega : 1 < j)
  have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj1, Nat.cast_one]
  have hexp : 1 - (j : ℝ) = -((j - 1 : ℕ) : ℝ) := by rw [hcast]; ring
  simp_rw [natLogMoment_eq]
  rw [integral_logMoment hjreal ha, hexp, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, ← hcast]
  simp [div_eq_mul_inv, mul_inv_rev, one_div]

private theorem natLogMoment_tail {j M : ℕ} (hj : 2 ≤ j) (hM : 2 ≤ M) : (∑' n : ℕ, natLogMoment j ((n + M + 1 : ℕ) : ℝ)) ≤ 1 / (((j - 1 : ℕ) : ℝ)
    * (Real.log M) ^ (j - 1)) := by
  have hMreal : 1 < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
  calc
    _ ≤ ∫ t in Ioi (M : ℝ), natLogMoment j t := AntitoneOn.tsum_comp_add_le_integral M (antitoneOn_natLogMoment j hMreal)
        (integrableOn_natLogMoment hj hMreal) (by
          intro t ht
          unfold natLogMoment
          have ht1 : 1 < t := hMreal.trans ht
          have hlog : 0 < Real.log t := Real.log_pos ht1
          have ht0 : 0 < t := by linarith
          positivity)
    _ = _ := integral_natLogMoment hj hMreal
private theorem logarithmic_consumer_tail (H q : ℕ → ℝ) {B W a2 a1 a0 : ℝ} (hB : 0 ≤ B) (hW : 0 ≤ W) (ha2 : 0 ≤ a2) (ha1 : 0 ≤ a1) (ha0 : 0 ≤ a0)
    (hq : ∀ m : ℕ, 2 ≤ m → 0 ≤ q m) (hH : ∀ m : ℕ, 2 ≤ m → |H m| ≤ B * (m : ℝ) / (Real.log m) ^ 4) (hQ : ∀ m : ℕ, 2 ≤ m → q m ≤ W / (m : ℝ) ^ 2 *
    (a2 * (Real.log m) ^ 2 + a1 * Real.log m + a0)) {M : ℕ} (hM : 2 ≤ M) : (∑' n : ℕ, |H (n + M + 1)| * q (n + M + 1)) ≤ B * W * (a2 / Real.log M
    + a1 / (2 * (Real.log M) ^ 2) + a0 / (3 * (Real.log M) ^ 3)) := by
  have hs (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => natLogMoment j ((n + M + 1 : ℕ) : ℝ)) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff (M + 1)).mpr (summable_natLogMoment hj)
  have hs2 := (hs 2 (by omega)).mul_left a2
  have hs3 := (hs 3 (by omega)).mul_left a1
  have hs4 := (hs 4 (by omega)).mul_left a0
  have hmajor := ((hs2.add hs3).add hs4).mul_left (B * W)
  have hpoint (n : ℕ) : |H (n + M + 1)| * q (n + M + 1) ≤ B * W * (a2 * natLogMoment 2 ((n + M + 1 : ℕ) : ℝ) + a1 * natLogMoment 3 ((n + M + 1 :
      ℕ) : ℝ) + a0 * natLogMoment 4 ((n + M + 1 : ℕ) : ℝ)) := by
    have hm : 2 ≤ n + M + 1 := by omega
    have hmreal : 1 < ((n + M + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + M + 1)
    simpa [natLogMoment, div_eq_mul_inv, mul_assoc] using logarithmic_product_le hB (by exact_mod_cast (by omega : 0 < n + M + 1))
        (Real.log_pos hmreal) (hq _ hm) (hH _ hm) (hQ _ hm)
  have hsum : Summable (fun n : ℕ => |H (n + M + 1)| * q (n + M + 1)) := hmajor.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (hq _ (by
      omega))) hpoint
  have hT2 : (∑' n : ℕ, natLogMoment 2 ((n + M + 1 : ℕ) : ℝ)) ≤ 1 / Real.log M := by
    simpa using natLogMoment_tail (j := 2) (by omega) hM
  have hT3 : (∑' n : ℕ, natLogMoment 3 ((n + M + 1 : ℕ) : ℝ)) ≤ 1 / (2 * (Real.log M) ^ 2) := by
    simpa using natLogMoment_tail (j := 3) (by omega) hM
  have hT4 : (∑' n : ℕ, natLogMoment 4 ((n + M + 1 : ℕ) : ℝ)) ≤ 1 / (3 * (Real.log M) ^ 3) := by
    simpa using natLogMoment_tail (j := 4) (by omega) hM
  calc
    _ ≤ ∑' n : ℕ, B * W * (a2 * natLogMoment 2 ((n + M + 1 : ℕ) : ℝ) + a1 * natLogMoment 3 ((n + M + 1 : ℕ) : ℝ) + a0 * natLogMoment 4 ((n + M +
        1 : ℕ) : ℝ)) := hsum.tsum_le_tsum hpoint hmajor
    _ = B * W * (a2 * (∑' n : ℕ, natLogMoment 2 ((n + M + 1 : ℕ) : ℝ)) + a1 * (∑' n : ℕ, natLogMoment 3 ((n + M + 1 : ℕ) : ℝ)) + a0 * (∑' n : ℕ,
        natLogMoment 4 ((n + M + 1 : ℕ) : ℝ))) := by
      rw [tsum_mul_left, (hs2.add hs3).tsum_add hs4, hs2.tsum_add hs3]
      simp_rw [tsum_mul_left]
    _ ≤ B * W * (a2 * (1 / Real.log M) + a1 * (1 / (2 * (Real.log M) ^ 2)) + a0 * (1 / (3 * (Real.log M) ^ 3))) := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hT2 ha2) (mul_le_mul_of_nonneg_left hT3 ha1)) (mul_le_mul_of_nonneg_left hT4 ha0))
        (mul_nonneg hB hW)
    _ = _ := by ring
private theorem blockIntegral_nonneg (d : KernelData) {x : ℝ} (hx : 1 < x) (m : ℕ) : 0 ≤ blockIntegral d.k d.A d.D x m := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (abs_nonneg _) (weight_nonneg (hx.trans ht))
private theorem budget_coefficients_nonneg (d : KernelData) : 0 ≤ quadratic d ∧ 0 ≤ linear d ∧ 0 ≤ constant d := by
  have hC := d.C_nonneg
  have hmu := d.mu_nonneg
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold quadratic linear constant
  constructor
  · positivity
  · constructor <;> positivity

theorem quotient_logarithmic_tail (d : KernelData) (H : ℕ → ℝ) {B x : ℝ} (hB : 0 ≤ B) (hx : 1 < x) (hH : ∀ m : ℕ, 2 ≤ m → |H m| ≤ B * (m : ℝ) /
    (Real.log m) ^ 4) {M : ℕ} (hM : 2 ≤ M) : (∑' n : ℕ, |H (n + M + 1)| * blockIntegral d.k d.A d.D x (n + M + 1)) ≤ B * weightEnvelope x *
    (quadratic d / Real.log M + linear d / (2 * (Real.log M) ^ 2) + constant d / (3 * (Real.log M) ^ 3)) := by
  obtain ⟨ha2, ha1, ha0⟩ := budget_coefficients_nonneg d
  exact logarithmic_consumer_tail H (blockIntegral d.k d.A d.D x) hB (weightEnvelope_nonneg hx) ha2 ha1 ha0 (fun m _ => blockIntegral_nonneg d hx
      m) hH (fun m hm => by
      simpa [envelope] using ((quotientIntegralProducer d x hx).2.2 m hm)) hM

def signedBlock (d : KernelData) (H : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ := H m * block d.k d.A d.D m t * weight t
private theorem signedBlock_norm (d : KernelData) (H : ℕ → ℝ) (m : ℕ) {x t : ℝ} (hx : 1 < x) (ht : t ∈ Ioi x) : ‖signedBlock d H m t‖ = |H m| *
    (|block d.k d.A d.D m t| * weight t) := by
  simp [signedBlock, Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg (hx.trans ht)), mul_assoc]

private theorem signedBlock_integrable (d : KernelData) (H : ℕ → ℝ) {x : ℝ} (hx : 1 < x) {m : ℕ} (hm : 1 ≤ m) : IntegrableOn (signedBlock d H m)
    (Ioi x) := by
  have hmajor := ((quotientIntegralProducer d x hx).1 m hm).const_mul |H m|
  have hMeas : Measurable (signedBlock d H m) := by
    have h1 : Measurable (fun t : ℝ => residual d.k d.A d.D (t / (m : ℝ))) := (measurable_residual d.k d.A d.D).comp (by fun_prop)
    have h2 : Measurable (fun t : ℝ => residual d.k d.A d.D (t / ((m : ℝ) + 1))) := (measurable_residual d.k d.A d.D).comp (by fun_prop)
    have hH : Measurable (fun _ : ℝ => H m) := measurable_const
    unfold signedBlock block
    exact (hH.fun_mul (h1.fun_sub h2)).fun_mul (show Measurable weight by unfold weight; fun_prop)
  apply hmajor.mono' hMeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact le_of_eq (signedBlock_norm d H m hx ht)
private theorem signedBlock_integral_norm (d : KernelData) (H : ℕ → ℝ) (m : ℕ) {x : ℝ} (hx : 1 < x) : (∫ t in Ioi x, ‖signedBlock d H m t‖) = |H
    m| * blockIntegral d.k d.A d.D x m := by
  calc
    _ = ∫ t in Ioi x, |H m| * (|block d.k d.A d.D m t| * weight t) := setIntegral_congr_fun measurableSet_Ioi fun t ht => signedBlock_norm d H m
        hx ht
    _ = _ := integral_const_mul _ _
private theorem summable_quotient_integral_norms (d : KernelData) (H : ℕ → ℝ) {B x : ℝ} (hB : 0 ≤ B) (hx : 1 < x) (hH : ∀ m : ℕ, 2 ≤ m → |H m| ≤
    B * (m : ℝ) / (Real.log m) ^ 4) : Summable (fun n : ℕ => ∫ t in Ioi x, ‖signedBlock d H (n + 1) t‖) := by
  have htail := summable_logarithmic_consumer H (blockIntegral d.k d.A d.D x) hB (fun m _ => blockIntegral_nonneg d hx m) hH (fun m hm => by
      simpa [envelope] using ((quotientIntegralProducer d x hx).2.2 m hm))
  have hall : Summable (fun n : ℕ => |H (n + 1)| * blockIntegral d.k d.A d.D x (n + 1)) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_assoc] using htail
  simpa only [signedBlock_integral_norm d H _ hx] using hall
/-- Actual signed blocks: every positive block is integrable, norm integrals are
summable, the unrestricted first coefficient is paid separately, and every
strict norm tail has the explicit logarithmic bound. -/
theorem quotient_signed_integral_budget (d : KernelData) (H : ℕ → ℝ) {B x : ℝ}
    (hB : 0 ≤ B) (hx : 1 < x)
    (hH : ∀ m : ℕ, 2 ≤ m → |H m| ≤ B * (m : ℝ) / (Real.log m) ^ 4) :
    (∀ m : ℕ, 1 ≤ m → IntegrableOn (signedBlock d H m) (Ioi x)) ∧
    Summable (fun n : ℕ => ∫ t in Ioi x, ‖signedBlock d H (n + 1) t‖) ∧
    (∫ t in Ioi x, ‖signedBlock d H 1 t‖) ≤
      |H 1| * weightEnvelope x * firstConstant d ∧
    (∀ M : ℕ, 2 ≤ M →
      (∑' n : ℕ, ∫ t in Ioi x, ‖signedBlock d H (n + M + 1) t‖) ≤
        B * weightEnvelope x *
          (quadratic d / Real.log M + linear d / (2 * (Real.log M) ^ 2) +
            constant d / (3 * (Real.log M) ^ 3))) := by
  refine ⟨fun m hm => signedBlock_integrable d H hx hm,
    summable_quotient_integral_norms d H hB hx hH, ?_, ?_⟩
  · rw [signedBlock_integral_norm d H 1 hx]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left
      ((quotientIntegralProducer d x hx).2.1) (abs_nonneg (H 1))
  · intro M hM
    simpa only [signedBlock_integral_norm d H _ hx] using
      quotient_logarithmic_tail d H hB hx hH hM

end D5.S3.Arith.Robin.QuotientIntegralBudget

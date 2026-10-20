/- GID: D5/S3/Arith/MoebiusLogarithmic/UniformBound
   generality: G
   mirror-B: D5/B/S3/Arith/MoebiusLogarithmic/UniformBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius, mathlib/module/Mathlib.NumberTheory.AbelSummation]
   utility: none
   digest: Finite logarithmic Moebius sums are controlled by a positive fractional-part kernel. -/

import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Arith.MoebiusLogarithmic.CoprimeConvolution
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.EulerProduct.Basic

open scoped BigOperators
open Finset MeasureTheory

noncomputable section
attribute [local instance] Classical.propDecidable
namespace D5.S3.Arith.MoebiusLogarithmic

/-- The original finite logarithmic sum, with its exact coprime restriction. -/
def coprimeLogSum (q : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Ioc 0 ⌊x⌋₊).filter (Nat.Coprime · q),
    (ArithmeticFunction.moebius n : ℝ) / n * Real.log (x / n)

private theorem positive_interval (k : ℕ) : Icc 1 k = Ioc 0 k := by
  ext n
  simp only [mem_Icc, mem_Ioc]
  omega

private def reciprocalFunction (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := f n / n
  map_zero' := by simp

private theorem reciprocalFunction_mul (f g : ArithmeticFunction ℝ) :
    reciprocalFunction (f * g) = reciprocalFunction f * reciprocalFunction g := by
  ext n
  change (f * g) n / (n : ℝ) = ∑ ab ∈ n.divisorsAntidiagonal,
    reciprocalFunction f ab.1 * reciprocalFunction g ab.2
  rw [ArithmeticFunction.mul_apply, sum_div]
  apply sum_congr rfl
  intro ab hab
  have he := (Nat.mem_divisorsAntidiagonal.mp hab).1
  change f ab.1 * g ab.2 / (n : ℝ) = (f ab.1 / ab.1) * (g ab.2 / ab.2)
  rw [div_mul_div_comm, ← Nat.cast_mul, he]

private theorem harmonic_cancellation {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / n *
      (harmonic ⌊x / n⌋₊ : ℝ)) = 1 := by
  let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hmz : m * z = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hr1 : reciprocalFunction (1 : ArithmeticFunction ℝ) = 1 := by
    ext n
    by_cases hn : n = 1 <;> simp [reciprocalFunction, ArithmeticFunction.one_apply, hn]
  have he := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (reciprocalFunction m) (reciprocalFunction z) ⌊x⌋₊
  rw [← reciprocalFunction_mul, hmz, hr1] at he
  have hs : (∑ n ∈ Ioc 0 ⌊x⌋₊, (1 : ArithmeticFunction ℝ) n) = 1 := by
    rw [sum_eq_single 1]
    · simp
    · intro n hn hn1
      simp [hn1]
    · intro hn
      exact (hn (mem_Ioc.mpr ⟨by omega, Nat.le_floor (by simpa using hx)⟩)).elim
  rw [hs] at he
  symm
  convert he using 1
  apply sum_congr rfl
  intro n hn
  simp only [reciprocalFunction, ArithmeticFunction.coe_mk,
    ArithmeticFunction.intCoe_apply, Nat.floor_div_natCast]
  congr 1
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [positive_interval]
  apply sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := ne_of_gt (mem_Ioc.mp hk).1
  simp [z, ArithmeticFunction.zeta_apply, hk0]

/-- The nonnegative fractional-part kernel on the positive real axis. -/
private def fractionalKernel (t : ℝ) : ℝ :=
  (t - (⌊t⌋₊ : ℝ)) / t ^ 2

private def fractionalPrimitive (t : ℝ) : ℝ := ∫ u in (1 : ℝ)..t, fractionalKernel u

private theorem kernel_integrable {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable fractionalKernel volume a b := by
  have hmeas : Measurable fractionalKernel := by
    unfold fractionalKernel
    exact (measurable_id.sub ((measurable_of_countable
      (f := fun n : ℕ => (n : ℝ))).comp measurable_id.nat_floor)).div
        (measurable_id.pow_const 2)
  have hc : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  apply hc.intervalIntegrable.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have ht0 : 0 < t := by
    rw [Set.uIoc_of_le hab] at ht
    linarith [ht.1]
  dsimp only [fractionalKernel]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
    (sub_nonneg.mpr (Nat.floor_le ht0.le)) (sq_nonneg t))]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  linarith [Nat.lt_floor_add_one t]

private theorem primitive_monotone {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    fractionalPrimitive a ≤ fractionalPrimitive b := by
  have hi₁ := kernel_integrable (a := 1) (b := a) le_rfl ha
  have hi₂ := kernel_integrable ha hab
  have hpos : 0 ≤ ∫ t in a..b, fractionalKernel t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (sub_nonneg.mpr (Nat.floor_le (by linarith [ht.1]))) (sq_nonneg t)
  have he := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  change (∫ t in (1 : ℝ)..a, fractionalKernel t) ≤ ∫ t in (1 : ℝ)..b, fractionalKernel t
  linarith

private theorem primitive_eq {x : ℝ} (hx : 1 ≤ x) :
    fractionalPrimitive x = Real.log x - (harmonic ⌊x⌋₊ : ℝ) + (⌊x⌋₊ : ℝ) / x := by
  let c : ℕ → ℝ := fun n => if n = 0 then 0 else 1
  have hcs (k : ℕ) : (∑ n ∈ Icc 0 k, c n) = k := by
    rw [Icc_eq_cons_Ioc (Nat.zero_le k), sum_cons]
    simp only [c, if_pos rfl, zero_add]
    have he : ∀ n ∈ Ioc 0 k, (if n = 0 then (0 : ℝ) else 1) = 1 := by
      intro n hn
      simp [ne_of_gt (mem_Ioc.mp hn).1]
    simp_rw [sum_congr rfl he]
    simp
  have hd (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) x) :
      HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t := by
    exact hasDerivAt_inv (by linarith [ht.1])
  have hi : IntegrableOn (deriv (fun u : ℝ => u⁻¹)) (Set.Icc 1 x) := by
    have hc : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc 1 x) := by
      exact ((continuousOn_id.pow 2).inv₀
        (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg
    exact (hc.congr (fun t ht => (hd t ht).deriv)).integrableOn_Icc
  have he := sum_mul_eq_sub_integral_mul₀ c (by simp [c]) x
    (fun t ht => (hd t ht).differentiableAt) hi
  have he' : (harmonic ⌊x⌋₊ : ℝ) = (⌊x⌋₊ : ℝ) / x +
      ∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2 := by
    simp only [hcs] at he
    have hs : (∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ)⁻¹ * c k) = (harmonic ⌊x⌋₊ : ℝ) := by
      rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
      simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [positive_interval]
      apply sum_congr rfl
      intro k hk
      simp [c, ne_of_gt (mem_Ioc.mp hk).1]
    rw [hs, ← intervalIntegral.integral_of_le hx] at he
    have hder : (∫ t in (1 : ℝ)..x, deriv (fun u : ℝ => u⁻¹) t * (⌊t⌋₊ : ℝ)) =
        -(∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [(hd t (by rw [Set.uIcc_of_le hx] at ht; exact ht)).deriv]
      ring
    rw [hder] at he
    simpa [div_eq_mul_inv, mul_comm] using he
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact continuousOn_id.inv₀ (fun t ht => by change t ≠ 0; linarith [ht.1])
  have hfloor : IntervalIntegrable (fun t : ℝ => (⌊t⌋₊ : ℝ) / t ^ 2) volume 1 x := by
    have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 1 x) := by
      exact (continuousOn_id.pow 2).inv₀
        (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
    have hs := integrableOn_mul_sum_Icc c (m := 0) (a := 1) (b := x) (by norm_num) hc.integrableOn_Icc
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    simpa [hcs, div_eq_mul_inv, mul_comm] using hs
  have hk : fractionalPrimitive x = (∫ t in (1 : ℝ)..x, t⁻¹) -
      ∫ t in (1 : ℝ)..x, (⌊t⌋₊ : ℝ) / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hinv hfloor]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
    dsimp [fractionalKernel]
    field_simp
    <;> ring
  rw [hk, integral_inv_of_pos (by norm_num) (by linarith), div_one]
  linarith

private theorem primitive_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ fractionalPrimitive x ∧ fractionalPrimitive x ≤ 1 - 1 / x := by
  have hi := kernel_integrable (a := 1) (b := x) le_rfl hx
  have hc : ContinuousOn (fun t : ℝ => 1 / t ^ 2) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]
    exact continuousOn_const.div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))
  have he : (∫ t in (1 : ℝ)..x, 1 / t ^ 2) = 1 - 1 / x := by
    have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) x) :
        HasDerivAt (fun u : ℝ => -u⁻¹) (1 / t ^ 2) t := by
      have ht0 : t ≠ 0 := by rw [Set.uIcc_of_le hx] at ht; linarith [ht.1]
      convert! (hasDerivAt_inv ht0).neg using 1 <;>
        simp only [neg_neg, one_div, Pi.neg_apply]
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    simpa [one_div, sub_eq_add_neg, add_comm] using he
  constructor
  · apply intervalIntegral.integral_nonneg hx
    intro t ht
    exact div_nonneg (sub_nonneg.mpr (Nat.floor_le (by linarith [ht.1]))) (sq_nonneg t)
  · change (∫ t in (1 : ℝ)..x, fractionalKernel t) ≤ _
    rw [← he]
    apply intervalIntegral.integral_mono_on hx hi hc.intervalIntegrable
    intro t ht
    dsimp [fractionalKernel]
    apply div_le_div_of_nonneg_right _ (sq_nonneg t)
    linarith [Nat.lt_floor_add_one t]

private theorem weighted_prefix_bound (a w : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (ha : ∀ k ≤ N, |∑ i ∈ range k, a i| ≤ 1)
    (hw : ∀ i < N, 0 ≤ w i)
    (hdec : ∀ i, i + 1 < N → w (i + 1) ≤ w i) :
    |∑ i ∈ range N, w i * a i| ≤ w 0 := by
  have he := Finset.sum_range_by_parts w a N
  simp only [smul_eq_mul] at he
  have he' : (∑ i ∈ range N, w i * a i) =
      w (N - 1) * (∑ i ∈ range N, a i) +
        ∑ i ∈ range (N - 1), (w i - w (i + 1)) * (∑ j ∈ range (i + 1), a j) := by
    rw [he]
    have hn : (∑ i ∈ range (N - 1),
        (w i - w (i + 1)) * (∑ j ∈ range (i + 1), a j)) =
        -(∑ i ∈ range (N - 1),
          (w (i + 1) - w i) * (∑ j ∈ range (i + 1), a j)) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hn]
    ring
  rw [he']
  calc
    _ ≤ |w (N - 1) * (∑ i ∈ range N, a i)| +
        |∑ i ∈ range (N - 1), (w i - w (i + 1)) * (∑ j ∈ range (i + 1), a j)| :=
      abs_add_le _ _
    _ ≤ w (N - 1) + ∑ i ∈ range (N - 1), (w i - w (i + 1)) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw _ (by omega))]
        exact (mul_le_mul_of_nonneg_left (ha N le_rfl) (hw _ (by omega))).trans_eq (mul_one _)
      · calc
          _ ≤ ∑ i ∈ range (N - 1),
              |(w i - w (i + 1)) * (∑ j ∈ range (i + 1), a j)| := abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply sum_le_sum
            intro i hi
            have hiN : i + 1 < N := by have := mem_range.mp hi; omega
            have hcoef := sub_nonneg.mpr (hdec i hiN)
            rw [abs_mul, abs_of_nonneg hcoef]
            exact (mul_le_mul_of_nonneg_left (ha _ (by omega)) hcoef).trans_eq (mul_one _)
    _ = w 0 := by rw [sum_range_sub']; ring

/-- The logarithmic base sum lies in the stronger interval with endpoint `2(1-1/x)`. -/
theorem logarithmic_base_bound (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ coprimeLogSum 1 x ∧ coprimeLogSum 1 x ≤ 2 * (1 - 1 / x) := by
  let N := ⌊x⌋₊
  have hN : 0 < N := Nat.floor_pos.mpr hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let a : ℕ → ℝ := fun i => (ArithmeticFunction.moebius (i + 1) : ℝ) / (i + 1)
  let w : ℕ → ℝ := fun i => fractionalPrimitive (x / (i + 1))
  have hpref (k : ℕ) : (∑ i ∈ range k, a i) = reciprocalSum (k : ℝ) := by
    simpa [a, reciprocalSum, Nat.cast_add, Nat.cast_one, positive_interval,
      Ico_add_one_right_eq_Icc] using
      (sum_Ico_add' (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / n) 0 k 1)
  have harg (i : ℕ) (hi : i < N) : 1 ≤ x / (i + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < i + 1)).mpr
    have hn : i + 1 ≤ N := by omega
    have hn' : ((i + 1 : ℕ) : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hn
    simpa using hn'
  have hw (i : ℕ) (hi : i < N) : 0 ≤ w i := (primitive_bounds (harg i hi)).1
  have hdec (i : ℕ) (hi : i + 1 < N) : w (i + 1) ≤ w i := by
    apply primitive_monotone (harg (i + 1) hi)
    change x / (↑(i + 1) + 1) ≤ x / (↑i + 1)
    apply div_le_div_of_nonneg_left hx0.le (by positivity)
    norm_num
  have hbound := weighted_prefix_bound a w N hN
    (fun k hk => by rw [hpref]; exact abs_reciprocalSum_le_one _) hw hdec
  have hrepr : coprimeLogSum 1 x = 1 - 1 / x + ∑ i ∈ range N, w i * a i := by
    have hh := harmonic_cancellation hx
    have hf := floor_cancellation hx
    have he (n : ℕ) (hn : n ∈ Ioc 0 N) :
        Real.log (x / n) = (harmonic ⌊x / n⌋₊ : ℝ) -
          (⌊x / n⌋₊ : ℝ) / (x / n) + fractionalPrimitive (x / n) := by
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Ioc.mp hn).1
      have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp (mem_Ioc.mp hn).2
      linarith [primitive_eq ((le_div_iff₀ hn0).mpr (by simpa using hnx))]
    have hcorr : (∑ n ∈ Ioc 0 N,
        (ArithmeticFunction.moebius n : ℝ) / n * ((⌊x / n⌋₊ : ℝ) / (x / n))) = 1 / x := by
      rw [← hf, sum_div]
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (mem_Ioc.mp hn).1)
      field_simp
    have herr : (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / n *
        fractionalPrimitive (x / n)) = ∑ i ∈ range N, w i * a i := by
      rw [← Icc_add_one_left_eq_Ioc, range_eq_Ico]
      simpa [a, w, Nat.cast_add, Nat.cast_one, mul_comm, Ico_add_one_right_eq_Icc] using
        (sum_Ico_add' (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / n *
          fractionalPrimitive (x / n)) 0 N 1).symm
    have hfilter : (Ioc 0 ⌊x⌋₊).filter (Nat.Coprime · 1) = Ioc 0 ⌊x⌋₊ := by
      apply filter_eq_self.mpr
      intro n hn
      exact Nat.coprime_one_right n
    rw [coprimeLogSum, hfilter]
    change (∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / n * Real.log (x / n)) = _
    calc
      _ = ∑ n ∈ Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) / n *
          ((harmonic ⌊x / n⌋₊ : ℝ) - (⌊x / n⌋₊ : ℝ) / (x / n) +
            fractionalPrimitive (x / n)) := sum_congr rfl fun n hn => by rw [he n hn]
      _ = _ := by
        simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
        rw [hh, hcorr, herr]
  have hw0 : w 0 = fractionalPrimitive x := by simp [w]
  rw [hw0] at hbound
  have hp := primitive_bounds hx
  have hb := abs_le.mp hbound
  rw [hrepr]
  constructor <;> linarith

private theorem sum_divisors_triangle (f : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 (N / d), f d e := by
  have hpair : (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, f d (n / d)) =
      ∑ ab ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun ab => ab.1 * ab.2 ≤ N), f ab.1 ab.2 := by
    trans ∑ n ∈ Ioc 0 N, ∑ ab ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter
      (fun ab => ab.1 * ab.2 = n), f ab.1 ab.2
    · apply sum_congr rfl
      intro n hn
      rw [← Nat.sum_divisorsAntidiagonal f,
        Nat.divisorsAntidiagonal_eq_prod_filter_of_le (mem_Ioc.mp hn).1.ne' (mem_Ioc.mp hn).2]
    · simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro ab hab
      have hab' := mem_product.mp hab
      have ha := (mem_Ioc.mp hab'.1).1
      have hb := (mem_Ioc.mp hab'.2).1
      simp [mem_Ioc, Nat.mul_pos ha hb]
  rw [hpair, sum_filter, sum_product]
  apply sum_congr rfl
  intro d hd
  simp only [sum_ite, sum_const_zero, add_zero]
  congr 1
  ext e
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨he0, heN⟩, hde⟩
    exact ⟨he0, (Nat.le_div_iff_mul_le (mem_Ioc.mp hd).1).mpr (by simpa [mul_comm] using hde)⟩
  · rintro ⟨he0, he⟩
    exact ⟨⟨he0, he.trans (Nat.div_le_self N d)⟩,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le (mem_Ioc.mp hd).1).mp he⟩

private theorem logarithmic_convolution (q : ℕ) (x : ℝ) (hx : 0 < x) :
    coprimeLogSum q x =
      ∑ d ∈ (Ioc 0 ⌊x⌋₊).filter (PrimeSupported q),
        coprimeLogSum 1 (x / d) / d := by
  let N := ⌊x⌋₊
  let h : ℕ → ℝ := fun n => Real.log (x / n) / n
  have he (n : ℕ) :
      (if n.Coprime q then (ArithmeticFunction.moebius n : ℝ) else 0) * h n =
        ∑ d ∈ n.divisors, if PrimeSupported q d then
          (ArithmeticFunction.moebius (n / d) : ℝ) * h n else 0 := by
    have hc := congrArg (fun a : ℤ => (a : ℝ)) (sum_supported_moebius q n)
    simp only [Int.cast_sum, Int.cast_ite, Int.cast_zero, sum_filter] at hc
    rw [← hc, sum_mul]
    apply sum_congr rfl
    intro d hd
    split_ifs <;> simp_all
  have hleft : coprimeLogSum q x =
      ∑ n ∈ Ioc 0 N, (if n.Coprime q then (ArithmeticFunction.moebius n : ℝ) else 0) * h n := by
    simp only [coprimeLogSum, sum_filter]
    apply sum_congr rfl
    intro n hn
    dsimp [h]
    split_ifs <;> ring
  rw [hleft]
  simp_rw [he]
  have hreindex := sum_divisors_triangle
    (fun d e => if PrimeSupported q d then (ArithmeticFunction.moebius e : ℝ) * h (d * e) else 0) N
  have hdiv : (∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors,
      if PrimeSupported q d then (ArithmeticFunction.moebius (n / d) : ℝ) * h n else 0) =
      ∑ d ∈ Ioc 0 N, ∑ e ∈ Ioc 0 (N / d),
        if PrimeSupported q d then (ArithmeticFunction.moebius e : ℝ) * h (d * e) else 0 := by
    convert hreindex using 1
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro d hd
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  rw [hdiv, sum_filter]
  apply sum_congr rfl
  intro d hd
  by_cases hsd : PrimeSupported q d
  · simp only [if_pos hsd]
    have hfilter : (Ioc 0 ⌊x / d⌋₊).filter (Nat.Coprime · 1) = Ioc 0 ⌊x / d⌋₊ :=
      filter_eq_self.mpr (fun n hn => Nat.coprime_one_right n)
    rw [coprimeLogSum, hfilter, Nat.floor_div_natCast, sum_div]
    apply sum_congr rfl
    intro e he
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mem_Ioc.mp hd).1.ne'
    have he0 : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (mem_Ioc.mp he).1.ne'
    dsimp [h]
    rw [Nat.cast_mul, div_div]
    ring
  · simp [hsd]

private theorem supported_reciprocal_mass (q N : ℕ) (hq : 1 ≤ q) :
    (∑ d ∈ (Ioc 0 N).filter (PrimeSupported q), (d : ℝ)⁻¹) ≤ (q : ℝ) / Nat.totient q := by
  let f : ℕ →* ℝ := {
    toFun := fun n => (n : ℝ)⁻¹
    map_one' := by simp
    map_mul' := by intro a b; simp [mul_inv_rev, mul_comm] }
  have hf {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hs := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hf q.primeFactors
  have hmem (d : ℕ) (hd : d ∈ (Ioc 0 N).filter (PrimeSupported q)) :
      d ∈ Nat.factoredNumbers q.primeFactors := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpd
    exact hp.mem_primeFactors ((mem_filter.mp hd).2 p hp hpd) (by omega)
  let s := ((Ioc 0 N).filter (PrimeSupported q)).attach.map
    ⟨fun d : ↥((Ioc 0 N).filter (PrimeSupported q)) =>
        (⟨d.val, hmem d.val d.property⟩ : Nat.factoredNumbers q.primeFactors),
      fun a b he => Subtype.ext (congrArg
        (fun d : Nat.factoredNumbers q.primeFactors => d.val) he)⟩
  have hle := hs.2.summable.sum_le_tsum s
    (fun d hd => inv_nonneg.mpr (Nat.cast_nonneg d.val))
  have hprod : (∏ p ∈ q.primeFactors.filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹) =
      (q : ℝ) / Nat.totient q := by
    have hfilter : q.primeFactors.filter Nat.Prime = q.primeFactors :=
      filter_eq_self.mpr (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [hfilter, prod_inv_distrib]
    have ht : (Nat.totient q : ℝ) = (q : ℝ) * ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) := by
      simpa only [map_mul, map_prod, map_sub, map_one, map_inv₀, map_natCast] using
        congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    have ht0 : (Nat.totient q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (by omega)).ne'
    have hp0 : (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at ht
      exact ht0 ht
    apply (eq_div_iff ht0).mpr
    rw [ht, mul_left_comm, inv_mul_cancel₀ hp0, mul_one]
  rw [hs.2.tsum_eq] at hle
  change (∑ d ∈ s, (d.val : ℝ)⁻¹) ≤
    ∏ p ∈ q.primeFactors.filter Nat.Prime, (1 - (p : ℝ)⁻¹)⁻¹ at hle
  rw [hprod] at hle
  simp only [s, sum_map] at hle
  change (∑ d ∈ ((Ioc 0 N).filter (PrimeSupported q)).attach,
    (d.val : ℝ)⁻¹) ≤ _ at hle
  rwa [sum_attach _ (fun d : ℕ => (d : ℝ)⁻¹)] at hle

/-- The unconditional uniform bound for every positive modulus and positive real cutoff. -/
theorem coprime_log_uniform_bound (q : ℕ) (x : ℝ) (hq : 1 ≤ q) (hx : 0 < x) :
    0 ≤ coprimeLogSum q x ∧ coprimeLogSum q x ≤ 2 * q / Nat.totient q := by
  rw [logarithmic_convolution q x hx]
  have hterm (d : ℕ) (hd : d ∈ (Ioc 0 ⌊x⌋₊).filter (PrimeSupported q)) :
      0 ≤ coprimeLogSum 1 (x / d) ∧ coprimeLogSum 1 (x / d) ≤ 2 := by
    have hd' := mem_Ioc.mp (mem_filter.mp hd).1
    have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd'.1
    have hdx : (d : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hd'.2
    have hb := logarithmic_base_bound (x / d) ((le_div_iff₀ hdpos).mpr (by simpa using hdx))
    have ht : (0 : ℝ) ≤ 1 / (x / (d : ℝ)) := by positivity
    exact ⟨hb.1, hb.2.trans (by linarith)⟩
  constructor
  · exact sum_nonneg fun d hd => div_nonneg (hterm d hd).1 (Nat.cast_nonneg d)
  · calc
      _ ≤ ∑ d ∈ (Ioc 0 ⌊x⌋₊).filter (PrimeSupported q), 2 / (d : ℝ) :=
        sum_le_sum fun d hd => div_le_div_of_nonneg_right (hterm d hd).2 (Nat.cast_nonneg d)
      _ = 2 * ∑ d ∈ (Ioc 0 ⌊x⌋₊).filter (PrimeSupported q), (d : ℝ)⁻¹ := by simp [mul_sum, div_eq_mul_inv]
      _ ≤ 2 * ((q : ℝ) / Nat.totient q) :=
        mul_le_mul_of_nonneg_left (supported_reciprocal_mass q _ hq) (by norm_num)
      _ = _ := by ring

#print axioms logarithmic_base_bound
#print axioms coprime_log_uniform_bound

#print axioms harmonic_cancellation
#print axioms primitive_eq
end D5.S3.Arith.MoebiusLogarithmic

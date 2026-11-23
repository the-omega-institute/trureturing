/- GID: D5/S3/Fourier/Concentration/FiniteSincCollisionMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteSincCollisionMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sinc-squared moments are controlled by weighted near-collisions. -/

import D5.S3.Fourier.InfiniteSincProduct
import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Control of a finite weighted sinc matrix at the scale of its near-collisions. -/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory Set
open scoped NNReal
open D5.S3.Fourier.InfiniteSincProduct
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSineMissingWindow (floor_grid_cover sine_score_change)
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder

namespace D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

private def binKernel (d : ℤ) : ℝ :=
  if d.natAbs ≤ 1 then 1 else 1 / ((d.natAbs : ℝ) - 1) ^ 2

private theorem binKernel_nonneg (d : ℤ) : 0 ≤ binKernel d := by
  unfold binKernel
  split <;> positivity

private theorem binKernel_even : Function.Even binKernel := by
  intro d
  simp [binKernel]

private theorem binKernel_succ (n : ℕ) :
    binKernel ((n + 1 : ℕ) : ℤ) = (if n = 0 then 1 else 0) + 1 / (n : ℝ) ^ 2 := by
  cases n with
  | zero => norm_num [binKernel]
  | succ n =>
    rw [binKernel, Int.natAbs_natCast, ite_eq_right (by omega)]
    simp [Nat.cast_succ]

private theorem binKernel_sum :
    Summable binKernel ∧ (∑' d : ℤ, binKernel d) ≤ 7 := by
  have hsingle : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by simp)
  have hnat : Summable (fun n : ℕ => binKernel (n : ℤ)) := by
    rw [← summable_nat_add_iff 1]
    simp_rw [binKernel_succ]
    exact hsingle.add hasSum_zeta_two.summable
  have hint : Summable binKernel := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨hnat, hnat.congr fun n => (binKernel_even (n : ℤ)).symm⟩
  refine ⟨hint, ?_⟩
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat binKernel_even hint,
    tsum_pnat_eq_tsum_succ (f := fun n : ℕ => binKernel (n : ℤ))]
  have hsum :
      (∑' n : ℕ, binKernel ((n + 1 : ℕ) : ℤ)) = 1 + Real.pi ^ 2 / 6 := by
    simp_rw [binKernel_succ]
    rw [hsingle.tsum_add hasSum_zeta_two.summable, tsum_ite_eq, hasSum_zeta_two.tsum_eq]
  rw [hsum, show binKernel 0 = 1 by norm_num [binKernel]]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have hpi : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  linarith

private theorem row_le (bins : Finset ℤ) (k : ℤ) :
    ∑ l ∈ bins, binKernel (k - l) ≤ 7 := by
  let e : ℤ ≃ ℤ := Equiv.subLeft k
  change (∑ l ∈ bins, binKernel (e.toEmbedding l)) ≤ 7
  rw [← sum_map bins e.toEmbedding]
  exact (binKernel_sum.1.sum_le_tsum _ (fun d _ => binKernel_nonneg d)).trans binKernel_sum.2

private theorem sinc_sq_le_binKernel (x y : ℝ) :
    Real.sinc (x - y) ^ 2 ≤ binKernel (frequencyBin x - frequencyBin y) := by
  let d := frequencyBin x - frequencyBin y
  change Real.sinc (x - y) ^ 2 ≤ binKernel d
  unfold binKernel
  split_ifs with h
  · have hs : |Real.sinc (x - y)| ≤ |(1 : ℝ)| := by
      simpa only [abs_one] using Real.abs_sinc_le_one (x - y)
    simpa only [one_pow] using sq_le_sq.mpr hs
  · have hx := mem_frequencyBin x
    have hy := mem_frequencyBin y
    have hd : (d.natAbs : ℝ) - 1 ≤ |x - y| := by
      rw [Nat.cast_natAbs]
      push_cast
      have he : (d : ℝ) = (frequencyBin x : ℝ) - (frequencyBin y : ℝ) := by
        simp [d]
      rw [he]
      rcases le_total (frequencyBin x : ℝ) (frequencyBin y : ℝ) with hxy | hyx
      · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith [hx.2, hy.1, neg_abs_le (x - y)]
      · rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        linarith [hx.1, hy.2, le_abs_self (x - y)]
    have hdpos : 0 < (d.natAbs : ℝ) - 1 := by
      have : 1 < d.natAbs := by omega
      exact sub_pos.mpr (by exact_mod_cast this)
    have hxy : x - y ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at hd
      exact (not_lt_of_ge hd) hdpos
    calc
      _ = (|Real.sin (x - y)| / |x - y|) ^ 2 := by
        rw [Real.sinc_of_ne_zero hxy, ← abs_div, sq_abs]
      _ ≤ (1 / ((d.natAbs : ℝ) - 1)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hdpos hd
          |>.trans' (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _))
      _ = _ := by rw [div_pow, one_pow]

private theorem bin_quadratic_le (bins : Finset ℤ) (mass : ℤ → ℝ) :
    (∑ k ∈ bins, ∑ l ∈ bins, mass k * mass l * binKernel (k - l)) ≤
      7 * ∑ k ∈ bins, mass k ^ 2 := by
  have hswap :
      (∑ k ∈ bins, ∑ l ∈ bins, mass l ^ 2 * binKernel (k - l)) =
        ∑ k ∈ bins, ∑ l ∈ bins, mass k ^ 2 * binKernel (k - l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [show l - k = -(k - l) by omega, binKernel_even]
  calc
    _ ≤ ∑ k ∈ bins, ∑ l ∈ bins, (mass k ^ 2 + mass l ^ 2) / 2 * binKernel (k - l) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      refine mul_le_mul_of_nonneg_right ?_ (binKernel_nonneg _)
      nlinarith only [sq_nonneg (mass k - mass l)]
    _ = ∑ k ∈ bins, ∑ l ∈ bins, mass k ^ 2 * binKernel (k - l) := by
      simp only [div_mul_eq_mul_div, ← Finset.sum_div, add_mul, Finset.sum_add_distrib]
      rw [hswap]
      ring
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [← Finset.mul_sum, mul_comm 7]
      exact mul_le_mul_of_nonneg_left (row_le bins k) (sq_nonneg _)

private theorem regroup {I : Type*} (s : Finset I) (b : I → ℤ) (c : I → ℝ)
    (K : ℤ → ℤ → ℝ) :
    let mass := fun k => ∑ i ∈ s with b i = k, c i
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * K (b i) (b j)) =
      ∑ k ∈ s.image b, ∑ l ∈ s.image b, mass k * mass l * K k l := by
  intro mass
  let bins := s.image b
  have hb : ∀ i ∈ s, b i ∈ bins := fun i hi => mem_image_of_mem b hi
  calc
    _ = ∑ k ∈ bins, ∑ i ∈ s with b i = k, ∑ l ∈ bins, ∑ j ∈ s with b j = l,
        c i * c j * K (b i) (b j) := by
      rw [sum_fiberwise_of_maps_to hb]
      refine sum_congr rfl fun i hi => ?_
      exact (sum_fiberwise_of_maps_to hb _).symm
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      rw [sum_comm]
      refine sum_congr rfl fun l hl => ?_
      dsimp only [mass]
      simp only [sum_mul]
      refine sum_congr rfl fun i hi => ?_
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]

/-- The mass of pairs of sampled frequencies whose difference has magnitude at most `r`. -/
private def nearCollisionMass {I : Type*} (s : Finset I) (x c : I → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if |x i - x j| ≤ r then c i * c j else 0

private theorem sinc_sq_ge_quarter {x : ℝ} (hx : |x| ≤ 1) :
    (1 : ℝ) / 4 ≤ Real.sinc x ^ 2 := by
  have hcos := (Real.one_sub_sq_div_two_le_cos (x := x))
  have hsinc : Real.cos x ≤ Real.sinc x :=
    Real.cos_le_sinc (hx.trans_lt (by linarith [Real.pi_gt_three]))
  have hx' : |x| ≤ |(1 : ℝ)| := by simpa only [abs_one] using hx
  have hsq : x ^ 2 ≤ 1 := by simpa only [one_pow] using sq_le_sq.mpr hx'
  have hhalf : (1 : ℝ) / 2 ≤ Real.sinc x := by linarith
  nlinarith only [sq_nonneg (Real.sinc x - 1 / 2), hhalf]

/-- A sinc-squared pair sum is comparable to the weighted collision mass at its frequency scale. -/
private theorem sinc_pair_comparison {I : Type*} (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {r : ℝ} (hr : 0 < r) :
    nearCollisionMass s x c r / 4 ≤
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ∧
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ≤
      7 * nearCollisionMass s x c r := by
  classical
  constructor
  · simp only [nearCollisionMass, sum_div]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    have hnonneg := mul_nonneg (hc i hi) (hc j hj)
    split_ifs with h
    · rw [div_eq_mul_inv, show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
      apply mul_le_mul_of_nonneg_left _ hnonneg
      apply sinc_sq_ge_quarter
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]
      exact h
    · rw [zero_div]
      positivity
  · let b (i : I) := frequencyBin (x i / r)
    let bins := s.image b
    let mass (k : ℤ) := ∑ i ∈ s with b i = k, c i
    have hdiag : (∑ k ∈ bins, mass k ^ 2) ≤ nearCollisionMass s x c r := by
      have hregroup := regroup s b c (fun k l => if k = l then 1 else 0)
      simp only [mul_ite, mul_one, mul_zero] at hregroup
      have heq : (∑ i ∈ s, ∑ j ∈ s, if b i = b j then c i * c j else 0) =
          ∑ k ∈ bins, mass k ^ 2 := by
        simp only [pow_two]
        change _ = ∑ k ∈ s.image b, mass k * mass k
        rw [hregroup]
        apply sum_congr rfl
        intro k hk
        simp [hk, mass]
      rw [← heq]
      refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
      by_cases hij : b i = b j
      · have hx := mem_frequencyBin (x i / r)
        have hy := mem_frequencyBin (x j / r)
        change (x i / r) ∈ Set.Ioc (b i : ℝ) ((b i : ℝ) + 1) at hx
        change (x j / r) ∈ Set.Ioc (b j : ℝ) ((b j : ℝ) + 1) at hy
        rw [← hij] at hy
        have hdist : |x i - x j| ≤ r := by
          have hs : |(x i - x j) / r| ≤ 1 := by
            rw [sub_div]
            exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
          rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul] at hs
          exact hs
        simp [hij, hdist]
      · simp only [hij, ite_false]
        split_ifs
        · exact mul_nonneg (hc i hi) (hc j hj)
        · exact le_rfl
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * binKernel (b i - b j) := by
        refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc i hi) (hc j hj))
        rw [sub_div]
        exact sinc_sq_le_binKernel (x i / r) (x j / r)
      _ = ∑ k ∈ bins, ∑ l ∈ bins, mass k * mass l * binKernel (k - l) :=
        regroup s b c (fun k l => binKernel (k - l))
      _ ≤ 7 * ∑ k ∈ bins, mass k ^ 2 := bin_quadratic_le bins mass
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (by norm_num)

private def intervalMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) : E :=
  (2 * a)⁻¹ • ∫ t in -a..a, f t

private theorem intervalMean_const_mul (a : ℝ) (c : ℂ) (f : ℝ → ℂ) :
    intervalMean a (fun t => c * f t) = c * intervalMean a f := by
  simp only [intervalMean, intervalIntegral.integral_const_mul, Complex.real_smul]
  ring

private theorem intervalMean_sum {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (s : Finset I) (f : I → ℝ → E) (hf : ∀ j ∈ s, Continuous (f j)) :
    intervalMean a (fun t => ∑ j ∈ s, f j t) = ∑ j ∈ s, intervalMean a (f j) := by
  unfold intervalMean
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    smul_sum]

private theorem complexSinc_real (x : ℝ) : complexSinc (x : ℂ) = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [complexSinc_of_ne_zero (Complex.ofReal_ne_zero.mpr hx), Real.sinc_of_ne_zero hx]
    push_cast
    rfl

private theorem intervalMean_mode {a : ℝ} (ha : 0 < a) (v : ℝ) :
    intervalMean a (fun t : ℝ => Complex.exp (Complex.I * (v : ℂ) * (t : ℂ))) =
      (Real.sinc (a * v) : ℂ) := by
  calc
    _ = uniformIntervalFourierLaplace a (v : ℂ) := by
      have hfun : (fun x : ℝ => (uniformIntervalDensity a x : ℂ) *
        Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))) =
          (Icc (-a) a).indicator (fun x : ℝ =>
            ((2 * a : ℝ)⁻¹ : ℂ) * Complex.exp (Complex.I * (v : ℂ) * (x : ℂ))) := by
        funext x
        by_cases hx : x ∈ Icc (-a) a <;> simp [uniformIntervalDensity, hx]
      rw [uniformIntervalFourierLaplace, hfun, integral_indicator measurableSet_Icc,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
        intervalIntegral.integral_const_mul, intervalMean, Complex.real_smul, Complex.ofReal_inv]
    _ = _ := by
      rw [uniformIntervalFourierLaplace_eq_complexSinc ha, ← Complex.ofReal_mul,
        complexSinc_real]

private theorem intervalMean_shifted_mode {a : ℝ} (ha : 0 < a) (v s : ℝ) :
    intervalMean a (fun t : ℝ => Complex.exp (Complex.I * (v : ℂ) * ((s + t : ℝ) : ℂ))) =
      Complex.exp (Complex.I * (v : ℂ) * (s : ℂ)) * (Real.sinc (a * v) : ℂ) := by
  simp only [Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [intervalMean_const_mul, intervalMean_mode ha]

private theorem intervalMean_re (a : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    (intervalMean a f).re = intervalMean a (fun t => (f t).re) := by
  simp only [intervalMean, Complex.smul_re, smul_eq_mul]
  congr 1
  exact (intervalIntegral.intervalIntegral_re (hf.intervalIntegrable _ _)).symm

private theorem intervalMean_cos {a : ℝ} (ha : 0 < a) (v s : ℝ) :
    intervalMean a (fun t => Real.cos (v * (s + t))) =
      Real.cos (v * s) * Real.sinc (a * v) := by
  let mode (t : ℝ) := Complex.exp (Complex.I * (v : ℂ) * ((s + t : ℝ) : ℂ))
  have hcontinuous : Continuous mode := by unfold mode; fun_prop
  have hmean := congrArg Complex.re (intervalMean_shifted_mode ha v s)
  change (intervalMean a mode).re =
    (Complex.exp (Complex.I * (v : ℂ) * (s : ℂ)) * (Real.sinc (a * v) : ℂ)).re at hmean
  rw [intervalMean_re a mode hcontinuous] at hmean
  have hmode (t : ℝ) : (mode t).re = Real.cos (v * (s + t)) := by
    unfold mode
    rw [show Complex.I * (v : ℂ) * ((s + t : ℝ) : ℂ) =
      ((v * (s + t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re _
  rw [show (fun t => (mode t).re) = (fun t => Real.cos (v * (s + t))) from funext hmode]
    at hmean
  rw [hmean, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    show Complex.I * (v : ℂ) * (s : ℂ) =
      ((v * s : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]

/-- Two successive averages over the same centered interval, with their sum added to the center. -/
def doubleMean (a : ℝ) (f : ℝ → ℝ) (center : ℝ) : ℝ :=
  intervalMean a (fun u => intervalMean a (fun t => f (center + u + t)))

private theorem doubleMean_modes {I : Type*} (s : Finset I) (c v : I → ℝ)
    {a : ℝ} (ha : 0 < a) (center : ℝ) :
    doubleMean a (fun t => ∑ i ∈ s, c i * Real.cos (v i * t)) center =
      ∑ i ∈ s, c i * (Real.cos (v i * center) * Real.sinc (a * v i) ^ 2) := by
  have hm (u : ℝ) (i : I) :
      intervalMean a (fun t => c i * Real.cos (v i * (center + u + t))) =
        c i * (Real.cos (v i * (center + u)) * Real.sinc (a * v i)) := by
    have hmul : ∀ f : ℝ → ℝ, intervalMean a (fun t => c i * f t) = c i * intervalMean a f := by
      intro f
      simp only [intervalMean, intervalIntegral.integral_const_mul, smul_eq_mul]
      ring
    rw [hmul, intervalMean_cos ha]
  unfold doubleMean
  have hind (u : ℝ) : ∀ i ∈ s, Continuous (fun t => c i * Real.cos (v i * (center + u + t))) :=
    fun i _ => by fun_prop
  simp_rw [intervalMean_sum a s _ (hind _), hm]
  rw [intervalMean_sum a s _ (fun i _ => by fun_prop)]
  refine sum_congr rfl fun i _ => ?_
  calc
    _ = intervalMean a (fun t => c i * Real.cos (v i * (center + t))) * Real.sinc (a * v i) := by
      simp only [intervalMean, ← mul_assoc, intervalIntegral.integral_mul_const, smul_eq_mul]
    _ = _ := by
      have hzero := hm 0 i
      simp only [add_zero] at hzero
      rw [hzero, sq, mul_assoc, mul_assoc]

private def pairCosineScore {I : Type*} (s : Finset I) (x c : I → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.cos ((x i - x j) * t)

private theorem doubleMean_pairCosineScore {I : Type*} (s : Finset I) (x c : I → ℝ)
    {a : ℝ} (ha : 0 < a) (center : ℝ) :
    doubleMean a (pairCosineScore s x c) center =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (Real.cos ((x i - x j) * center) * Real.sinc (a * (x i - x j)) ^ 2) := by
  unfold pairCosineScore
  simpa only [Finset.sum_product] using
    doubleMean_modes (s ×ˢ s) (fun ij => c ij.1 * c ij.2)
      (fun ij => x ij.1 - x ij.2) ha center

private theorem doubleMean_pair_comparison {I : Type*} (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {a : ℝ} (ha : 0 < a) (center : ℝ) :
    nearCollisionMass s x c a⁻¹ / 4 ≤ doubleMean a (pairCosineScore s x c) 0 ∧
      doubleMean a (pairCosineScore s x c) center ≤ 7 * nearCollisionMass s x c a⁻¹ := by
  have h := sinc_pair_comparison s x c hc (inv_pos.mpr ha)
  simp only [div_inv_eq_mul, mul_comm _ a] at h
  rw [doubleMean_pairCosineScore s x c ha 0, doubleMean_pairCosineScore s x c ha center]
  constructor
  · simpa only [mul_zero, Real.cos_zero, one_mul] using h.1
  · refine le_trans ?_ h.2
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc i hi) (hc j hj))
    exact mul_le_of_le_one_left (sq_nonneg _) (Real.cos_le_one _)

private theorem continuous_mean_pair {I : Type*} (s : Finset I) (x c : I → ℝ)
    {a : ℝ} (ha : 0 < a) (center : ℝ) :
    Continuous (fun u => intervalMean a (fun t => pairCosineScore s x c (center + u + t))) := by
  have hf (u : ℝ) :
      intervalMean a (fun t => pairCosineScore s x c (center + u + t)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j *
        (Real.cos ((x i - x j) * (center + u)) * Real.sinc (a * (x i - x j))) := by
    unfold pairCosineScore
    rw [intervalMean_sum a s _ (fun i _ => continuous_finsetSum _ (fun j _ => by fun_prop))]
    refine sum_congr rfl fun i _ => ?_
    rw [intervalMean_sum a s _ (fun j _ => by fun_prop)]
    refine sum_congr rfl fun j _ => ?_
    have hm (f : ℝ → ℝ) : intervalMean a (fun t => (c i * c j) * f t) =
        (c i * c j) * intervalMean a f := by
      simp only [intervalMean, intervalIntegral.integral_const_mul, smul_eq_mul]
      ring
    rw [hm, intervalMean_cos ha]
  simp_rw [hf]
  exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => by fun_prop))

private theorem const_le_intervalMean {a q : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hf : Continuous f) (h : ∀ t ∈ Ioo (-a) a, q ≤ f t) :
    q ≤ intervalMean a f := by
  have hs : 0 ≤ (2 * a)⁻¹ := by positivity
  have hb : -a ≤ a := by linarith
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) hb
    (continuous_const.intervalIntegrable (-a) a) (hf.intervalIntegrable (-a) a) h
  unfold intervalMean
  rw [smul_eq_mul]
  calc
    q = (2 * a)⁻¹ * (∫ t in -a..a, q) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, show a - -a = 2 * a by ring]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hm hs

private theorem exists_small_grid {I K : Type*} [Fintype K] (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {a : ℝ} (ha : 0 < a) (center q : ℝ) (grid : K → ℝ)
    (hbudget : 7 * (Fintype.card K : ℝ) * nearCollisionMass s x c a⁻¹ < q) :
    ∃ b ∈ Ioo (center - 2 * a) (center + 2 * a),
      ∑ k, pairCosineScore s x c (b + grid k) < q := by
  let F (b : ℝ) : ℝ := ∑ k, pairCosineScore s x c (b + grid k)
  let inner (u : ℝ) : ℝ := intervalMean a (fun t => F (center + u + t))
  have hinner (u : ℝ) :
      inner u = ∑ k, intervalMean a (fun t => pairCosineScore s x c (center + grid k + u + t)) := by
    unfold inner F
    rw [intervalMean_sum a univ _]
    · apply sum_congr rfl
      intro k _
      congr 1
      funext t
      congr 1
      ring
    · intro k _
      unfold pairCosineScore
      exact continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => by fun_prop))
  have hfun : inner = fun u => ∑ k, intervalMean a
      (fun t => pairCosineScore s x c (center + grid k + u + t)) := funext hinner
  have hcontinuous : Continuous inner := by
    rw [hfun]
    exact continuous_finsetSum _ (fun k _ => continuous_mean_pair s x c ha (center + grid k))
  have hupper : intervalMean a inner < q := by
    rw [hfun]
    rw [intervalMean_sum a univ _ (fun k _ => continuous_mean_pair s x c ha (center + grid k))]
    change (∑ k, doubleMean a (pairCosineScore s x c) (center + grid k)) < q
    have hpoint := sum_le_sum (s := (univ : Finset K)) (fun k _ =>
      (doubleMean_pair_comparison s x c hc ha (center + grid k)).2)
    simp only [sum_const, card_univ, nsmul_eq_mul] at hpoint
    exact hpoint.trans_lt (by convert hbudget using 1; ring)
  by_contra! h
  have hlong : q ≤ intervalMean a inner := by
    apply const_le_intervalMean ha hcontinuous
    intro u hu
    apply const_le_intervalMean ha
    · unfold F pairCosineScore
      exact continuous_finsetSum _ (fun k _ => continuous_finsetSum _ (fun i _ =>
        continuous_finsetSum _ (fun j _ => by fun_prop)))
    · exact fun t ht => h (center + u + t) ⟨by linarith [hu.1, ht.1], by linarith [hu.2, ht.2]⟩
  exact (not_lt_of_ge hlong) hupper

/-- Weighted near-collisions of degree-`p` sums of the input frequencies. -/
def tailCollisionMass {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) (r : ℝ) : ℝ :=
  nearCollisionMass (piAntidiag univ p) (monomialFrequency g) (monomialWeight w) r

private theorem monomialWeight_nonneg {J : Type*} [Fintype J] (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (m : J → ℕ) : 0 ≤ monomialWeight w m := by
  exact mul_nonneg (Nat.cast_nonneg _) (prod_nonneg (fun j _ => pow_nonneg (hw j) _))

private theorem phase_re (g t : ℝ) : (phase g t).re = Real.cos (g * t) := by
  unfold phase
  rw [show (g : ℂ) * Complex.I * (t : ℂ) = ((g * t : ℝ) : ℂ) * Complex.I by
    push_cast
    ring, Complex.exp_ofReal_mul_I_re]

private theorem moment_eq_pair {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) (t : ℝ) :
    ‖complexScore g w t‖ ^ (2 * p) =
      pairCosineScore (piAntidiag univ p) (monomialFrequency g) (monomialWeight w) t := by
  have hneg (n : J → ℕ) : monomialFrequency (fun j => -g j) n = -monomialFrequency g n := by
    simp [monomialFrequency, mul_neg, sum_neg_distrib]
  have h := congrArg Complex.re (score_even_expansion g w t p)
  simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, phase_re, hneg, ← sub_eq_add_neg] at h
  exact h

/-- The two uniform averages at scale `L` are controlled by degree-`p` near-collisions. -/
theorem tail_moment_comparison {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ) {L : ℝ} (hL : 0 < L) (center : ℝ) :
    tailCollisionMass g w p (2 / L) / 4 ≤
      doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) 0 ∧
    doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) center ≤
      7 * tailCollisionMass g w p (2 / L) := by
  simp_rw [moment_eq_pair, tailCollisionMass]
  have hscale : (L / 2)⁻¹ = 2 / L := by rw [inv_div]
  rw [← hscale]
  exact doubleMean_pair_comparison _ _ _ (fun m _ => monomialWeight_nonneg w hw m)
    (by positivity) center

/-- The near-collision budget guarantees a closed window with a start in a bounded open interval. -/
theorem exists_bounded_tail_window {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ)
    {L H h δ : ℝ} (hL : 0 < L) (hh : 0 < h) (hδ : 0 ≤ δ)
    (hbudget : 7 * ((⌊H / h⌋₊ : ℝ) + 1) * tailCollisionMass g w p (2 / L) < δ ^ (2 * p))
    (A : ℝ) :
    ∃ b ∈ Ioo A (A + 2 * L), ∀ t ∈ Icc b (b + H),
      ∑ j, w j * Real.sin (g j * t) < δ + h * ∑ j, w j * |g j| := by
  let K := Fin (⌊H / h⌋₊ + 1)
  let grid (k : K) : ℝ := (k : ℕ) * h
  have hcard : (Fintype.card K : ℝ) = (⌊H / h⌋₊ : ℝ) + 1 := by simp [K]
  have hscale : (L / 2)⁻¹ = 2 / L := by rw [inv_div]
  have hgridBudget : 7 * (Fintype.card K : ℝ) *
      nearCollisionMass (piAntidiag univ p) (monomialFrequency g) (monomialWeight w) (L / 2)⁻¹ <
        δ ^ (2 * p) := by simpa only [hcard, hscale, tailCollisionMass] using hbudget
  obtain ⟨b, hb, hsmall⟩ := exists_small_grid _ _ _ (fun m _ => monomialWeight_nonneg w hw m)
    (by positivity) (A + L) _ grid hgridBudget
  simp_rw [← moment_eq_pair g w p] at hsmall
  have hgrid (k : K) : ‖complexScore g w (b + grid k)‖ < δ := by
    by_contra! h
    have hterm := pow_le_pow_left₀ hδ h (2 * p)
    have hsum := single_le_sum (s := (univ : Finset K))
      (fun j _ => pow_nonneg (norm_nonneg (complexScore g w (b + grid j))) (2 * p)) (mem_univ k)
    exact (not_lt_of_ge (hterm.trans hsum)) hsmall
  refine ⟨b, ⟨by linarith [hb.1], by linarith [hb.2]⟩, fun t ht => ?_⟩
  have ht' : t - b ∈ Icc (0 : ℝ) H :=
    ⟨sub_nonneg.mpr ht.1, (sub_le_iff_le_add).mpr (by linarith [ht.2])⟩
  obtain ⟨k, hk⟩ := floor_grid_cover hh ht'
  have hk' : |t - (b + grid k)| ≤ h := by simpa only [grid, sub_sub] using hk
  let weight (j : J) : ℝ≥0 := ⟨w j, hw j⟩
  have hchange := sine_score_change univ g (fun _ : J => 0) weight t (b + grid k)
  simp only [zero_add] at hchange
  change (∑ j, w j * Real.sin (g j * t)) -
      (∑ j, w j * Real.sin (g j * (b + grid k))) ≤
        (∑ j, w j * |g j|) * |t - (b + grid k)| at hchange
  have hstep := hchange.trans (mul_le_mul_of_nonneg_left hk'
    (sum_nonneg (fun j _ => mul_nonneg (hw j) (abs_nonneg _))))
  have hnode : (∑ j, w j * Real.sin (g j * (b + grid k))) < δ := by
    rw [← im_complexScore]
    exact (Complex.im_le_norm _).trans_lt (hgrid k)
  linarith only [hstep, hnode, mul_comm h (∑ j, w j * |g j|)]

#print axioms tail_moment_comparison
#print axioms exists_bounded_tail_window

end D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/- GID: D5/S3/Fourier/Concentration/FiniteSincCollisionMoment
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FiniteSincCollisionMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sinc-squared moments are controlled by weighted near-collisions. -/

import D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder.SpectralSampling
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Control of a finite weighted sinc matrix at the scale of its near-collisions. -/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory Set
open scoped NNReal
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSineMissingWindow (sine_score_change)
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
    Summable binKernel ∧ (∑' d : ℤ, binKernel d) = 3 + Real.pi ^ 2 / 3 := by
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
  linarith

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

/-- The mass of pairs of sampled frequencies whose difference has magnitude at most `r`. -/
def nearCollisionMass {I : Type*} (s : Finset I) (x c : I → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, if |x i - x j| ≤ r then c i * c j else 0

/-- The sum of squared masses of bins of diameter at most `r` counts only near-collisions. -/
theorem sum_bin_mass_sq_le_nearCollisionMass {I : Type*} (s : Finset I) (x c : I → ℝ)
    (b : I → ℤ) (r : ℝ) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, b i = b j → |x i - x j| ≤ r) :
    (∑ k ∈ s.image b, (∑ i ∈ s with b i = k, c i) ^ 2) ≤ nearCollisionMass s x c r := by
  let mass (k : ℤ) := ∑ i ∈ s with b i = k, c i
  have hregroup := regroup_binEnergy s b c (fun k l => if k = l then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hregroup
  have heq : (∑ i ∈ s, ∑ j ∈ s, if b i = b j then c i * c j else 0) =
      ∑ k ∈ s.image b, mass k ^ 2 := by
    simp only [pow_two]
    change _ = ∑ k ∈ s.image b, mass k * mass k
    rw [hregroup]
    apply sum_congr rfl
    intro k hk
    simp [hk, mass]
  change (∑ k ∈ s.image b, mass k ^ 2) ≤ _
  rw [← heq]
  refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
  by_cases hij : b i = b j
  · simp [hij, hsame i hi j hj hij]
  · simp only [hij, ite_false]
    split_ifs
    · exact mul_nonneg (hc i hi) (hc j hj)
    · exact le_rfl

private theorem sin_one_sq_le_sinc_sq {x : ℝ} (hx : |x| ≤ 1) :
    Real.sin 1 ^ 2 ≤ Real.sinc x ^ 2 := by
  have hpi : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hsin : 0 ≤ Real.sin 1 := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num) hpi.le
  apply pow_le_pow_left₀ hsin _ 2
  have hsymm : Real.sinc |x| = Real.sinc x := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, Real.sinc_neg]
  rw [← hsymm]
  by_cases hzero : |x| = 0
  · rw [hzero, Real.sinc_zero]
    exact Real.sin_le_one 1
  · have hpos : 0 < |x| := lt_of_le_of_ne (abs_nonneg x) (Ne.symm hzero)
    rw [Real.sinc_of_ne_zero hzero, le_div_iff₀ hpos]
    have hconc := strictConcaveOn_sin_Icc.concaveOn.2
      (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show (1 : ℝ) ∈ Icc 0 Real.pi from ⟨by norm_num, hpi.le⟩)
      (sub_nonneg.mpr hx) (abs_nonneg x) (by ring : (1 - |x|) + |x| = 1)
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_mul, Real.sin_zero, mul_comm]
      using hconc

/-- A sinc-squared pair sum is comparable to the weighted collision mass at its frequency scale. -/
private theorem sinc_pair_comparison {I : Type*} (s : Finset I) (x c : I → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {r : ℝ} (hr : 0 < r) :
    nearCollisionMass s x c r * Real.sin 1 ^ 2 ≤
      (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ∧
    (∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.sinc ((x i - x j) / r) ^ 2) ≤
      (3 + Real.pi ^ 2 / 3) * nearCollisionMass s x c r := by
  classical
  constructor
  · simp only [nearCollisionMass, Finset.sum_mul]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    have hnonneg := mul_nonneg (hc i hi) (hc j hj)
    split_ifs with h
    · apply mul_le_mul_of_nonneg_left _ hnonneg
      apply sin_one_sq_le_sinc_sq
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul]
      exact h
    · rw [zero_mul]
      positivity
  · let b (i : I) := frequencyBin (x i / r)
    let bins := s.image b
    let mass (k : ℤ) := ∑ i ∈ s with b i = k, c i
    have hdiag : (∑ k ∈ bins, mass k ^ 2) ≤ nearCollisionMass s x c r := by
      apply sum_bin_mass_sq_le_nearCollisionMass s x c b r hc
      intro i _ j _ hij
      have hx := mem_frequencyBin (x i / r)
      have hy := mem_frequencyBin (x j / r)
      change (x i / r) ∈ Set.Ioc (b i : ℝ) ((b i : ℝ) + 1) at hx
      change (x j / r) ∈ Set.Ioc (b j : ℝ) ((b j : ℝ) + 1) at hy
      rw [← hij] at hy
      have hs : |(x i - x j) / r| ≤ 1 := by
        rw [sub_div]
        exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr, one_mul] at hs
      exact hs
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * binKernel (b i - b j) := by
        refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc i hi) (hc j hj))
        rw [sub_div]
        exact sinc_sq_le_binKernel (x i / r) (x j / r)
      _ = ∑ k ∈ bins, ∑ l ∈ bins, mass k * mass l * binKernel (k - l) :=
        regroup_binEnergy s b c (fun k l => binKernel (k - l))
      _ ≤ (3 + Real.pi ^ 2 / 3) * ∑ k ∈ bins, mass k ^ 2 := by
        rw [← binKernel_sum.2]
        exact binEnergy_le binKernel binKernel_nonneg binKernel_even binKernel_sum.1 bins mass
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiag (by positivity)

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

private theorem intervalMean_mode {a : ℝ} (ha : 0 < a) (v : ℝ) :
    intervalMean a (fun t : ℝ => Complex.exp (Complex.I * (v : ℂ) * (t : ℂ))) =
      (Real.sinc (a * v) : ℂ) := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  by_cases hv : v = 0
  · subst v
    simp [intervalMean, intervalIntegral.integral_const, show a - -a = 2 * a by ring]
    field_simp
  · have hphase : (fun t : ℝ => Complex.exp (Complex.I * (v : ℂ) * (t : ℂ))) =
        fun t : ℝ => Complex.exp (↑(v * t) * Complex.I) := by
      funext t
      push_cast
      congr 1
      ring
    rw [hphase, intervalMean, intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) hv, mul_neg,
      integral_exp_mul_I_eq_sinc]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
    rw [mul_comm v a]
    push_cast
    field_simp

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
    nearCollisionMass s x c a⁻¹ * Real.sin 1 ^ 2 ≤ doubleMean a (pairCosineScore s x c) 0 ∧
      doubleMean a (pairCosineScore s x c) center ≤ doubleMean a (pairCosineScore s x c) 0 ∧
    doubleMean a (pairCosineScore s x c) 0 ≤ (3 + Real.pi ^ 2 / 3) * nearCollisionMass s x c a⁻¹ := by
  have h := sinc_pair_comparison s x c hc (inv_pos.mpr ha)
  simp only [div_inv_eq_mul, mul_comm _ a] at h
  rw [doubleMean_pairCosineScore s x c ha 0, doubleMean_pairCosineScore s x c ha center]
  constructor
  · simpa only [mul_zero, Real.cos_zero, one_mul] using h.1
  · refine ⟨?_, by simpa only [mul_zero, Real.cos_zero, one_mul] using h.2⟩
    simp only [mul_zero, Real.cos_zero, one_mul]
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
    (hbudget : (3 + Real.pi ^ 2 / 3) * (Fintype.card K : ℝ) * nearCollisionMass s x c a⁻¹ < q) :
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
      let h := doubleMean_pair_comparison s x c hc ha (center + grid k)
      h.2.1.trans h.2.2)
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

theorem monomialWeight_nonneg {J : Type*} [Fintype J] (w : J → ℝ)
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
    tailCollisionMass g w p (2 / L) * Real.sin 1 ^ 2 ≤
      doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) 0 ∧
    doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) center ≤
      doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) 0 ∧
    doubleMean (L / 2) (fun t => ‖complexScore g w t‖ ^ (2 * p)) 0 ≤
      (3 + Real.pi ^ 2 / 3) * tailCollisionMass g w p (2 / L) := by
  simp_rw [moment_eq_pair, tailCollisionMass]
  have hscale : (L / 2)⁻¹ = 2 / L := by rw [inv_div]
  rw [← hscale]
  exact doubleMean_pair_comparison _ _ _ (fun m _ => monomialWeight_nonneg w hw m)
    (by positivity) center

private theorem midpoint_grid_cover {N : ℕ} (hN : 0 < N) {H u : ℝ}
    (hu : u ∈ Icc 0 H) :
    ∃ k : Fin N, |u - ((k : ℕ) + (1 / 2 : ℝ)) * (H / N)| ≤ H / N / 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hH : 0 ≤ H := hu.1.trans hu.2
  rcases hH.eq_or_lt with hzero | hpos
  · have hu0 : u = 0 := by linarith [hu.1, hu.2]
    exact ⟨⟨0, hN⟩, by simp [← hzero, hu0]⟩
  let e := H / (N : ℝ)
  have he : 0 < e := div_pos hpos hNreal
  have hEnd : (N : ℝ) * e = H := by dsimp [e]; field_simp
  by_cases hlast : u = H
  · let k : Fin N := ⟨N - 1, by omega⟩
    have hk : ((k : ℕ) : ℝ) = (N : ℝ) - 1 := by
      change ((N - 1 : ℕ) : ℝ) = _
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    refine ⟨k, ?_⟩
    change |u - ((k : ℕ) + (1 / 2 : ℝ)) * e| ≤ e / 2
    rw [hlast, hk, ← hEnd]
    rw [show (N : ℝ) * e - ((N : ℝ) - 1 + 1 / 2) * e = e / 2 by ring]
    exact le_of_eq (abs_of_nonneg (by positivity))
  · have hratio : u / e < (N : ℝ) := (div_lt_iff₀ he).2
      (by rw [hEnd]; exact lt_of_le_of_ne hu.2 hlast)
    have hratio0 : 0 ≤ u / e := div_nonneg hu.1 he.le
    have hkBound : ⌊u / e⌋₊ < N := by
      by_contra! h
      exact hratio.not_ge ((Nat.le_floor_iff hratio0).1 h)
    let k : Fin N := ⟨⌊u / e⌋₊, hkBound⟩
    have hlow : ((k : ℕ) : ℝ) * e ≤ u :=
      (le_div_iff₀ he).1 (Nat.floor_le hratio0)
    have hhigh : u < (((k : ℕ) : ℝ) + 1) * e :=
      (div_lt_iff₀ he).1 (Nat.lt_floor_add_one _)
    refine ⟨k, abs_le.2 ⟨?_, ?_⟩⟩
    · change -(e / 2) ≤ u - ((k : ℕ) + (1 / 2 : ℝ)) * e
      linarith
    · change u - ((k : ℕ) + (1 / 2 : ℝ)) * e ≤ e / 2
      linarith

/-- The near-collision budget guarantees a closed window with a start in a bounded open interval. -/
theorem exists_bounded_tail_window {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (p : ℕ)
    {N : ℕ} {L H δ : ℝ} (hL : 0 < L) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hbudget : (3 + Real.pi ^ 2 / 3) * (N : ℝ) *
      tailCollisionMass g w p (2 / L) < δ ^ (2 * p))
    (A : ℝ) :
    ∃ b ∈ Ioo A (A + 2 * L), ∀ t ∈ Icc b (b + H),
      |∑ j, w j * Real.sin (g j * t)| < δ + (H / N / 2) * ∑ j, w j * |g j| := by
  let K := Fin N
  let grid (k : K) : ℝ := ((k : ℕ) + (1 / 2 : ℝ)) * (H / N)
  have hcard : (Fintype.card K : ℝ) = N := by simp [K]
  have hscale : (L / 2)⁻¹ = 2 / L := by rw [inv_div]
  have hgridBudget : (3 + Real.pi ^ 2 / 3) * (Fintype.card K : ℝ) *
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
  obtain ⟨k, hk⟩ := midpoint_grid_cover hN ht'
  have hk' : |t - (b + grid k)| ≤ H / N / 2 := by
    simpa only [grid, sub_sub] using hk
  let weight (j : J) : ℝ≥0 := ⟨w j, hw j⟩
  have hchange := sine_score_change univ g (fun _ : J => 0) weight t (b + grid k)
  simp only [zero_add] at hchange
  change (∑ j, w j * Real.sin (g j * t)) -
      (∑ j, w j * Real.sin (g j * (b + grid k))) ≤
        (∑ j, w j * |g j|) * |t - (b + grid k)| at hchange
  have hreverse := sine_score_change univ g (fun _ : J => 0) weight (b + grid k) t
  simp only [zero_add, abs_sub_comm (b + grid k) t] at hreverse
  change (∑ j, w j * Real.sin (g j * (b + grid k))) -
      (∑ j, w j * Real.sin (g j * t)) ≤
        (∑ j, w j * |g j|) * |t - (b + grid k)| at hreverse
  have habs : |(∑ j, w j * Real.sin (g j * t)) -
      (∑ j, w j * Real.sin (g j * (b + grid k)))| ≤
        (∑ j, w j * |g j|) * |t - (b + grid k)| := by
    rw [abs_sub_le_iff]
    exact ⟨hchange, hreverse⟩
  have hstep := habs.trans (mul_le_mul_of_nonneg_left hk'
    (sum_nonneg (fun j _ => mul_nonneg (hw j) (abs_nonneg _))))
  have hnode : |∑ j, w j * Real.sin (g j * (b + grid k))| < δ := by
    rw [← im_complexScore]
    exact (Complex.abs_im_le_norm _).trans_lt (hgrid k)
  have htriangle := abs_add_le ((∑ j, w j * Real.sin (g j * t)) -
    (∑ j, w j * Real.sin (g j * (b + grid k)))) (∑ j, w j * Real.sin (g j * (b + grid k)))
  rw [sub_add_cancel] at htriangle
  linarith only [htriangle, hstep, hnode, mul_comm (H / N / 2) (∑ j, w j * |g j|)]

#print axioms tail_moment_comparison
#print axioms exists_bounded_tail_window

end D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

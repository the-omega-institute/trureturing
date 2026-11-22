/- GID: D5/S3/Analytic/PetzDyadicEscapeSpectrum
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzDyadicEscapeSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coalescing binomial rate laws obstruct inversion of the diagonal Petz scale curve. -/

import D5.S3.Analytic.PetzDyadicStripEnergy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! # Inversion obstruction for the finite Petz escape profile

The weighted diagonal of the canonical strip Gram yields the finite rate
profile. Its Laplace readout and derivative admit exact finite moment formulas.
The even and odd parts of a coalescing binomial law have equal mass and mean.
Their transport distance is at least the rate spacing, while the difference
of their profiles is of order `spacing ^ (2 * m - 1)` uniformly at positive scales.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Analytic.PetzDyadicEscapeSpectrum

open PetzStripGramRemainder (stripGram logistic)
open private cothFactor from D5.S3.Analytic.PetzStripGramRemainder

noncomputable section

private theorem stripGram_diagonal (x : ℝ) :
    stripGram x x = Real.exp x - 1 - x := by
  unfold stripGram
  simp only [sub_self, logistic, cothFactor, ite_true, mul_one, ← Real.exp_add]
  rw [show x / 2 + x / 2 = x by ring]
  ring

/-- The weighted diagonal strip Gram divided by the scale, with value zero
at scale zero. -/
def rateProfile {ι : Type*} [Fintype ι] (rates weights : ι → ℝ) (s : ℝ) : ℝ :=
  (∑ i, weights i * stripGram (-(s * rates i)) (-(s * rates i))) / s

private theorem stripGram_diagonal_sub_le {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |stripGram x x - stripGram y y| ≤ |x - y| := by
  let f : ℝ → ℝ := fun z => Real.exp z - 1 - z
  have hd (z : ℝ) : HasDerivAt f (Real.exp z - 1) z :=
    ((Real.hasDerivAt_exp z).sub_const 1).sub (hasDerivAt_id z)
  have hb (z : ℝ) (hz : z ∈ Set.Iic (0 : ℝ)) : ‖deriv f z‖ ≤ 1 := by
    have hsign : Real.exp z - 1 ≤ 0 := sub_nonpos.mpr (Real.exp_le_one_iff.mpr hz)
    rw [(hd z).deriv, Real.norm_eq_abs, abs_of_nonpos hsign]
    linarith [Real.exp_pos z]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hd z).differentiableAt) hb (convex_Iic (0 : ℝ))
    (show y ∈ Set.Iic (0 : ℝ) from hy) (show x ∈ Set.Iic (0 : ℝ) from hx)
  simpa only [stripGram_diagonal, Real.norm_eq_abs, one_mul, f] using h

/-- At cutoff `s * eps`, the diagonal contribution of the logarithmic ratios
of the escape eigenvalues differs from the finite rate profile by an explicit
error independent of the scale `s`. -/
theorem diagonal_log_ratio_profile_error {ι : Type*} [Fintype ι]
    (rates weights : ι → ℝ) {eps s : ℝ} (heps : 0 < eps) (hs : 0 < s)
    (hrates : ∀ i, 0 ≤ rates i) (hweights : ∀ i, 0 < weights i)
    (hlog : ∀ i, Real.log (Real.exp (-(rates i / eps))) -
      Real.log (eps * weights i) ≤ 0) :
    let frequency (i : ι) :=
      (s * eps) * (Real.log (Real.exp (-(rates i / eps))) - Real.log (eps * weights i))
    |(∑ i, weights i * stripGram (frequency i) (frequency i)) / s -
      rateProfile rates weights s| ≤ eps * ∑ i, weights i * |Real.log (eps * weights i)| := by
  let frequency (i : ι) :=
    (s * eps) * (Real.log (Real.exp (-(rates i / eps))) - Real.log (eps * weights i))
  change |(∑ i, weights i * stripGram (frequency i) (frequency i)) / s -
    rateProfile rates weights s| ≤ _
  rw [rateProfile, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ ∑ i, |weights i * stripGram (frequency i) (frequency i) -
        weights i * stripGram (-(s * rates i)) (-(s * rates i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, weights i * ((s * eps) * |Real.log (eps * weights i)|) := by
      apply Finset.sum_le_sum
      intro i _
      have hx : frequency i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs.le heps.le) (hlog i)
      have hy : -(s * rates i) ≤ 0 := neg_nonpos.mpr (mul_nonneg hs.le (hrates i))
      have hshift : frequency i - -(s * rates i) = -(s * eps) * Real.log (eps * weights i) := by
        dsimp only [frequency]
        rw [Real.log_exp]
        field_simp [heps.ne']
        ring
      have hLip := stripGram_diagonal_sub_le hx hy
      rw [hshift, abs_mul, abs_neg, abs_of_pos (mul_pos hs heps)] at hLip
      rw [← mul_sub, abs_mul, abs_of_pos (hweights i)]
      exact mul_le_mul_of_nonneg_left hLip (hweights i).le
    _ = _ := by
      rw [show eps * (∑ i, weights i * |Real.log (eps * weights i)|) * s =
        (s * eps) * ∑ i, weights i * |Real.log (eps * weights i)| by ring,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The exact rate moments with the exponential scale tilt. -/
def tiltedRateMoment {ι : Type*} [Fintype ι]
    (rates weights : ι → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i, weights i * rates i ^ k * Real.exp (-(s * rates i))

/-- The un-tilted finite rate moment, with mass at degree zero and mean
at degree one for normalized laws. -/
def rateMoment {ι : Type*} [Fintype ι] (rates weights : ι → ℝ) (k : ℕ) : ℝ :=
  tiltedRateMoment rates weights k 0

theorem rateMoment_eq_sum {ι : Type*} [Fintype ι] (rates weights : ι → ℝ) (k : ℕ) :
    rateMoment rates weights k = ∑ i, weights i * rates i ^ k := by
  simp [rateMoment, tiltedRateMoment]

/-- An exact scale observation is the Laplace value after the affine
contributions from mass and mean are included. -/
theorem rateProfile_eq_laplace {ι : Type*} [Fintype ι]
    (rates weights : ι → ℝ) (s : ℝ) :
    rateProfile rates weights s =
      (tiltedRateMoment rates weights 0 s - rateMoment rates weights 0 +
        s * rateMoment rates weights 1) / s := by
  rw [rateProfile, rateMoment_eq_sum, rateMoment_eq_sum]
  apply congrArg (fun a : ℝ => a / s)
  simp only [stripGram_diagonal, sub_neg_eq_add, tiltedRateMoment, pow_zero, pow_one, mul_one]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Differentiating a tilted rate moment raises its degree with a minus sign.
At scale zero the successive derivatives therefore give signed rate moments. -/
theorem hasDerivAt_tiltedRateMoment {ι : Type*} [Fintype ι]
    (rates weights : ι → ℝ) (k : ℕ) (s : ℝ) :
    HasDerivAt (tiltedRateMoment rates weights k)
      (-tiltedRateMoment rates weights (k + 1) s) s := by
  unfold tiltedRateMoment
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  have hneg : HasDerivAt (fun t => -(t * rates i)) (-rates i) s := by
    simpa only [mul_neg] using (hasDerivAt_mul_const (x := s) (-rates i))
  convert hneg.exp.const_mul (weights i * rates i ^ k) using 1
  rw [pow_succ]
  ring

/-- The exact derivative of the finite Petz profile at positive scales
and, algebraically, at every nonzero scale. -/
theorem hasDerivAt_rateProfile {ι : Type*} [Fintype ι]
    (rates weights : ι → ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (rateProfile rates weights)
      (∑ i, weights i * ((1 - (1 + s * rates i) * Real.exp (-(s * rates i))) / s ^ 2)) s := by
  have hprofile : rateProfile rates weights = fun t =>
      ∑ i, weights i * ((Real.exp (-(t * rates i)) - 1 + t * rates i) / t) := by
    funext t
    simp only [rateProfile, stripGram_diagonal, sub_neg_eq_add, Finset.sum_div, mul_div_assoc]
  rw [hprofile]
  apply HasDerivAt.fun_sum
  intro i _
  have hrate := hasDerivAt_mul_const (x := s) (rates i)
  have hneg : HasDerivAt (fun t => -(t * rates i)) (-rates i) s := by
    simpa only [mul_neg] using (hasDerivAt_mul_const (x := s) (-rates i))
  have hnum := (hneg.exp.sub_const 1).fun_add hrate
  have h := (hnum.fun_div (hasDerivAt_id' s) hs).const_mul (weights i)
  convert h using 1
  ring

/-- Coalescing rates with grid spacing `eta`. -/
def binomialRate (n : ℕ) (r0 eta : ℝ) (j : Fin (n + 1)) : ℝ :=
  r0 + (j.val : ℝ) * eta

private def binomialWeight (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  (n.choose j.val : ℝ) / (2 : ℝ) ^ (n - 1)

/-- Normalized even part of the alternating binomial weights. -/
def evenBinomial (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  if Even j.val then binomialWeight n j else 0

/-- Normalized odd part of the alternating binomial weights. -/
def oddBinomial (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  if Odd j.val then binomialWeight n j else 0

private theorem binomialWeight_pos (n : ℕ) (j : Fin (n + 1)) :
    0 < binomialWeight n j := by
  have hj : 0 < n.choose j.val := Nat.choose_pos (Nat.lt_succ_iff.mp j.isLt)
  have hcast : (0 : ℝ) < (n.choose j.val : ℝ) := by exact_mod_cast hj
  exact div_pos hcast (by positivity)

private theorem evenBinomial_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ evenBinomial n j := by
  unfold evenBinomial
  split_ifs
  · exact (binomialWeight_pos n j).le
  · exact le_rfl

private theorem oddBinomial_nonneg (n : ℕ) (j : Fin (n + 1)) :
    0 ≤ oddBinomial n j := by
  unfold oddBinomial
  split_ifs
  · exact (binomialWeight_pos n j).le
  · exact le_rfl

private theorem even_add_odd (n : ℕ) (j : Fin (n + 1)) :
    evenBinomial n j + oddBinomial n j = binomialWeight n j := by
  rcases Nat.even_or_odd j.val with h | h
  · simp [evenBinomial, oddBinomial, h, Nat.not_odd_iff_even.mpr h]
  · simp [evenBinomial, oddBinomial, h, Nat.not_even_iff_odd.mpr h]

private theorem even_sub_odd (n : ℕ) (j : Fin (n + 1)) :
    evenBinomial n j - oddBinomial n j = (-1 : ℝ) ^ j.val * binomialWeight n j := by
  rcases Nat.even_or_odd j.val with h | h
  · simp [evenBinomial, oddBinomial, h, Nat.not_odd_iff_even.mpr h, h.neg_one_pow]
  · simp [evenBinomial, oddBinomial, h, Nat.not_even_iff_odd.mpr h, h.neg_one_pow]

private theorem binomial_generating (n : ℕ) (x : ℝ) :
    (∑ j : Fin (n + 1), (n.choose j.val : ℝ) * x ^ j.val) = (1 + x) ^ n := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (n.choose j : ℝ) * x ^ j),
    add_comm (1 : ℝ) x, add_pow x (1 : ℝ) n]
  apply Finset.sum_congr rfl
  intro j _
  simp [mul_comm]

private theorem signed_binomial_generating (n : ℕ) (x : ℝ) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * x ^ j.val) =
      (1 - x) ^ n := by
  rw [sub_eq_add_neg, ← binomial_generating]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_pow]
  ring

private theorem signed_binomial_mass (n : ℕ) (hn : 0 < n) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ)) = 0 := by
  simpa only [one_pow, mul_one, sub_self, zero_pow hn.ne'] using
    signed_binomial_generating n 1

private theorem signed_binomial_first (n : ℕ) (hn : 1 < n) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * (j.val : ℝ)) = 0 := by
  have hleft : HasDerivAt
      (fun x : ℝ => ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * x ^ j.val)
      (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * (j.val : ℝ)) 1 := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [one_pow, mul_one] using
      (hasDerivAt_pow j.val (1 : ℝ)).const_mul ((-1 : ℝ) ^ j.val * (n.choose j.val : ℝ))
  have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) 1 := by
    simpa only [zero_sub] using
      (hasDerivAt_const (1 : ℝ) (1 : ℝ)).fun_sub (hasDerivAt_id' (1 : ℝ))
  have hright : HasDerivAt (fun x : ℝ => (1 - x) ^ n) 0 1 := by
    simpa only [sub_self, zero_pow (show n - 1 ≠ 0 by omega), mul_zero, zero_mul] using
      hbase.fun_pow n
  have heq : (fun x : ℝ =>
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * x ^ j.val) =
        fun x : ℝ => (1 - x) ^ n :=
    funext (signed_binomial_generating n)
  rw [heq] at hleft
  exact hleft.unique hright

private theorem weighted_binomial_difference (n : ℕ) (f : Fin (n + 1) → ℝ) :
    (∑ j, (evenBinomial n j - oddBinomial n j) * f j) =
      (∑ j, (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * f j) / (2 : ℝ) ^ (n - 1) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [even_sub_odd, binomialWeight]
  ring

/-- Both laws have nonnegative weights and unit mass. -/
theorem binomial_laws_normalized (n : ℕ) (hn : 0 < n) :
    (∀ j, 0 ≤ evenBinomial n j) ∧ (∀ j, 0 ≤ oddBinomial n j) ∧
      (∑ j, evenBinomial n j) = 1 ∧ (∑ j, oddBinomial n j) = 1 := by
  have hadd : (∑ j, evenBinomial n j) + (∑ j, oddBinomial n j) = 2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [even_add_odd, binomialWeight]
    rw [← Finset.sum_div]
    have h := binomial_generating n (1 : ℝ)
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at h
    simp only [one_pow, mul_one] at h
    rw [h, div_eq_iff (show (2 : ℝ) ^ (n - 1) ≠ 0 by positivity),
      mul_comm (2 : ℝ), ← pow_succ, Nat.sub_add_cancel hn]
  have hsub : (∑ j, evenBinomial n j) - (∑ j, oddBinomial n j) = 0 := by
    simpa only [mul_one, Finset.sum_sub_distrib, signed_binomial_mass n hn, zero_div] using
      weighted_binomial_difference n (fun _ => 1)
  exact ⟨evenBinomial_nonneg n, oddBinomial_nonneg n, by linarith, by linarith⟩

/-- The degree-one rate moments of the two laws agree. -/
theorem binomial_laws_equal_mean (n : ℕ) (hn : 1 < n) (r0 eta : ℝ) :
    rateMoment (binomialRate n r0 eta) (evenBinomial n) 1 =
      rateMoment (binomialRate n r0 eta) (oddBinomial n) 1 := by
  rw [rateMoment_eq_sum, rateMoment_eq_sum, ← sub_eq_zero]
  simp only [pow_one, ← Finset.sum_sub_distrib, ← sub_mul]
  rw [weighted_binomial_difference]
  have hnum :
      (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * binomialRate n r0 eta j) =
        (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ)) * r0 +
        (∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val * (n.choose j.val : ℝ) * (j.val : ℝ)) *
          eta := by
    simp only [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    unfold binomialRate
    ring
  rw [hnum, signed_binomial_mass n (by omega), signed_binomial_first n hn]
  simp

/-- The signed Laplace difference is the alternating binomial polynomial
evaluated at the exponential of the rate spacing. -/
theorem binomial_laplace_difference (n : ℕ) (r0 eta s : ℝ) :
    tiltedRateMoment (binomialRate n r0 eta) (evenBinomial n) 0 s -
      tiltedRateMoment (binomialRate n r0 eta) (oddBinomial n) 0 s =
        Real.exp (-(s * r0)) * (1 - Real.exp (-(s * eta))) ^ n /
          (2 : ℝ) ^ (n - 1) := by
  simp only [tiltedRateMoment, pow_zero, mul_one, ← Finset.sum_sub_distrib, ← sub_mul]
  rw [weighted_binomial_difference]
  have hexp (j : Fin (n + 1)) :
      Real.exp (-(s * binomialRate n r0 eta j)) =
        Real.exp (-(s * r0)) * Real.exp (-(s * eta)) ^ j.val := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply congrArg Real.exp
    unfold binomialRate
    ring
  simp_rw [hexp]
  apply congrArg (fun a : ℝ => a / (2 : ℝ) ^ (n - 1))
  rw [← signed_binomial_generating n (Real.exp (-(s * eta))), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The binomial witness has an exact profile difference at each scale.
Cancellation of the mass and mean leaves only the signed Laplace term. -/
theorem binomial_profile_difference (n : ℕ) (hn : 1 < n) (r0 eta s : ℝ) :
    rateProfile (binomialRate n r0 eta) (evenBinomial n) s -
      rateProfile (binomialRate n r0 eta) (oddBinomial n) s =
        Real.exp (-(s * r0)) * (1 - Real.exp (-(s * eta))) ^ n /
          ((2 : ℝ) ^ (n - 1) * s) := by
  have hnorm := binomial_laws_normalized n (by omega)
  have hmass : rateMoment (binomialRate n r0 eta) (evenBinomial n) 0 =
      rateMoment (binomialRate n r0 eta) (oddBinomial n) 0 := by
    simp only [rateMoment_eq_sum, pow_zero, mul_one, hnorm.2.2.1, hnorm.2.2.2]
  rw [rateProfile_eq_laplace, rateProfile_eq_laplace, hmass,
    binomial_laws_equal_mean n hn, ← sub_div]
  have hcancel (a b c d : ℝ) : (a - c + d) - (b - c + d) = a - b := by ring
  rw [hcancel, binomial_laplace_difference, div_div]

/-- An explicit constant for the uniform estimate over all positive scales. -/
def binomialUniformConstant (n : ℕ) (rMin : ℝ) : ℝ :=
  ((n - 1).factorial : ℝ) / rMin ^ (n - 1) / (2 : ℝ) ^ (n - 1)

theorem binomialUniformConstant_pos (n : ℕ) {rMin : ℝ} (hrMin : 0 < rMin) :
    0 < binomialUniformConstant n rMin := by
  have hfac : (0 : ℝ) < ((n - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  exact div_pos (div_pos hfac (pow_pos hrMin _)) (by positivity)

/-- A uniform estimate for the binomial witness, including the pointwise
scale factor that gives order `eta ^ n`. -/
theorem binomial_profile_difference_bound (n : ℕ) (hn : 1 < n)
    {rMin r0 eta s : ℝ} (hrMin : 0 < rMin) (hr0 : rMin ≤ r0)
    (heta : 0 ≤ eta) (hs : 0 < s) :
    |rateProfile (binomialRate n r0 eta) (evenBinomial n) s -
      rateProfile (binomialRate n r0 eta) (oddBinomial n) s| ≤
        Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / (2 : ℝ) ^ (n - 1) ∧
    Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / (2 : ℝ) ^ (n - 1) ≤
        binomialUniformConstant n rMin * eta ^ n := by
  let D : ℝ := (2 : ℝ) ^ (n - 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hbase : 0 ≤ 1 - Real.exp (-(s * eta)) := by
    apply sub_nonneg.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hs.le heta))
  have hstep : 1 - Real.exp (-(s * eta)) ≤ s * eta := by
    linarith [Real.one_sub_le_exp_neg (s * eta)]
  have hfac : (0 : ℝ) < ((n - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  have hdecay :
      Real.exp (-(s * r0)) * s ^ (n - 1) ≤ ((n - 1).factorial : ℝ) / rMin ^ (n - 1) := by
    apply (le_div_iff₀ (pow_pos hrMin _)).mpr
    have hexp : Real.exp (-(s * r0)) ≤ Real.exp (-(s * rMin)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hr0 hs.le))
    have hpow := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (s * rMin)
      (mul_nonneg hs.le hrMin.le) (n - 1))
    calc
      _ ≤ Real.exp (-(s * rMin)) * s ^ (n - 1) * rMin ^ (n - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hexp (pow_nonneg hs.le _)) (pow_nonneg hrMin.le _)
      _ = Real.exp (-(s * rMin)) * (s * rMin) ^ (n - 1) := by rw [mul_pow, mul_assoc]
      _ ≤ Real.exp (-(s * rMin)) * (Real.exp (s * rMin) * ((n - 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  constructor
  · rw [binomial_profile_difference n hn]
    change |Real.exp (-(s * r0)) * (1 - Real.exp (-(s * eta))) ^ n / (D * s)| ≤
      Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / D
    rw [abs_of_nonneg
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hbase _)) (mul_nonneg hD.le hs.le))]
    calc
      _ ≤ Real.exp (-(s * r0)) * (s * eta) ^ n / (D * s) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hstep n) (Real.exp_pos _).le)
          (mul_nonneg hD.le hs.le)
      _ = _ := by
        have hsplit : s ^ n = s ^ (n - 1) * s := by
          rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
        rw [mul_pow, hsplit]
        field_simp [hD.ne', hs.ne']
  · change Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / D ≤
      (((n - 1).factorial : ℝ) / rMin ^ (n - 1) / D) * eta ^ n
    calc
      _ ≤ (((n - 1).factorial : ℝ) / rMin ^ (n - 1)) * eta ^ n / D :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdecay (pow_nonneg heta _)) hD.le
      _ = _ := by ring

private theorem card_parity_of_fin (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : p < 2) :
    (Finset.univ.filter (fun j : Fin (2 * m - 1 + 1) => j.val % 2 = p)).card = m := by
  let index (i : Fin m) : Fin (2 * m - 1 + 1) :=
    ⟨2 * i.val + p, by have hi := i.isLt; omega⟩
  let half (j : Fin (2 * m - 1 + 1)) : Fin m :=
    ⟨j.val / 2, by have hj := j.isLt; omega⟩
  have hcard :
      (Finset.univ : Finset (Fin m)).card =
        (Finset.univ.filter (fun j : Fin (2 * m - 1 + 1) => j.val % 2 = p)).card := by
    apply Finset.card_nbij' index half
    · intro i _
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (2 * i.val + p) % 2 = p
      omega
    · intro j _
      exact Finset.mem_univ _
    · intro i _
      apply Fin.ext
      change (2 * i.val + p) / 2 = i.val
      omega
    · intro j hj
      have hpar := (Finset.mem_filter.mp hj).2
      apply Fin.ext
      change 2 * (j.val / 2) + p = j.val
      omega
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard.symm

/-- For the witness of order `2 * m - 1`, each probability law has exactly
`m` nonzero weights. -/
theorem binomial_laws_support_card (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter (fun j => evenBinomial (2 * m - 1) j ≠ 0)).card = m ∧
    (Finset.univ.filter (fun j => oddBinomial (2 * m - 1) j ≠ 0)).card = m := by
  have he : Finset.univ.filter (fun j => evenBinomial (2 * m - 1) j ≠ 0) =
      Finset.univ.filter (fun j : Fin (2 * m - 1 + 1) => j.val % 2 = 0) := by
    ext j
    have hw := (binomialWeight_pos (2 * m - 1) j).ne'
    by_cases hj : Even j.val <;> simp [evenBinomial, hw, hj, ← Nat.even_iff]
  have ho : Finset.univ.filter (fun j => oddBinomial (2 * m - 1) j ≠ 0) =
      Finset.univ.filter (fun j : Fin (2 * m - 1 + 1) => j.val % 2 = 1) := by
    ext j
    have hw := (binomialWeight_pos (2 * m - 1) j).ne'
    by_cases hj : Odd j.val <;> simp [oddBinomial, hw, hj, ← Nat.odd_iff]
  rw [he, ho]
  exact ⟨card_parity_of_fin m hm 0 (by decide), card_parity_of_fin m hm 1 (by decide)⟩

/-- Nonnegative coupling matrices with the prescribed finite marginals. -/
structure FiniteCoupling {ι : Type*} [Fintype ι] (weights weights' : ι → ℝ) where
  mass : ι → ι → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  row_sum : ∀ i, (∑ j, mass i j) = weights i
  col_sum : ∀ j, (∑ i, mass i j) = weights' j

/-- Discrete transport cost for the real-line distance between the rates. -/
def FiniteCoupling.cost {ι : Type*} [Fintype ι] {weights weights' : ι → ℝ}
    (coupling : FiniteCoupling weights weights') (rates : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, coupling.mass i j * |rates i - rates j|

/-- The finite Wasserstein distance for unit-mass laws on a common rate grid,
expressed as the infimum of costs of their coupling matrices. -/
def finiteWasserstein1 {ι : Type*} [Fintype ι]
    (rates weights weights' : ι → ℝ) : ℝ :=
  sInf (Set.range fun coupling : FiniteCoupling weights weights' => coupling.cost rates)

private theorem parity_rate_separation (n : ℕ) (r0 : ℝ) {eta : ℝ} (heta : 0 ≤ eta)
    {i j : Fin (n + 1)} (hi : Even i.val) (hj : Odd j.val) :
    eta ≤ |binomialRate n r0 eta i - binomialRate n r0 eta j| := by
  have hne : i.val ≠ j.val := by
    intro heq
    exact (Nat.not_odd_iff_even.mpr hi) (by simpa only [heq] using hj)
  have hdist : 1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hc : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hdiff : binomialRate n r0 eta i - binomialRate n r0 eta j =
      ((i.val : ℝ) - (j.val : ℝ)) * eta := by unfold binomialRate; ring
  rw [hdiff, abs_mul, abs_of_nonneg heta]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hdist heta

/-- Every coupling of the two binomial laws moves unit mass across at least
one grid spacing. -/
theorem binomial_wasserstein_lower_bound (n : ℕ) (hn : 0 < n)
    (r0 : ℝ) {eta : ℝ} (heta : 0 ≤ eta) :
    eta ≤ finiteWasserstein1 (binomialRate n r0 eta) (evenBinomial n) (oddBinomial n) := by
  obtain ⟨he, ho, hmassE, hmassO⟩ := binomial_laws_normalized n hn
  let product : FiniteCoupling (evenBinomial n) (oddBinomial n) :=
    { mass := fun i j => evenBinomial n i * oddBinomial n j
      nonneg := fun i j => mul_nonneg (he i) (ho j)
      row_sum := fun i => by rw [← Finset.mul_sum, hmassO, mul_one]
      col_sum := fun j => by rw [← Finset.sum_mul, hmassE, one_mul] }
  unfold finiteWasserstein1
  apply le_csInf
  · exact ⟨_, product, rfl⟩
  rintro _ ⟨coupling, rfl⟩
  have hrow (i j : Fin (n + 1)) (hi : ¬Even i.val) : coupling.mass i j = 0 := by
    have hle : coupling.mass i j ≤ ∑ k, coupling.mass i k :=
      Finset.single_le_sum (fun k _ => coupling.nonneg i k) (Finset.mem_univ j)
    rw [coupling.row_sum, evenBinomial, ite_eq_right hi] at hle
    exact le_antisymm hle (coupling.nonneg i j)
  have hcol (i j : Fin (n + 1)) (hj : ¬Odd j.val) : coupling.mass i j = 0 := by
    have hle : coupling.mass i j ≤ ∑ k, coupling.mass k j :=
      Finset.single_le_sum (fun k _ => coupling.nonneg k j) (Finset.mem_univ i)
    rw [coupling.col_sum, oddBinomial, ite_eq_right hj] at hle
    exact le_antisymm hle (coupling.nonneg i j)
  calc
    eta = ∑ i, ∑ j, coupling.mass i j * eta := by
      simp only [← Finset.sum_mul, coupling.row_sum, hmassE, one_mul]
    _ ≤ coupling.cost (binomialRate n r0 eta) := by
      unfold FiniteCoupling.cost
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      by_cases hi : Even i.val
      · by_cases hj : Odd j.val
        · exact mul_le_mul_of_nonneg_left (parity_rate_separation n r0 heta hi hj)
            (coupling.nonneg i j)
        · simp [hcol i j hj]
      · simp [hrow i j hi]

/-- The explicit binomial pair on the interval has the right support sizes,
equal first moments, a uniform observation error, and a transport lower bound. -/
theorem coalescing_binomial_witness (m : ℕ) (hm : 2 ≤ m) {rMin rMax eta : ℝ}
    (hrMin : 0 < rMin) (heta : 0 < eta) (hspan : rMin + ((2 * m - 1 : ℕ) : ℝ) * eta ≤ rMax) :
    let n := 2 * m - 1
    let rates := binomialRate n rMin eta
    let evenWeights := evenBinomial n
    let oddWeights := oddBinomial n
    StrictMono rates ∧
    (∀ j, rates j ∈ Set.Icc rMin rMax) ∧
    (∀ j, 0 ≤ evenWeights j ∧ 0 ≤ oddWeights j) ∧
    (Finset.univ.filter (fun j => evenWeights j ≠ 0)).card = m ∧
    (Finset.univ.filter (fun j => oddWeights j ≠ 0)).card = m ∧
    (∑ j, evenWeights j) = 1 ∧ (∑ j, oddWeights j) = 1 ∧
    rateMoment rates evenWeights 1 = rateMoment rates oddWeights 1 ∧
    (∀ s : ℝ, 0 < s → |rateProfile rates evenWeights s - rateProfile rates oddWeights s| ≤
      binomialUniformConstant n rMin * eta ^ n) ∧
    eta ≤ finiteWasserstein1 rates evenWeights oddWeights := by
  dsimp only
  let n : ℕ := 2 * m - 1
  have hn : 1 < n := by dsimp [n]; omega
  obtain ⟨he, ho, hmassE, hmassO⟩ := binomial_laws_normalized n (by omega)
  obtain ⟨hcardE, hcardO⟩ := binomial_laws_support_card m (by omega)
  refine ⟨?_, ?_, fun j => ⟨he j, ho j⟩, hcardE, hcardO, hmassE, hmassO,
    binomial_laws_equal_mean n hn rMin eta, ?_,
    binomial_wasserstein_lower_bound n (by omega) rMin heta.le⟩
  · intro i j hij
    have hcast : (i.val : ℝ) < (j.val : ℝ) := by
      exact_mod_cast (show i.val < j.val from hij)
    exact add_lt_add_right (mul_lt_mul_of_pos_right hcast heta) rMin
  · intro j
    have hj : (j.val : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp j.isLt
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) heta.le),
      (add_le_add_right (mul_le_mul_of_nonneg_right hj heta.le) rMin).trans hspan⟩
  · intro s hs
    obtain ⟨hpoint, huniform⟩ :=
      binomial_profile_difference_bound n hn hrMin le_rfl heta.le hs
    exact hpoint.trans huniform

/-- Even an error bound valid at every positive scale cannot yield a
uniform inverse Hölder estimate with exponent greater than `1 / (2*m - 1)`.
The common grid is allowed to vary within the fixed interval. Both laws
have exactly `m` atoms and the same mean. -/
theorem no_uniform_holder_inverse (m : ℕ) (hm : 2 ≤ m) {rMin rMax alpha : ℝ}
    (hrMin : 0 < rMin) (hrange : rMin < rMax)
    (halpha : 1 < ((2 * m - 1 : ℕ) : ℝ) * alpha) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (rates w v : Fin (2 * m - 1 + 1) → ℝ) (delta : ℝ),
        StrictMono rates →
        (∀ j, rates j ∈ Set.Icc rMin rMax) →
        (∀ j, 0 ≤ w j ∧ 0 ≤ v j) →
        (Finset.univ.filter (fun j => w j ≠ 0)).card = m →
        (Finset.univ.filter (fun j => v j ≠ 0)).card = m →
        (∑ j, w j) = 1 → (∑ j, v j) = 1 →
        rateMoment rates w 1 = rateMoment rates v 1 →
        0 < delta →
        (∀ s : ℝ, 0 < s → |rateProfile rates w s - rateProfile rates v s| ≤ delta) →
        finiteWasserstein1 rates w v ≤ C * delta ^ alpha := by
  rintro ⟨C, hC, hinverse⟩
  let n : ℕ := 2 * m - 1
  let B := binomialUniformConstant n rMin
  let beta := (n : ℝ) * alpha - 1
  have hn : 1 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hB : 0 < B := binomialUniformConstant_pos n hrMin
  have hbeta : 0 < beta := sub_pos.mpr halpha
  have hcoef : 0 ≤ C * B ^ alpha :=
    mul_nonneg hC (Real.rpow_nonneg hB.le _)
  have hk : 0 < C * B ^ alpha + 1 := by linarith
  have hcont := Real.continuousAt_rpow_const 0 beta (Or.inr hbeta.le)
  obtain ⟨rho, hrho, hclose⟩ :=
    Metric.continuousAt_iff.mp hcont (1 / (C * B ^ alpha + 1)) (div_pos one_pos hk)
  let eta := min (rho / 2) ((rMax - rMin) / (n : ℝ))
  have heta : 0 < eta :=
    lt_min (div_pos hrho (by norm_num)) (div_pos (sub_pos.mpr hrange) hnR)
  have hetarho : eta < rho := (min_le_left _ _).trans_lt (by linarith)
  have hspan : rMin + (n : ℝ) * eta ≤ rMax := by
    have hbound : eta ≤ (rMax - rMin) / (n : ℝ) := min_le_right _ _
    have hmul := (le_div_iff₀ hnR).mp hbound
    linarith [show (n : ℝ) * eta = eta * (n : ℝ) by ring]
  have hdist : dist eta 0 < rho := by
    rw [Real.dist_0_eq_abs, abs_of_pos heta]
    exact hetarho
  have heps : eta ^ beta < 1 / (C * B ^ alpha + 1) := by
    have h := hclose hdist
    simpa only [Real.zero_rpow hbeta.ne', Real.dist_0_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos heta beta)] using h
  have hsmall : C * B ^ alpha * eta ^ beta < 1 := by
    calc
      _ ≤ (C * B ^ alpha + 1) * eta ^ beta :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg heta.le _)
      _ < (C * B ^ alpha + 1) * (1 / (C * B ^ alpha + 1)) :=
        mul_lt_mul_of_pos_left heps hk
      _ = 1 := by field_simp [hk.ne']
  let delta := B * eta ^ n
  have hdelta : 0 < delta := mul_pos hB (pow_pos heta n)
  have hexponent : (n : ℝ) * alpha = 1 + beta := by dsimp [beta]; ring
  have hpower : delta ^ alpha = B ^ alpha * (eta * eta ^ beta) := by
    dsimp only [delta]
    rw [Real.mul_rpow hB.le (pow_nonneg heta.le _), ← Real.rpow_natCast_mul heta.le,
      hexponent, Real.rpow_add heta, Real.rpow_one]
  have hstrict : C * delta ^ alpha < eta := by
    rw [hpower]
    calc
      _ = eta * (C * B ^ alpha * eta ^ beta) := by ring
      _ < eta * 1 := mul_lt_mul_of_pos_left hsmall heta
      _ = _ := mul_one eta
  obtain ⟨hmono, hinterval, hnonneg, hcardW, hcardV, hmassW, hmassV, hmean, hobs, hcost⟩ :=
    coalescing_binomial_witness m hm hrMin heta hspan
  have hupper := hinverse _ _ _ delta hmono hinterval hnonneg hcardW hcardV
    hmassW hmassV hmean hdelta hobs
  exact (not_lt_of_ge (hcost.trans hupper)) hstrict

#print axioms diagonal_log_ratio_profile_error
#print axioms rateMoment_eq_sum
#print axioms rateProfile_eq_laplace
#print axioms hasDerivAt_tiltedRateMoment
#print axioms hasDerivAt_rateProfile
#print axioms binomial_laws_normalized
#print axioms binomial_laws_equal_mean
#print axioms binomial_laws_support_card
#print axioms binomial_laplace_difference
#print axioms binomial_profile_difference
#print axioms binomialUniformConstant_pos
#print axioms binomial_profile_difference_bound
#print axioms binomial_wasserstein_lower_bound
#print axioms coalescing_binomial_witness
#print axioms no_uniform_holder_inverse

end

end D5.S3.Analytic.PetzDyadicEscapeSpectrum

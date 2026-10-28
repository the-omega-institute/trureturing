/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfGenerating
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Gaussian generating-function helper for the original finite-source comparison. -/

/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED independent source proposal, 2026-10-26.
No compiler, kernel, or official acceptance is asserted.

Depends on the ROOT-COLLECTED LaguerreSevenHalfPolynomial.lean supplier.
Its explicit polynomial and coefficient definitions are imported, not copied.
The binomial series used below is Mathlib's ordinary complex binomial series;
no generalized Laguerre expansion is assumed. No OAI code is ported here.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfPolynomial
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped BigOperators Topology

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- The actual physical polynomial mode, without a normalization factor. -/
def phi (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * (laguerre n).eval (2 * x)

/-- Principal complex power; on the open unit disk `1-z` is in the slit plane. -/
def generating (x : ℝ) (z : ℂ) : ℂ :=
  (1 - z) ^ ((-9 / 2 : ℝ) : ℂ) *
    Complex.exp (-(x : ℂ) * (1 + z) / (1 - z))

private def pochhammerQuotient (a : ℝ) (m : ℕ) : ℝ :=
  (ascPochhammer ℝ m).eval a / (m.factorial : ℝ)

private theorem choose_asc {K : Type*} [Field K] [CharZero K] (a : K) (m : ℕ) :
    Ring.choose (a + m - 1) m =
      (ascPochhammer K m).eval a / (m.factorial : K) := by
  rw [Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]
  have he : a + (m : K) - 1 - m + 1 = a := by ring
  rw [he]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem cast_pochhammer (a : ℝ) (m : ℕ) :
    ((pochhammerQuotient a m : ℝ) : ℂ) =
      (ascPochhammer ℂ m).eval (a : ℂ) / (m.factorial : ℂ) := by
  have hp : (((ascPochhammer ℝ m).eval a : ℝ) : ℂ) =
      (ascPochhammer ℂ m).eval (a : ℂ) := by
    induction m with
    | zero => simp
    | succ m ih =>
        simp only [ascPochhammer_succ_eval, Complex.ofReal_mul,
          Complex.ofReal_add, Complex.ofReal_natCast, ih]
  simpa only [pochhammerQuotient, Complex.ofReal_div, Complex.ofReal_natCast] using
    congrArg (fun w : ℂ => w / (m.factorial : ℂ)) hp

private theorem binomial_real (a t : ℝ) (ht : |t| < 1) :
    HasSum (fun m => pochhammerQuotient a m * t ^ m) (1 / (1 - t) ^ a) := by
  have ht' : t ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using ht
  have hs := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum_sub ht'
  simpa [FormalMultilinearSeries.ofScalars, choose_asc, pochhammerQuotient] using hs

private theorem binomial_complex (a : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun m => (pochhammerQuotient a m : ℂ) * z ^ m)
      (1 / (1 - z) ^ (a : ℂ)) := by
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have hs := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero
    (a : ℂ)).hasSum_sub hz'
  simpa [FormalMultilinearSeries.ofScalars, choose_asc, cast_pochhammer] using hs

private theorem exp_real (u : ℝ) :
    HasSum (fun j : ℕ => u ^ j / (j.factorial : ℝ)) (Real.exp u) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp u

private theorem exp_complex (u : ℂ) :
    HasSum (fun j : ℕ => u ^ j / (j.factorial : ℂ)) (Complex.exp u) := by
  simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp u

private theorem pochhammerQuotient_nonneg (j m : ℕ) :
    0 ≤ pochhammerQuotient ((9 / 2 : ℝ) + j) m := by
  exact div_nonneg (ascPochhammer_pos m _ (by positivity)).le (by positivity)

private def gaussianTerm (x : ℝ) (z : ℂ) (j m : ℕ) : ℂ :=
  ((((-2 * x) ^ j / (j.factorial : ℝ)) *
    pochhammerQuotient ((9 / 2 : ℝ) + j) m : ℝ) : ℂ) * z ^ (j + m)

private theorem gaussianTerm_norm (x : ℝ) (z : ℂ) (j m : ℕ) :
    ‖gaussianTerm x z j m‖ =
      ((2 * |x|) ^ j / (j.factorial : ℝ)) *
        pochhammerQuotient ((9 / 2 : ℝ) + j) m * ‖z‖ ^ (j + m) := by
  simp only [gaussianTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ (j.factorial : ℝ) from Nat.cast_nonneg _),
    abs_of_nonneg (pochhammerQuotient_nonneg j m), norm_pow]

/-- Absolute convergence of the double series, used only for pointwise regrouping.
Its sum may grow in `x`; it is not the graph-domain domination estimate. -/
private theorem gaussianTerm_summable (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun p : ℕ × ℕ => gaussianTerm x z p.1 p.2) := by
  let t : ℝ := ‖z‖
  let A : ℝ := 2 * |x|
  have ht0 : 0 ≤ t := norm_nonneg z
  have ht1 : t < 1 := hz
  have hd : 0 < 1 - t := sub_pos.mpr ht1
  let T : ℕ × ℕ → ℝ := fun p =>
    (A ^ p.1 / (p.1.factorial : ℝ)) *
      pochhammerQuotient ((9 / 2 : ℝ) + p.1) p.2 * t ^ (p.1 + p.2)
  have hrow (j : ℕ) :
      HasSum (fun m => T (j, m))
        ((1 / (1 - t) ^ (9 / 2 : ℝ)) *
          ((A * t / (1 - t)) ^ j / (j.factorial : ℝ))) := by
    have hb := (binomial_real ((9 / 2 : ℝ) + j) t
      (by simpa [abs_of_nonneg ht0] using ht1)).mul_left
        ((A ^ j / (j.factorial : ℝ)) * t ^ j)
    convert hb using 1
    · ext m
      simp only [T, pow_add]
      ring
    · rw [Real.rpow_add_natCast hd.ne']
      simp only [div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
  have hout := (exp_real (A * t / (1 - t))).mul_left
    (1 / (1 - t) ^ (9 / 2 : ℝ))
  have hT : Summable T := (summable_prod_of_nonneg (fun p => by
    dsimp [T, A]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (by positivity) (by positivity))
        (pochhammerQuotient_nonneg p.1 p.2)) (pow_nonneg ht0 _))).2
    ⟨fun j => (hrow j).summable, by
      simpa only [(hrow _).tsum_eq] using hout.summable⟩
  apply Summable.of_norm
  simpa only [gaussianTerm_norm, T, t, A] using hT

private theorem one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro h
  have hz1 : z = 1 := sub_eq_zero.mp h |>.symm
  simpa [hz1] using hz

private theorem gaussianTerm_row (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) (j : ℕ) :
    HasSum (fun m => gaussianTerm x z j m)
      ((1 / (1 - z) ^ (9 / 2 : ℂ)) *
        ((-2 * (x : ℂ) * z / (1 - z)) ^ j / (j.factorial : ℂ))) := by
  have hb := (binomial_complex ((9 / 2 : ℝ) + j) z hz).mul_left
    ((((-2 * x) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) * z ^ j)
  convert hb using 1
  · ext m
    simp only [gaussianTerm, Complex.ofReal_mul, pow_add]
    ring
  · push_cast
    rw [Complex.cpow_add _ _ (one_sub_ne_zero hz), Complex.cpow_natCast]
    simp only [div_pow, mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring

private theorem gaussianTerm_product_hasSum (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun p : ℕ × ℕ => gaussianTerm x z p.1 p.2)
      ((1 / (1 - z) ^ (9 / 2 : ℂ)) *
        Complex.exp (-2 * (x : ℂ) * z / (1 - z))) := by
  have hs := gaussianTerm_summable x z hz
  apply hs.hasSum_iff.mpr
  rw [hs.tsum_prod]
  simp_rw [(gaussianTerm_row x z hz _).tsum_eq]
  exact ((exp_complex (-2 * (x : ℂ) * z / (1 - z))).mul_left
    (1 / (1 - z) ^ (9 / 2 : ℂ))).tsum_eq

private theorem gaussianTerm_coefficient (x : ℝ) (z : ℂ) (j m : ℕ) :
    gaussianTerm x z j m =
      ((coefficient (j + m) j * (2 * x) ^ j : ℝ) : ℂ) * z ^ (j + m) := by
  have hp : (-2 * x) ^ j = (-1 : ℝ) ^ j * (2 * x) ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have hc : ((-2 * x) ^ j / (j.factorial : ℝ)) *
      pochhammerQuotient ((9 / 2 : ℝ) + j) m =
        coefficient (j + m) j * (2 * x) ^ j := by
    rw [coefficient_add, hp]
    simp only [pochhammerQuotient, div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [gaussianTerm, hc]

private theorem gaussianTerm_antidiagonal (x : ℝ) (z : ℂ) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, gaussianTerm x z p.1 p.2) =
      (((laguerre n).eval (2 * x) : ℝ) : ℂ) * z ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  rw [laguerre_eval]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [gaussianTerm_coefficient, Nat.add_sub_of_le hjn]
  push_cast
  rfl

/-- Complex Laguerre generating series, derived from the literal finite coefficients. -/
theorem laguerre_hasSum_complex (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n => (((laguerre n).eval (2 * x) : ℝ) : ℂ) * z ^ n)
      ((1 / (1 - z) ^ (9 / 2 : ℂ)) *
        Complex.exp (-2 * (x : ℂ) * z / (1 - z))) := by
  classical
  let e : (Σ n : ℕ, Finset.antidiagonal n) ≃ ℕ × ℕ :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
  have hp := gaussianTerm_product_hasSum x z hz
  have hs : HasSum
      (fun p : Σ n : ℕ, Finset.antidiagonal n =>
        gaussianTerm x z p.2.1.1 p.2.1.2)
      ((1 / (1 - z) ^ (9 / 2 : ℂ)) *
        Complex.exp (-2 * (x : ℂ) * z / (1 - z))) := by
    exact e.hasSum_iff.mpr hp
  have hd (n : ℕ) : HasSum
      (fun p : Finset.antidiagonal n => gaussianTerm x z p.1.1 p.1.2)
      ((((laguerre n).eval (2 * x) : ℝ) : ℂ) * z ^ n) := by
    have hf := hasSum_fintype
      (fun p : Finset.antidiagonal n => gaussianTerm x z p.1.1 p.1.2)
    have he : (∑ p : Finset.antidiagonal n, gaussianTerm x z p.1.1 p.1.2) =
        (((laguerre n).eval (2 * x) : ℝ) : ℂ) * z ^ n :=
      (Finset.sum_coe_sort (Finset.antidiagonal n)
        (fun p : ℕ × ℕ => gaussianTerm x z p.1 p.2)).trans
          (gaussianTerm_antidiagonal x z n)
    rw [he] at hf
    exact hf
  exact hs.sigma hd

/-- The requested complex generating equality. In fact positivity of `x` is unnecessary. -/
theorem phi_hasSum_complex (x : ℝ) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n => (phi x n : ℂ) * z ^ n) (generating x z) := by
  have hs := (laguerre_hasSum_complex x z hz).mul_left (Real.exp (-x) : ℂ)
  have he : -(x : ℂ) + (-2 * (x : ℂ) * z / (1 - z)) =
      -(x : ℂ) * (1 + z) / (1 - z) := by
    field_simp [one_sub_ne_zero hz]
    <;> ring
  convert hs using 1
  · ext n
    simp only [phi, Complex.ofReal_mul]
    ring
  · simp only [generating, Complex.ofReal_exp, Complex.ofReal_neg]
    rw [show ((-9 / 2 : ℝ) : ℂ) = -(9 / 2 : ℂ) by norm_num,
      Complex.cpow_neg, ← he, Complex.exp_add]
    ring

theorem generating_ofReal (x q : ℝ) (hq : |q| < 1) :
    generating x (q : ℂ) =
      (((1 - q) ^ (-9 / 2 : ℝ) *
        Real.exp (-x * (1 + q) / (1 - q)) : ℝ) : ℂ) := by
  have hpos : 0 ≤ 1 - q := by have := (abs_lt.mp hq).2; linarith
  simp only [generating, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow hpos]

/-- Real HasSum for every real `|q|<1`, with no assumed expansion. -/
theorem phi_hasSum_real (x q : ℝ) (hq : |q| < 1) :
    HasSum (fun n => phi x n * q ^ n)
      ((1 - q) ^ (-9 / 2 : ℝ) *
        Real.exp (-x * (1 + q) / (1 - q))) := by
  apply Complex.hasSum_ofReal.mp
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, generating_ofReal x q hq] using
    phi_hasSum_complex x (q : ℂ) (by simpa using hq)

/-- A local power series suffices to identify every Taylor coefficient. -/
theorem generating_hasFPowerSeriesAt (x : ℝ) :
    HasFPowerSeriesAt (generating x)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (phi x n : ℂ))) 0 := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (phi x n : ℂ))
  have hs : Summable (fun n => (phi x n : ℂ) * (1 / 2 : ℂ) ^ n) :=
    (phi_hasSum_complex x (1 / 2) (by norm_num)).summable
  have hn : Summable (fun n => ‖p n‖ * (1 / 2 : ℝ) ^ n) := by
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      norm_div, norm_one, Complex.norm_ofNat] using hs.norm
  refine ⟨((1 / 2 : NNReal) : ENNReal), ⟨?_, by norm_num, ?_⟩⟩
  · exact p.le_radius_of_summable_norm (r := (1 / 2 : NNReal)) hn
  · intro z hz
    have hz' : ‖z‖ < 1 := by
      have : ‖z‖ < (1 / 2 : ℝ) := by
        have hnn : ‖z‖₊ < (1 / 2 : NNReal) :=
          ENNReal.coe_lt_coe.mp (by simpa [enorm_eq_nnnorm] using hz)
        exact_mod_cast hnn
      linarith
    simpa [p, FormalMultilinearSeries.ofScalars] using phi_hasSum_complex x z hz'

/-- Actual Taylor-coefficient identification, obtained from the proved series. -/
theorem generating_iteratedDeriv (x : ℝ) (n : ℕ) :
    iteratedDeriv n (generating x) 0 = (n.factorial : ℂ) * (phi x n : ℂ) := by
  obtain ⟨r, hr⟩ := generating_hasFPowerSeriesAt x
  have h := hr.factorial_smul (1 : ℂ) n
  simpa [← iteratedDeriv_eq_iteratedFDeriv, FormalMultilinearSeries.ofScalars,
    nsmul_eq_mul] using h.symm

theorem generating_taylor_coefficient (x : ℝ) (n : ℕ) :
    iteratedDeriv n (generating x) 0 / (n.factorial : ℂ) =
      (Real.exp (-x) * (laguerre n).eval (2 * x) : ℂ) := by
  rw [generating_iteratedDeriv]
  simp [phi, Nat.factorial_ne_zero]

end FiniteGaussianCap4.LaguerreSevenHalf

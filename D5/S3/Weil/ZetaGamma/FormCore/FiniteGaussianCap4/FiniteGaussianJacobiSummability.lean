/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianJacobiSummability
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian infinite Jacobi energy and complete boundary payment. -/
/-
SPDX-License-Identifier: Apache-2.0
Finite-source Gaussian Jacobi development, 2026-10-26.
Actual finite-source coefficient summability. The ratio test uses the proved
N_(n+1)^2 recurrence; no Gamma asymptotic or coefficient bound is assumed.
Imported supplier attribution and license notices remain applicable.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.FiniteGaussianGraph
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfFiniteJacobi
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace FiniteGaussianCap4
open LaguerreSevenHalf

private def atomWeightedSquare (a : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 2 *
    (gaussianSiteAmplitude a * gaussianSiteQ a ^ n / centralNormalization n) ^ 2

private theorem atomWeightedSquare_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ atomWeightedSquare a n := by unfold atomWeightedSquare; positivity

private theorem atomWeightedSquare_step (a : ℝ) (n : ℕ) :
    atomWeightedSquare a (n + 1) =
      ((1 + 1 / ((n : ℝ) + 1)) ^ 2 *
        (1 + (7 / 2 : ℝ) / ((n : ℝ) + 1)) * gaussianSiteQ a ^ 2) * atomWeightedSquare a n := by
  rw [atomWeightedSquare, atomWeightedSquare, pow_succ (gaussianSiteQ a) n]
  simp only [Nat.cast_add, Nat.cast_one, div_pow, mul_pow]
  rw [centralNormalization_sq_step]
  field_simp [(centralNormalization_pos n).ne',
    show (n : ℝ) + 1 ≠ 0 by positivity,
    show (n : ℝ) + 9 / 2 ≠ 0 by positivity]
  <;> ring

private theorem atomWeightedSquare_summable (a : ℝ) : Summable (atomWeightedSquare a) := by
  let q := gaussianSiteQ a
  have hq : q ^ 2 < 1 := by
    obtain ⟨hl, hu⟩ := abs_lt.mp (gaussianSiteQ_abs_lt_one a)
    have hp : 0 < (1 - q) * (1 + q) := mul_pos (by dsimp [q]; linarith) (by dsimp [q]; linarith)
    nlinarith
  let r : ℝ := (1 + q ^ 2) / 2
  have hqr : q ^ 2 < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hdiv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : Tendsto (fun n : ℕ =>
      (1 + 1 / ((n : ℝ) + 1)) ^ 2 *
        (1 + (7 / 2 : ℝ) / ((n : ℝ) + 1)) * q ^ 2) atTop (𝓝 (q ^ 2)) := by
    have hdiv' : Tendsto (fun n : ℕ => (7 / 2 : ℝ) * (1 / ((n : ℝ) + 1)))
        atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (7 / 2 : ℝ))).mul hdiv
    simpa [div_eq_mul_inv] using
      ((((tendsto_const_nhds (x := (1 : ℝ))).add hdiv).pow 2).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add hdiv')).mul
          (tendsto_const_nhds (x := q ^ 2))
  apply summable_of_ratio_norm_eventually_le hr
  filter_upwards [hratio.eventually_le_const hqr] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (atomWeightedSquare_nonneg a (n + 1)),
    abs_of_nonneg (atomWeightedSquare_nonneg a n), atomWeightedSquare_step]
  exact mul_le_mul_of_nonneg_right hn (atomWeightedSquare_nonneg a n)

/-- All actual normalized modes have a summable quadratic second moment.
This is unconditional for every finite real source, including repeated sites. -/
theorem finiteGaussian_normalized_weighted_square_summable {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) : Summable (fun n : ℕ =>
      ((n : ℝ) + 1) ^ 2 * finiteGaussianNormalizedCoefficient c site n ^ 2) := by
  classical
  have hsum : Summable (fun n : ℕ =>
      (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * atomWeightedSquare (site i) n) := by
    exact (hasSum_sum (s := Finset.univ) (fun i _ =>
      ((atomWeightedSquare_summable (site i)).mul_left (c i ^ 2)).hasSum)).summable.mul_left _
  apply hsum.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc : finiteGaussianNormalizedCoefficient c site n =
      ∑ i, c i * (gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n /
        centralNormalization n) := by
    simp only [finiteGaussianNormalizedCoefficient, finiteGaussianCoefficient,
      div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc]
  have h := mul_le_mul_of_nonneg_left (finite_real_square_bound (fun i =>
    c i * (gaussianSiteAmplitude (site i) * gaussianSiteQ (site i) ^ n /
      centralNormalization n))) (sq_nonneg ((n : ℝ) + 1))
  convert h using 1
  simp only [atomWeightedSquare, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteGaussian_even_weighted_square_summable {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) : Summable (fun k : ℕ =>
      ((k : ℝ) + 1) ^ 2 * finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) := by
  have hi : Function.Injective (fun k : ℕ => 2 * k) := by
    intro a b h
    change 2 * a = 2 * b at h
    omega
  have h := (finiteGaussian_normalized_weighted_square_summable c site).comp_injective hi
  apply h.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hc : ((k : ℝ) + 1) ^ 2 ≤ ((2 * k : ℕ) + 1 : ℝ) ^ 2 := by
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

private theorem quadratic_summable {d : ℕ → ℝ}
    (hd : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * d k ^ 2))
    (p : ℕ → ℝ) (C : ℝ) (hp : ∀ k, |p k| ≤ C * ((k : ℝ) + 1) ^ 2) :
    Summable (fun k : ℕ => p k * d k ^ 2) := by
  apply (hd.mul_left C).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (d k))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hp k) (sq_nonneg (d k))

/-- Actual diagonal, edge, positive comparison, and H-energy series.
The statement uses precisely the supplied normalized coefficients and tailH. -/
theorem finiteGaussian_actual_jacobi_summability {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    Summable (fun k : ℕ => jacobiD k * finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) ∧
    Summable (fun k : ℕ => jacobiB k * finiteGaussianNormalizedCoefficient c site (2 * k) *
      finiteGaussianNormalizedCoefficient c site (2 * (k + 1))) ∧
    Summable (fun k : ℕ => (2 * (k : ℝ) + 9 / 4) ^ 2 *
      finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) ∧
    Summable (fun k : ℕ => tailH k * finiteGaussianNormalizedCoefficient c site (2 * k) ^ 2) := by
  let d : ℕ → ℝ := fun k => finiteGaussianNormalizedCoefficient c site (2 * k)
  have hw : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * d k ^ 2) :=
    finiteGaussian_even_weighted_square_summable c site
  have hR : Summable (fun k => jacobiR k * d k ^ 2) := by
    apply quadratic_summable hw jacobiR 3
    intro k
    rw [abs_of_nonneg (jacobiR_nonneg k)]
    have hk := Nat.cast_nonneg (α := ℝ) k
    dsimp [jacobiR]
    nlinarith [sq_nonneg (k : ℝ)]
  have hL : Summable (fun k => jacobiL k * d k ^ 2) := by
    apply quadratic_summable hw jacobiL 2
    intro k
    rw [abs_of_nonneg (jacobiL_nonneg k)]
    have hk := Nat.cast_nonneg (α := ℝ) k
    dsimp [jacobiL]
    nlinarith [sq_nonneg (k : ℝ)]
  have hshift : Summable (fun k => jacobiL (k + 1) * d (k + 1) ^ 2) :=
    hL.comp_injective (fun a b h => by omega)
  have he2 : Summable (fun k => 2 * jacobiB k * d k * d (k + 1)) := by
    apply (hR.add hshift).of_norm_bounded
    intro k
    exact (Real.norm_eq_abs _).trans_le (jacobi_edge_abs_payment k (d k) (d (k + 1)))
  have he : Summable (fun k => jacobiB k * d k * d (k + 1)) := by
    convert he2.mul_left (1 / 2 : ℝ) using 1
    funext k
    ring
  refine ⟨?_, he, ?_, ?_⟩
  · apply quadratic_summable hw jacobiD 14
    intro k
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hD : 0 ≤ jacobiD k := by unfold jacobiD; positivity
    rw [abs_of_nonneg hD]
    dsimp [jacobiD]
    nlinarith [sq_nonneg (k : ℝ)]
  · apply quadratic_summable hw (fun k => (2 * (k : ℝ) + 9 / 4) ^ 2) 6
    intro k
    rw [abs_of_nonneg (sq_nonneg _)]
    have hk := Nat.cast_nonneg (α := ℝ) k
    nlinarith [sq_nonneg (k : ℝ)]
  · apply quadratic_summable hw (fun k => tailH k) 50
    intro k
    have hk := Nat.cast_nonneg (α := ℝ) k
    unfold tailH
    apply abs_le.2
    constructor <;> nlinarith [sq_nonneg (k : ℝ)]

theorem finiteGaussian_actual_edge_abs_summable {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) : Summable (fun k : ℕ =>
      |2 * jacobiB k * finiteGaussianNormalizedCoefficient c site (2 * k) *
        finiteGaussianNormalizedCoefficient c site (2 * (k + 1))|) := by
  have h := ((finiteGaussian_actual_jacobi_summability c site).2.1.mul_left (2 : ℝ)).norm
  simpa only [Real.norm_eq_abs, mul_assoc] using h

end FiniteGaussianCap4

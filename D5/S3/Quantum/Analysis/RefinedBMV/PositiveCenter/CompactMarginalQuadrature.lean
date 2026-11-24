/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMarginalQuadrature
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact closed-mesh and signed quadrature formulas for the regularized marginal. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical
import D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
import Batteries.Tactic.OpenPrivate

open scoped BigOperators

noncomputable section

namespace RefinedBMV.PositiveCenter

open DimThree (gaps gaps_length_eq_choose)
open D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth (meshRemainder mesh_sum_eq)
open SmallCorner

open private gridPoint gridAverage gaps_length_pos gridAverage_eq_marginal
  gridAverage_const_mul gridAverage_sub gridAverage_pow_eq centered_variance_eq from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
open private compositionMoment_marginal_sum from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

/-- The mass normalization for the closed marginal mesh of spacing `h`. -/
def compactMarginalMeshDenominator (h : ℝ) : ℝ := (3 + h) * (3 + 2 * h)

/-- The regularized exponential remainder multiplied by the affine marginal weight. -/
def regularizedMarginalIntegrand (h t x : ℝ) : ℝ :=
  (2 + h - x) * regularizedMarginalRemainder t x

private theorem compactKappa_mul_compactZ_eq_gridAverage {p : ℕ} (hp : 0 < p) (t : ℝ) :
    compactKappa p * compactZ p t = gridAverage p (regularizedMarginalRemainder t) := by
  by_cases ht : t = 0
  · subst t
    have hvariance : gridAverage p (fun x ↦ x ^ 2) = (1 + 3 / (p : ℝ)) / 2 := by
      rw [gridAverage_eq_marginal]
      exact centered_variance_eq hp
    rw [regularizedMarginalRemainder, ite_eq_left (rfl : (0 : ℝ) = 0)]
    simp only [compactZ_zero hp, mul_one, div_eq_inv_mul, gridAverage_const_mul, hvariance,
      compactKappa]
    ring
  · have hone : gridAverage p (fun _ ↦ 1) = 1 := by
      simpa only [pow_zero, compactCenteredMomentPolynomial] using gridAverage_pow_eq hp 0
    have hmean : gridAverage p (fun x ↦ x) = 0 := by
      simpa only [pow_one, compactCenteredMomentPolynomial] using gridAverage_pow_eq hp 1
    have hlinear : gridAverage p (fun x ↦ t * x) = 0 := by
      rw [gridAverage_const_mul, hmean, mul_zero]
    have hexp : compositionMoment p 0 t = gridAverage p (fun x ↦ Real.exp (t * x)) - 1 := by
      rw [compositionMoment_marginal_sum, gridAverage]
      apply congrArg (· - 1)
      apply congrArg (· / ((gaps p).length : ℝ))
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_comm t]
      rfl
    have hQ : compactKappa p * compactZ p t = compositionMoment p 0 t / t ^ 2 := by
      apply (eq_div_iff (pow_ne_zero _ ht)).2
      rw [compositionMoment_eq_compactZ hp]
      ring
    rw [hQ, hexp, regularizedMarginalRemainder, ite_eq_right ht]
    simp only [div_eq_inv_mul, gridAverage_const_mul, gridAverage_sub, hone, hlinear, sub_zero]

private theorem mul_marginal_step {p : ℕ} (hp : 0 < p) :
    (p : ℝ) * (3 / (p : ℝ)) = 3 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]

/-- The exact marginal is a weighted closed sum over all `p + 1` nodes, including at `t = 0`. -/
theorem compactKappa_mul_compactZ_eq_mesh_sum {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    compactKappa p * compactZ p t = 2 * h / compactMarginalMeshDenominator h *
      ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h) := by
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := div_pos (by norm_num) hpR
  have hph : (p : ℝ) * h = 3 := mul_marginal_step hp
  have hmass : ((gaps p).length : ℝ) * h ^ 2 = compactMarginalMeshDenominator h / 2 := by
    rw [gaps_length_eq_choose]
    exact tail_choose_scale hp
  have hweight (i : ℕ) (hi : i ∈ Finset.range (p + 1)) :
      ((p + 1 - i : ℕ) : ℝ) * h = 2 + h - (-1 + (i : ℝ) * h) := by
    rw [Nat.cast_sub (Finset.mem_range.mp hi).le, Nat.cast_add, Nat.cast_one]
    linear_combination hph
  have hsum :
      h * (∑ i ∈ Finset.range (p + 1),
        ((p + 1 - i : ℕ) : ℝ) * regularizedMarginalRemainder t (gridPoint p i)) =
      ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hnode : gridPoint p i = -1 + (i : ℝ) * h := by
      unfold gridPoint h
      ring
    rw [hnode, regularizedMarginalIntegrand, ← hweight i hi]
    ring
  change compactKappa p * compactZ p t = 2 * h / compactMarginalMeshDenominator h *
    ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h)
  rw [compactKappa_mul_compactZ_eq_gridAverage hp, gridAverage, ← hsum]
  rw [show compactMarginalMeshDenominator h = 2 * ((gaps p).length : ℝ) * h ^ 2 by
    linear_combination -2 * hmass]
  field_simp [hh.ne', (gaps_length_pos p).ne']

/-- The normalized Euler–Maclaurin quadrature with endpoint corrections through order four. -/
def compactMarginalQuadrature (h t : ℝ) : ℝ :=
  let f := regularizedMarginalIntegrand h t
  2 / compactMarginalMeshDenominator h *
    ((∫ x in (-1 : ℝ)..2, f x) + h / 2 * (f (-1) + f 2) +
      h ^ 2 / 12 * (iteratedDeriv 1 f 2 - iteratedDeriv 1 f (-1)) -
      h ^ 4 / 720 * (iteratedDeriv 3 f 2 - iteratedDeriv 3 f (-1)))

/-- The signed error in Pro equation (20), expressed as a sum of cell integrals.
The scaled kernel in `meshRemainder` includes the factor `h ^ 6`. -/
theorem compactKappa_mul_compactZ_sub_quadrature {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    compactKappa p * compactZ p t - compactMarginalQuadrature h t =
      2 / compactMarginalMeshDenominator h *
        meshRemainder (-1) h p
          (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) := by
  let h : ℝ := 3 / (p : ℝ)
  let f := regularizedMarginalIntegrand h t
  have hb : -1 + (p : ℝ) * h = 2 := by
    have hph : (p : ℝ) * h = 3 := mul_marginal_step hp
    rw [hph]
    norm_num
  have hsmooth : ContDiff ℝ ⊤ f := contDiff_regularizedMarginalIntegrand h t
  have hderiv (k : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hsmooth.differentiable_iteratedDeriv k (by simp)).differentiableAt.hasDerivAt
  have hsix : iteratedDeriv 6 f =
      (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) :=
    funext (iteratedDeriv_six_regularizedMarginalIntegrand h t)
  have hmesh := mesh_sum_eq (a := -1) (h := h) (n := p)
    (f0 := f) (f1 := iteratedDeriv 1 f) (f2 := iteratedDeriv 2 f)
    (f3 := iteratedDeriv 3 f) (f4 := iteratedDeriv 4 f) (f5 := iteratedDeriv 5 f)
    (f6 := iteratedDeriv 6 f) (by simpa only [iteratedDeriv_zero] using hderiv 0)
    (hderiv 1) (hderiv 2) (hderiv 3) (hderiv 4) (hderiv 5)
    (hsmooth.continuous_iteratedDeriv 6 le_top)
  rw [hb, hsix] at hmesh
  rw [compactKappa_mul_compactZ_eq_mesh_sum hp t]
  change 2 * h / compactMarginalMeshDenominator h *
      (∑ i ∈ Finset.range (p + 1), f (-1 + (i : ℝ) * h)) -
      compactMarginalQuadrature h t = _
  rw [mul_div_right_comm (2 : ℝ) h, mul_assoc, hmesh]
  unfold compactMarginalQuadrature
  ring

end RefinedBMV.PositiveCenter

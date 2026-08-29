/- GID: D5/S3/Weil/Budget/MultiscaleLoewnerConstraint
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/MultiscaleLoewnerConstraint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One positive spectrum forces its multiscale budget matrix to be positive semidefinite. -/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches for Loewner matrices, Stieltjes budgets, divided differences,
     and the resolvent-kernel body found no exact D5 owner or canonical definition.
   * Pinned Mathlib supplies `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
     `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`, and finite-sum integration.
   * The displayed quotient requires distinct scales; injectivity records that implicit
     source-domain restriction. Integrability records that the positive-spectrum budget
     curve is finite at every positive scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Matrix Set
open scoped BigOperators

namespace D5.S3.Weil.Budget.MultiscaleLoewnerConstraint

/-- The divided-difference matrix of a common positive-spectrum resolvent budget is positive
semidefinite, with its diagonal computed from the actual derivative of the budget curve. -/
theorem multiscale_loewner_constraint
    (M : Nat) (nu : Measure Real) (scale : Fin M -> Real)
    (scalePositive : forall i, 0 < scale i)
    (scaleInjective : Function.Injective scale)
    (budgetIntegrable : forall t, 0 < t ->
      Integrable (fun xi : Real => (xi ^ 2 + t)⁻¹) nu) :
    let budget : Real -> Real := fun t => ∫ xi : Real, (xi ^ 2 + t)⁻¹ ∂nu
    let loewner : Matrix (Fin M) (Fin M) Real := fun i j =>
      if i = j then -deriv budget (scale i)
      else (budget (scale i) - budget (scale j)) / (scale j - scale i)
    PosSemidef loewner := by
  dsimp only
  have kernelIntegrable : forall i j,
      Integrable (fun xi : Real =>
        ((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹) nu := by
    intro i j
    have leftIntegrable := budgetIntegrable (scale i) (scalePositive i)
    have rightIntegrable := budgetIntegrable (scale j) (scalePositive j)
    have leftBound : forall xi : Real,
        ‖(xi ^ 2 + scale i)⁻¹‖ <= (scale i)⁻¹ := by
      intro xi
      have denominatorPositive : 0 < xi ^ 2 + scale i :=
        add_pos_of_nonneg_of_pos (sq_nonneg xi) (scalePositive i)
      rw [Real.norm_of_nonneg (inv_nonneg.mpr denominatorPositive.le)]
      exact inv_anti₀ (scalePositive i) (le_add_of_nonneg_left (sq_nonneg xi))
    have productIntegrable := rightIntegrable.bdd_mul leftIntegrable.aestronglyMeasurable
      (ae_of_all nu leftBound)
    simpa only [_root_.mul_inv_rev, mul_comm] using productIntegrable
  let kernel : Matrix (Fin M) (Fin M) Real := fun i j =>
    ∫ xi : Real, ((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ ∂nu
  have kernelHermitian : kernel.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [kernel, star_trivial]
    apply integral_congr_ae
    filter_upwards [] with xi
    rw [mul_comm]
  have kernelPSD : PosSemidef kernel := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg kernelHermitian
    intro x
    have quadraticIdentity :
        star x ⬝ᵥ (kernel *ᵥ x) =
          ∫ xi : Real, (∑ i, x i * (xi ^ 2 + scale i)⁻¹) ^ 2 ∂nu := by
      change (∑ i, x i * ∑ j,
        (∫ xi : Real, ((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ ∂nu) * x j) = _
      simp_rw [Finset.mul_sum]
      have termIntegral (i j : Fin M) :
          x i * ((∫ xi : Real,
            ((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ ∂nu) * x j) =
            ∫ xi : Real,
              x i * (((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ * x j) ∂nu := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
      simp_rw [termIntegral]
      have termIntegrable (i j : Fin M) :
          Integrable (fun xi : Real =>
            x i * (((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ * x j)) nu := by
        simpa [mul_assoc] using
          (kernelIntegrable i j).mul_const (x j) |>.const_mul (x i)
      have innerIntegral (i : Fin M) :
          (∑ j, ∫ xi : Real,
              x i * (((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ * x j) ∂nu) =
            ∫ xi : Real, ∑ j,
              x i * (((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ * x j) ∂nu := by
        exact (MeasureTheory.integral_finsetSum Finset.univ
          (fun j _ => termIntegrable i j)).symm
      simp_rw [innerIntegral]
      rw [← MeasureTheory.integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards [] with xi
        let total : Real := ∑ i, x i * (xi ^ 2 + scale i)⁻¹
        change (∑ i, ∑ j,
          x i * (((xi ^ 2 + scale i) * (xi ^ 2 + scale j))⁻¹ * x j)) = total ^ 2
        rw [pow_two total]
        dsimp only [total]
        rw [Finset.sum_mul]
        congr 1
        funext i
        rw [Finset.mul_sum]
        congr 1
        funext j
        field_simp
      · intro i _
        exact integrable_finsetSum Finset.univ (fun j _ => termIntegrable i j)
    rw [quadraticIdentity]
    exact integral_nonneg fun xi => sq_nonneg _
  have budgetDerivative : forall i,
      HasDerivAt
        (fun t => ∫ xi : Real, (xi ^ 2 + t)⁻¹ ∂nu)
        (-kernel i i) (scale i) := by
    intro i
    have halfPositive : 0 < scale i / 2 := half_pos (scalePositive i)
    have neighborhood : Ioi (scale i / 2) ∈ nhds (scale i) :=
      Ioi_mem_nhds (by linarith [scalePositive i])
    have halfIntegrable :
        Integrable (fun xi : Real => (xi ^ 2 + scale i / 2)⁻¹) nu :=
      budgetIntegrable _ halfPositive
    have resolventBound : forall xi : Real,
        ‖(xi ^ 2 + scale i / 2)⁻¹‖ <= 2 / scale i := by
      intro xi
      have denominatorPositive : 0 < xi ^ 2 + scale i / 2 :=
        add_pos_of_nonneg_of_pos (sq_nonneg xi) halfPositive
      rw [Real.norm_of_nonneg (inv_nonneg.mpr denominatorPositive.le)]
      calc
        (xi ^ 2 + scale i / 2)⁻¹ <= (scale i / 2)⁻¹ :=
          inv_anti₀ halfPositive (le_add_of_nonneg_left (sq_nonneg xi))
        _ = 2 / scale i := by field_simp
    have squareIntegrable :
        Integrable (fun xi : Real => (xi ^ 2 + scale i / 2)⁻¹ ^ 2) nu := by
      have productIntegrable := halfIntegrable.mul_bdd halfIntegrable.aestronglyMeasurable
        (ae_of_all nu resolventBound)
      simpa [pow_two] using productIntegrable
    have derivativeResult :=
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (F := fun t xi : Real => (xi ^ 2 + t)⁻¹)
        (F' := fun t xi : Real => -((xi ^ 2 + t)⁻¹ ^ 2))
        (bound := fun xi : Real => (xi ^ 2 + scale i / 2)⁻¹ ^ 2)
        neighborhood
        (by
          filter_upwards [Ioi_mem_nhds (scalePositive i)] with t ht
          exact (budgetIntegrable t ht).aestronglyMeasurable)
        (budgetIntegrable _ (scalePositive i))
        (by
          apply AEStronglyMeasurable.congr
            (kernelIntegrable i i).neg.aestronglyMeasurable
          filter_upwards [] with xi
          simp only [Pi.neg_apply, pow_two, _root_.mul_inv_rev])
        (by
          filter_upwards [] with xi
          intro t ht
          change scale i / 2 < t at ht
          have lowerDenominatorPositive : 0 < xi ^ 2 + scale i / 2 :=
            add_pos_of_nonneg_of_pos (sq_nonneg xi) halfPositive
          have denominatorPositive : 0 < xi ^ 2 + t := by
            linarith [sq_nonneg xi, ht]
          have inverseLe : (xi ^ 2 + t)⁻¹ <= (xi ^ 2 + scale i / 2)⁻¹ :=
            inv_anti₀ lowerDenominatorPositive (by linarith [ht])
          rw [norm_neg, norm_pow,
            Real.norm_of_nonneg (inv_nonneg.mpr denominatorPositive.le)]
          exact pow_le_pow_left₀ (inv_nonneg.mpr denominatorPositive.le) inverseLe 2)
        squareIntegrable
        (by
          filter_upwards [] with xi
          intro t ht
          change scale i / 2 < t at ht
          have denominatorNe : xi ^ 2 + t ≠ 0 := by
            exact ne_of_gt (by linarith [sq_nonneg xi, ht])
          have denominatorDerivative : HasDerivAt (fun y : Real => xi ^ 2 + y) 1 t :=
            (hasDerivAt_id t).const_add (xi ^ 2)
          have inverseDerivative := denominatorDerivative.inv denominatorNe
          change HasDerivAt (fun y : Real => (xi ^ 2 + y)⁻¹)
            (-1 / (xi ^ 2 + t) ^ 2) t at inverseDerivative
          convert! inverseDerivative using 1
          simp only [div_eq_mul_inv, neg_mul, one_mul, inv_pow])
    simpa only [kernel, pow_two, _root_.mul_inv_rev, MeasureTheory.integral_neg] using
      derivativeResult.2
  have loewnerEqKernel :
      (fun i j : Fin M =>
        if i = j then
          -deriv (fun t => ∫ xi : Real, (xi ^ 2 + t)⁻¹ ∂nu) (scale i)
        else
          ((∫ xi : Real, (xi ^ 2 + scale i)⁻¹ ∂nu) -
            (∫ xi : Real, (xi ^ 2 + scale j)⁻¹ ∂nu)) /
            (scale j - scale i)) = kernel := by
    funext i j
    by_cases hij : i = j
    · subst j
      simp only [if_pos]
      rw [(budgetDerivative i).deriv]
      simp
    · simp only [if_neg hij]
      have scaleNe : scale j - scale i ≠ 0 := sub_ne_zero.mpr (scaleInjective.ne hij).symm
      rw [← MeasureTheory.integral_sub (budgetIntegrable _ (scalePositive i))
        (budgetIntegrable _ (scalePositive j)), ← MeasureTheory.integral_div]
      apply integral_congr_ae
      filter_upwards [] with xi
      have leftNe : xi ^ 2 + scale i ≠ 0 :=
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg xi) (scalePositive i))
      have rightNe : xi ^ 2 + scale j ≠ 0 :=
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg xi) (scalePositive j))
      field_simp [leftNe, rightNe, scaleNe]
      ring
  rw [loewnerEqKernel]
  exact kernelPSD

#print axioms multiscale_loewner_constraint

end D5.S3.Weil.Budget.MultiscaleLoewnerConstraint

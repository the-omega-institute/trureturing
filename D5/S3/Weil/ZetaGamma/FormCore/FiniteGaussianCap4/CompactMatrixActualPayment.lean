/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixActualPayment
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual finite Gaussian compact debit and head-tail integral payment. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualHead
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4HeadTailPayment
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteGaussianCap475
open FiniteGaussianCap4

private theorem measurable_actual_compactDebit : Measurable compactDebit := by
  have hcap : Measurable capWeight := by
    unfold capWeight
    exact Measurable.ite measurableSet_Ioi
      (((measurable_id.div_const Real.pi).pow_const (5 / 2 : ℝ)).sub
        (((measurable_id.div_const Real.pi).pow_const (-7 / 2 : ℝ)).const_mul 4))
      measurable_const
  unfold compactDebit
  exact Measurable.ite measurableSet_Ioo
    (((measurable_id.pow_const (2 : ℕ)).div_const 10).sub hcap) measurable_const

private theorem compactDebit_weighted_square_integrable (f : ℝ → ℝ)
    (hf : IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * f x ^ 2) (Ioi 0)) :
    IntegrableOn (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * compactDebit x * f x ^ 2) (Ioi 0) := by
  have hmul := hf.bdd_mul measurable_actual_compactDebit.aestronglyMeasurable
    (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using compactDebit_abs_le_four x))
  simpa only [IntegrableOn, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The compact correction has precisely the same actual integral on the
positive half-line and on its fixed support interval. -/
theorem compactDebit_integral_Ioi_eq_interval (g : ℝ → ℝ) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x * g x) =
      ∫ x in 0..6, x ^ (7 / 2 : ℝ) * compactDebit x * g x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 6)]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (fun x hx => hx.1)
  intro x hx
  have hnot : ¬ (0 < x ∧ x < 6) := by
    intro h
    exact hx.2 ⟨h.1, h.2.le⟩
  simp only [compactDebit, if_neg hnot, mul_zero, zero_mul]

/-- The enclosed matrix is the compact quadratic form of the same actual
finite Gaussian prefix, on the full physical half-line. -/
theorem finiteGaussianPrefix_compact_quadratic {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
      finiteGaussianPartialSum c site 32 x ^ 2) =
      ∑ i, ∑ j, actualCentralHeadCoordinates c site i *
        actualCentralHeadCoordinates c site j * compactMomentMatrix i j := by
  have heq : centralHead (actualCentralHeadCoordinates c site) =
      finiteGaussianPartialSum c site 32 := by
    funext x
    exact centralHead_actual_prefix c site reflection hc hs x
  rw [← heq, compactDebit_integral_Ioi_eq_interval]
  exact (centralHead_compact_quadratic (actualCentralHeadCoordinates c site)).2

/-- The original head and tail square budgets pay the complete signed
compact debit. All four integrability obligations come from the actual
finite-source graph theorem and the proved uniform multiplier bound. -/
theorem finiteGaussian_compact_head_tail_payment {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) :
    -(∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
      finiteGaussianPartialSum c site 32 x ^ 2) -
      (2 / 5 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        finiteGaussianPartialSum c site 32 x ^ 2) -
      44 * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) ≤
    -(∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
      gaussianFeature c site x ^ 2) := by
  let P := finiteGaussianPartialSum c site 32
  let T := fun x => gaussianFeature c site x - P x
  have he := finiteGaussian_weighted_energy_convergence c site (7 / 2 : ℝ) (by norm_num)
  have hP : IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * P x ^ 2) (Ioi 0) := he.1 32
  have hT : IntegrableOn (fun x : ℝ => x ^ (7 / 2 : ℝ) * T x ^ 2) (Ioi 0) :=
    (finiteGaussian_weighted_centered_energy_convergence c site 32
      (7 / 2 : ℝ) (by norm_num)).2.1
  have hvP := compactDebit_weighted_square_integrable P hP
  have hvF := compactDebit_weighted_square_integrable (gaussianFeature c site) he.2.1
  have hle := integral_mono_ae
    ((hvP.neg.sub (hP.const_mul (2 / 5 : ℝ))).sub (hT.const_mul 44))
    hvF.neg (show ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      -(x ^ (7 / 2 : ℝ) * compactDebit x * P x ^ 2) -
        (2 / 5 : ℝ) * (x ^ (7 / 2 : ℝ) * P x ^ 2) -
        44 * (x ^ (7 / 2 : ℝ) * T x ^ 2) ≤
      -(x ^ (7 / 2 : ℝ) * compactDebit x * gaussianFeature c site x ^ 2) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := mul_le_mul_of_nonneg_left (compactDebit_head_tail_payment x (P x) (T x))
        (Real.rpow_nonneg hx.le (7 / 2 : ℝ))
      have hsplit : P x + T x = gaussianFeature c site x := by dsimp only [T]; ring
      rw [hsplit] at h
      convert h using 1 <;> ring)
  have hint2 := integral_sub (hvP.neg.sub (hP.const_mul (2 / 5 : ℝ))) (hT.const_mul 44)
  have hint1 := integral_sub hvP.neg (hP.const_mul (2 / 5 : ℝ))
  simp only [Pi.sub_apply, Pi.neg_apply] at hle hint2 hint1
  rw [hint2, hint1] at hle
  simpa only [integral_neg, integral_const_mul, P, T] using hle

/-- The preceding physical payment now consumes the actual enclosed matrix;
no expansion, normalization, or matrix-integral bridge is assumed. -/
theorem finiteGaussian_matrix_head_tail_payment {ι : Type*} [Fintype ι]
    (c site : ι → ℝ) (reflection : Equiv.Perm ι)
    (hc : ∀ i, c (reflection i) = c i)
    (hs : ∀ i, site (reflection i) = -site i) :
    -(∑ i, ∑ j, actualCentralHeadCoordinates c site i *
        actualCentralHeadCoordinates c site j * compactMomentMatrix i j) -
      (2 / 5 : ℝ) * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        finiteGaussianPartialSum c site 32 x ^ 2) -
      44 * (∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) *
        (gaussianFeature c site x - finiteGaussianPartialSum c site 32 x) ^ 2) ≤
    -(∫ x in Ioi (0 : ℝ), x ^ (7 / 2 : ℝ) * compactDebit x *
      gaussianFeature c site x ^ 2) := by
  rw [← finiteGaussianPrefix_compact_quadratic c site reflection hc hs]
  exact finiteGaussian_compact_head_tail_payment c site

end FiniteGaussianCap475

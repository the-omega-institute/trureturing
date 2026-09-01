/- GID: D5/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/NegativeSquareLaplaceResolvent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A negative-square mode has an exact damping threshold and Laplace resolvent. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `NegativeSquareLaplaceResolvent`, the exact
     stabilization gap, and the target integral found research targets but no
     Lean owner. Existing resolvent modules concern different jet or operator
     constructions and do not prove this scalar threshold.
   * The frozen reflected-pair owners supply the signed spectral value
     `reflectionPairSignedDeterminant delta = -delta^2`. This module imports and
     applies that theorem directly.
   * Pinned Mathlib supplies `integrableOn_exp_mul_Ioi`,
     `integral_exp_mul_Ioi`, `integrableOn_const_iff`, and `volume_Ioi`.
     Those declarations discharge the improper-integral and necessity legs;
     the exponential integral is not reproved.
   * The resolvent is scalar and real. It records the damping debt of a
     negative-square mode and does not construct a global zeta resolvent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.NegativeSquareLaplaceResolvent

open Set MeasureTheory
open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum

/-- Damping minus the positive growth debt carried by the negative spectral atom. -/
def stabilizationGap (delta damping : ℝ) : ℝ :=
  damping + reflectionPairSignedDeterminant delta

/-- The forward Laplace kernel after adding scalar damping. -/
def dampedNegativeSquareKernel (delta damping time : ℝ) : ℝ :=
  Real.exp (-(stabilizationGap delta damping * time))

/-- The scalar resolvent of the stabilized negative-square mode. -/
def negativeSquareResolvent (delta damping : ℝ) : ℝ :=
  (stabilizationGap delta damping)⁻¹

/-- The stabilization gap is exactly `damping - delta^2`. -/
theorem stabilization_gap_eq (delta damping : ℝ) :
    stabilizationGap delta damping = damping - delta ^ 2 := by
  unfold stabilizationGap
  rw [(reflection_pair_signed_determinant delta 0).2.1]
  ring

/-- Positive stabilization is equivalent to damping strictly exceeding the
squared reflected split. -/
theorem stabilization_gap_pos_iff (delta damping : ℝ) :
    0 < stabilizationGap delta damping ↔ delta ^ 2 < damping := by
  rw [stabilization_gap_eq]
  constructor <;> intro h <;> linarith

/-- The stabilized kernel is integrable above the exact damping threshold. -/
theorem damped_negative_square_kernel_integrable_of_threshold
    (delta damping : ℝ) (hthreshold : delta ^ 2 < damping) :
    IntegrableOn (dampedNegativeSquareKernel delta damping) (Ioi 0) := by
  have hgap : 0 < stabilizationGap delta damping :=
    (stabilization_gap_pos_iff delta damping).2 hthreshold
  have hcoefficient : -(stabilizationGap delta damping) < 0 :=
    neg_lt_zero.mpr hgap
  simpa only [dampedNegativeSquareKernel] using
    (integrableOn_exp_mul_Ioi
      (a := -(stabilizationGap delta damping)) hcoefficient 0)

/-- Integrability on the forward half-line holds exactly above the damping
threshold. -/
theorem damped_negative_square_kernel_integrable_iff
    (delta damping : ℝ) :
    IntegrableOn (dampedNegativeSquareKernel delta damping) (Ioi 0) ↔
      delta ^ 2 < damping := by
  constructor
  · intro hintegrable
    by_contra hthreshold
    have hgap_nonpos : stabilizationGap delta damping ≤ 0 := by
      rw [stabilization_gap_eq]
      linarith
    have hcoefficient_nonneg : 0 ≤ -(stabilizationGap delta damping) := by
      linarith
    have hone_integrable :
        IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
      refine Integrable.mono' hintegrable (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with time htime
      have htime_nonneg : 0 ≤ time := le_of_lt htime
      have hargument_nonneg :
          0 ≤ -(stabilizationGap delta damping * time) := by
        rw [neg_mul]
        exact mul_nonneg hcoefficient_nonneg htime_nonneg
      have hone_le :
          1 ≤ Real.exp (-(stabilizationGap delta damping * time)) :=
        Real.one_le_exp hargument_nonneg
      simpa [dampedNegativeSquareKernel, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)] using hone_le
    have hone_not_integrable :
        ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
      simp
    exact hone_not_integrable hone_integrable
  · exact damped_negative_square_kernel_integrable_of_threshold delta damping

/-- Above threshold, the improper integral is the scalar resolvent. -/
theorem integral_damped_negative_square_kernel
    (delta damping : ℝ) (hthreshold : delta ^ 2 < damping) :
    (∫ time : ℝ in Ioi 0, dampedNegativeSquareKernel delta damping time) =
      negativeSquareResolvent delta damping := by
  have hgap : 0 < stabilizationGap delta damping :=
    (stabilization_gap_pos_iff delta damping).2 hthreshold
  have hcoefficient : -(stabilizationGap delta damping) < 0 :=
    neg_lt_zero.mpr hgap
  simpa [dampedNegativeSquareKernel, negativeSquareResolvent,
    hgap.ne'] using
    (integral_exp_mul_Ioi
      (a := -(stabilizationGap delta damping)) hcoefficient 0)

/-- The resolvent denominator vanishes exactly at the negative-square
stabilization threshold. -/
theorem stabilization_gap_eq_zero_iff (delta damping : ℝ) :
    stabilizationGap delta damping = 0 ↔ damping = delta ^ 2 := by
  rw [stabilization_gap_eq]
  constructor <;> intro h <;> linarith

/-- The scalar resolvent is positive exactly on the integrable side of the
threshold. -/
theorem negative_square_resolvent_pos_iff (delta damping : ℝ) :
    0 < negativeSquareResolvent delta damping ↔ delta ^ 2 < damping := by
  rw [negativeSquareResolvent, inv_pos, stabilization_gap_pos_iff]

/-- Above threshold, multiplying by the stabilization gap gives the identity. -/
theorem stabilization_gap_mul_resolvent
    (delta damping : ℝ) (hthreshold : delta ^ 2 < damping) :
    stabilizationGap delta damping * negativeSquareResolvent delta damping = 1 := by
  have hgap : stabilizationGap delta damping ≠ 0 :=
    ((stabilization_gap_pos_iff delta damping).2 hthreshold).ne'
  simp [negativeSquareResolvent, hgap]

/-- The exact scalar package: threshold, integrability, integral value, and
positive resolvent all agree. -/
theorem negative_square_laplace_resolvent
    (delta damping : ℝ) :
    (IntegrableOn (dampedNegativeSquareKernel delta damping) (Ioi 0) ↔
        delta ^ 2 < damping) ∧
      (delta ^ 2 < damping →
        (∫ time : ℝ in Ioi 0,
          dampedNegativeSquareKernel delta damping time) =
            negativeSquareResolvent delta damping) ∧
      (0 < negativeSquareResolvent delta damping ↔
        delta ^ 2 < damping) ∧
      (stabilizationGap delta damping = 0 ↔
        damping = delta ^ 2) := by
  exact ⟨damped_negative_square_kernel_integrable_iff delta damping,
    integral_damped_negative_square_kernel delta damping,
    negative_square_resolvent_pos_iff delta damping,
    stabilization_gap_eq_zero_iff delta damping⟩

/-- The threshold hypotheses are inhabited. -/
example :
    (∫ time : ℝ in Ioi 0, dampedNegativeSquareKernel 1 2 time) = 1 := by
  have hthreshold : (1 : ℝ) ^ 2 < 2 := by norm_num
  rw [integral_damped_negative_square_kernel 1 2 hthreshold]
  norm_num [negativeSquareResolvent, stabilizationGap,
    reflectionPairSignedDeterminant, pairDeterminant, reflectedGenerator]

#print axioms damped_negative_square_kernel_integrable_iff
#print axioms integral_damped_negative_square_kernel
#print axioms negative_square_laplace_resolvent

end D5.S3.Analytic.Adelic.NegativeSquareLaplaceResolvent

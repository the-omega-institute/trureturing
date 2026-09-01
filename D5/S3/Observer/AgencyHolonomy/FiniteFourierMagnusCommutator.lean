/- GID: D5/S3/Observer/AgencyHolonomy/FiniteFourierMagnusCommutator
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/FiniteFourierMagnusCommutator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expand the commutator of a finite Fourier-valued algebra generator with the frozen second-Magnus slot kernel as its exact coefficient. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic

/-!
# Finite Fourier generator commutator

The frozen alternating slot kernel was introduced as the finite coefficient
expected in the second Magnus term. This module closes that algebraic bridge.
For a finite family of elements of any complex associative algebra, the
commutator of the two Fourier syntheses at times `time1` and `time2` is the
double sum of algebra products weighted by the existing slot kernel.

No time-ordered exponential, Bochner integral, Magnus-series convergence,
unbounded-operator domain, infinite frequency limit, or zeta realization is
asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Observer.AgencyHolonomy.FiniteFourierMagnusCommutator

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

universe u v

/-- Finite Fourier synthesis with values in a complex associative algebra. -/
noncomputable def finiteFourierAlgebraGenerator
    {ι : Type u} {A : Type v} [Fintype ι] [Ring A] [Algebra ℂ A]
    (generator : ι → A) (frequency : ι → ℝ) (time : ℝ) : A :=
  ∑ p, fourierPhase (frequency p) time • generator p

/-- The algebra commutator used by the second Magnus coefficient. -/
def algebraCommutator
    {A : Type v} [Ring A] (left right : A) : A :=
  left * right - right * left

/-- The commutator of two finite Fourier generators expands exactly with the
frozen alternating slot kernel. -/
theorem finite_fourier_algebra_generator_commutator_expansion
    {ι : Type u} {A : Type v} [Fintype ι] [Ring A] [Algebra ℂ A]
    (generator : ι → A) (frequency : ι → ℝ) (time1 time2 : ℝ) :
    algebraCommutator
        (finiteFourierAlgebraGenerator generator frequency time1)
        (finiteFourierAlgebraGenerator generator frequency time2) =
      ∑ p, ∑ q,
        secondMagnusSwapKernel
            (frequency p) (frequency q) time1 time2 •
          (generator p * generator q) := by
  classical
  unfold algebraCommutator finiteFourierAlgebraGenerator
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← sub_smul]
  unfold secondMagnusSwapKernel
  congr 1
  ring

/-- At equal times the finite Fourier generator commutes with itself and the
kernel expansion vanishes term by term. -/
theorem finite_fourier_algebra_generator_equal_time_commutator
    {ι : Type u} {A : Type v} [Fintype ι] [Ring A] [Algebra ℂ A]
    (generator : ι → A) (frequency : ι → ℝ) (time : ℝ) :
    algebraCommutator
        (finiteFourierAlgebraGenerator generator frequency time)
        (finiteFourierAlgebraGenerator generator frequency time) = 0 := by
  simp [algebraCommutator]

/-- If the algebra generators commute pairwise, every Fourier-time
commutator vanishes. -/
theorem finite_fourier_algebra_generator_commutator_eq_zero_of_pairwise
    {ι : Type u} {A : Type v} [Fintype ι] [Ring A] [Algebra ℂ A]
    (generator : ι → A) (frequency : ι → ℝ) (time1 time2 : ℝ)
    (hCommute : ∀ p q, generator p * generator q = generator q * generator p) :
    algebraCommutator
        (finiteFourierAlgebraGenerator generator frequency time1)
        (finiteFourierAlgebraGenerator generator frequency time2) = 0 := by
  rw [finite_fourier_algebra_generator_commutator_expansion]
  classical
  let swap : ι × ι ≃ ι × ι := Equiv.prodComm ι ι
  have hSwap :
      (∑ p, ∑ q,
          secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 •
            (generator p * generator q)) =
        -(∑ p, ∑ q,
          secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 •
            (generator p * generator q)) := by
    calc
      (∑ p, ∑ q,
          secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 •
            (generator p * generator q)) =
          ∑ pair : ι × ι,
            secondMagnusSwapKernel
                (frequency pair.1) (frequency pair.2) time1 time2 •
              (generator pair.1 * generator pair.2) := by
            simp [Fintype.sum_prod_type]
      _ = ∑ pair : ι × ι,
            secondMagnusSwapKernel
                (frequency pair.2) (frequency pair.1) time1 time2 •
              (generator pair.2 * generator pair.1) := by
            exact Fintype.sum_equiv swap _ _ (fun _ => rfl)
      _ = -(∑ pair : ι × ι,
            secondMagnusSwapKernel
                (frequency pair.1) (frequency pair.2) time1 time2 •
              (generator pair.1 * generator pair.2)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro pair hpair
            rw [second_magnus_swap_kernel_swap_frequency,
              hCommute pair.2 pair.1]
            simp
      _ = -(∑ p, ∑ q,
          secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 •
            (generator p * generator q)) := by
            simp [Fintype.sum_prod_type]
  have hTwo :
      (2 : ℕ) • (∑ p, ∑ q,
          secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 •
            (generator p * generator q)) = 0 := by
    rw [two_nsmul, hSwap, add_neg_cancel]
  exact (nsmul_eq_zero_iff_right (by norm_num : (2 : ℕ) ≠ 0)).mp hTwo

#print axioms finite_fourier_algebra_generator_commutator_expansion
#print axioms finite_fourier_algebra_generator_equal_time_commutator
#print axioms finite_fourier_algebra_generator_commutator_eq_zero_of_pairwise

end D5.S3.Observer.AgencyHolonomy.FiniteFourierMagnusCommutator

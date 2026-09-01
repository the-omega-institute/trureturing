/- GID: D5/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen Fourier swap kernel is exactly the coefficient of represented degree-two free-Lie commutators in a finite matrix generator. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import D5.S3.Observer.Chronology.StepTwoFreeLieBridge
import Mathlib.Tactic

/-!
# Prime Fourier Magnus commutator bridge

A finite time-dependent matrix generator is assembled from fixed channel
matrices with the frozen Fourier characters. Bilinearity expands the
commutator at two times into represented degree-two free-Lie brackets. After
exchanging the two finite summation indices in the reversed product, the
coefficient of each ordered matrix product is exactly the frozen
`secondMagnusSwapKernel`.

This establishes the missing algebraic bridge between Fourier dispersion,
free-Lie degree two, and the second-Magnus swap kernel. It is finite and
purely algebraic. It does not integrate over a time simplex, construct a
continuous propagator, prove Magnus-series convergence, control an infinite
prime family, locate zeta zeros, or prove RH.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.AgencyHolonomy.PrimeFourierMagnusCommutatorBridge

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
open D5.S3.Observer.Chronology.StepTwoFreeLieBridge
open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

noncomputable section

universe u v

/-- Finite matrix generator with Fourier-rotated channel amplitudes. -/
def finiteFourierMatrixGenerator
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (frequency : ι → ℝ)
    (generator : ι → Matrix n n ℂ)
    (time : ℝ) : Matrix n n ℂ :=
  ∑ p, fourierPhase (frequency p) time • generator p

/-- Commuting two finite weighted generators expands into the weighted sum of
all represented degree-two free-Lie brackets. -/
theorem finite_weighted_generator_commutator
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (weight1 weight2 : ι → ℂ)
    (generator : ι → Matrix n n ℂ) :
    commutator
        (∑ p, weight1 p • generator p)
        (∑ p, weight2 p • generator p) =
      ∑ p, ∑ q,
        (weight1 p * weight2 q) •
          commutator (generator p) (generator q) := by
  classical
  unfold commutator
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm]
  simp_rw [Finset.sum_sub_distrib, ← Finset.sum_smul, smul_sub]
  abel

private theorem swapped_weighted_product_sum
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (weight1 weight2 : ι → ℂ)
    (generator : ι → Matrix n n ℂ) :
    (∑ p, ∑ q,
        (weight1 p * weight2 q) •
          (generator q * generator p)) =
      ∑ p, ∑ q,
        (weight1 q * weight2 p) •
          (generator p * generator q) := by
  rw [Finset.sum_comm]

/-- Pairing the reversed product by exchanging finite indices produces the
alternating coefficient of each ordered matrix product. -/
theorem finite_weighted_commutator_alternant
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (weight1 weight2 : ι → ℂ)
    (generator : ι → Matrix n n ℂ) :
    (∑ p, ∑ q,
        (weight1 p * weight2 q) •
          commutator (generator p) (generator q)) =
      ∑ p, ∑ q,
        (weight1 p * weight2 q -
          weight1 q * weight2 p) •
            (generator p * generator q) := by
  classical
  unfold commutator
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  rw [swapped_weighted_product_sum]
  simp_rw [sub_smul]
  abel

/-- The finite Fourier-generator commutator is a sum of represented formal
free-Lie brackets. -/
theorem finite_fourier_generator_freeLie_expansion
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (frequency : ι → ℝ)
    (generator : ι → Matrix n n ℂ)
    (time1 time2 : ℝ) :
    commutator
        (finiteFourierMatrixGenerator frequency generator time1)
        (finiteFourierMatrixGenerator frequency generator time2) =
      ∑ p, ∑ q,
        (fourierPhase (frequency p) time1 *
          fourierPhase (frequency q) time2) •
          freeLieEvaluation generator (freeLieDegreeTwo p q) := by
  rw [finite_weighted_generator_commutator]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [freeLieEvaluation_degreeTwo]
  rfl

/-- The frozen second-Magnus swap kernel is exactly the ordered-product
coefficient in the two-time generator commutator. -/
theorem finite_fourier_generator_secondMagnus_expansion
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (frequency : ι → ℝ)
    (generator : ι → Matrix n n ℂ)
    (time1 time2 : ℝ) :
    commutator
        (finiteFourierMatrixGenerator frequency generator time1)
        (finiteFourierMatrixGenerator frequency generator time2) =
      ∑ p, ∑ q,
        secondMagnusSwapKernel
            (frequency p) (frequency q) time1 time2 •
          (generator p * generator q) := by
  rw [finite_weighted_generator_commutator,
    finite_weighted_commutator_alternant]
  rfl

/-- If all channel matrices commute pairwise, the finite two-time Fourier
commutator vanishes. -/
theorem finite_fourier_generator_commutator_eq_zero_of_pairwise
    {ι : Type u} {n : Type v}
    [Fintype ι] [Fintype n] [DecidableEq n]
    (frequency : ι → ℝ)
    (generator : ι → Matrix n n ℂ)
    (time1 time2 : ℝ)
    (hCommute : ∀ p q,
      commutator (generator p) (generator q) = 0) :
    commutator
        (finiteFourierMatrixGenerator frequency generator time1)
        (finiteFourierMatrixGenerator frequency generator time2) = 0 := by
  rw [finite_fourier_generator_freeLie_expansion]
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  rw [freeLieEvaluation_degreeTwo, hCommute]
  simp [commutator] at hCommute
  simp [hCommute]

example (frequency : Fin 1 → ℝ)
    (generator : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ)
    (time1 time2 : ℝ) :
    commutator
        (finiteFourierMatrixGenerator frequency generator time1)
        (finiteFourierMatrixGenerator frequency generator time2) = 0 := by
  apply finite_fourier_generator_commutator_eq_zero_of_pairwise
  intro p q
  have hpq : p = q := Subsingleton.elim p q
  subst q
  simp [commutator]

#print axioms finite_weighted_generator_commutator
#print axioms finite_weighted_commutator_alternant
#print axioms finite_fourier_generator_freeLie_expansion
#print axioms finite_fourier_generator_secondMagnus_expansion
#print axioms finite_fourier_generator_commutator_eq_zero_of_pairwise

end

end D5.S3.Observer.AgencyHolonomy.PrimeFourierMagnusCommutatorBridge

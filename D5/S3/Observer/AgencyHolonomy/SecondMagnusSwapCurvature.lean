/- GID: D5/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/SecondMagnusSwapCurvature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The alternating Fourier slot kernel modulates finite holonomy into a bounded second-Magnus energy. -/

import D5.S3.Observer.AgencyHolonomy.TimeOrderedPrimeMemoryCocycle
import D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Second-Magnus swap curvature

For two frequencies and two time slots, the determinant-like Fourier kernel

`K_pq(t1,t2) = chi_p(t1) * chi_q(t2) - chi_q(t1) * chi_p(t2)`

is alternating under either frequency exchange or time-slot exchange. It
vanishes on the equal-time and equal-frequency diagonals and has norm at most
two. Center and relative coordinates factor the kernel into a unitary mean
phase and an odd relative-frequency sine.

Multiplying this kernel by any finite curvature field gives a pointwise
second-Magnus precursor. Its finite squared-norm energy is nonnegative and is
bounded by four times the existing finite holonomy energy. Specializing the
curvature field to stable residual swap curvature composes that estimate with
the existing residual envelope bound.

This file formalizes a finite algebraic slot kernel and energy estimate. It
does not construct a time-ordered exponential, integrate over an ordered time
simplex, prove convergence of a Magnus series, give a reverse coercive bound,
exclude resonant cancellation, dominate zero-side odd energy, locate zeta
zeros, or prove RH.
-/

/- Library-search audit trail (2026-09-01):
   * `PrimeFrequencyPhaseFlow` owns the unitary Fourier character.
   * `TimeOrderedPrimeMemoryCocycle` owns finite chronological affine words and
     their adjacent-swap memory curvature.
   * `FiniteHolonomyEnergy` owns the unweighted ordered-pair curvature energy
     and its stable residual envelope estimate.
   * Pinned Mathlib supplies `Complex.exp_add`, `Complex.two_sin`, complex
     norms, finite sums, and ordered-field square monotonicity.
   * Repository search found no existing owner of the alternating two-slot
     Fourier determinant or its finite energy domination theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.StableResidualSwapCurvatureBound
open D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy

noncomputable section

universe u

/-- The alternating Fourier determinant obtained by exchanging two frequency
channels between two fixed time slots. -/
noncomputable def secondMagnusSwapKernel
    (frequencyP frequencyQ time1 time2 : ℝ) : ℂ :=
  fourierPhase frequencyP time1 * fourierPhase frequencyQ time2 -
    fourierPhase frequencyQ time1 * fourierPhase frequencyP time2

/-- The finite ordered-pair energy after multiplying each curvature entry by
the second-Magnus Fourier slot kernel. -/
noncomputable def finiteSecondMagnusEnergy
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ)
    (curvature : ι → ι → ℂ)
    (time1 time2 : ℝ) : ℝ :=
  ∑ p, ∑ q,
    ‖secondMagnusSwapKernel
        (frequency p) (frequency q) time1 time2 * curvature p q‖ ^ 2

/-- The second-Magnus energy obtained from stable residual swap curvature. -/
noncomputable def stableResidualSecondMagnusEnergy
    {ι : Type u} [Fintype ι]
    (stable : ℂ)
    (residual channel : ι → ℂ)
    (frequency : ι → ℝ)
    (time1 time2 : ℝ) : ℝ :=
  finiteSecondMagnusEnergy frequency
    (fun p q =>
      stableResidualSwapCurvature stable
        (residual p) (residual q) (channel p) (channel q))
    time1 time2

/-- Exchanging the two frequency labels reverses the orientation of the slot
kernel. -/
theorem second_magnus_swap_kernel_swap_frequency
    (frequencyP frequencyQ time1 time2 : ℝ) :
    secondMagnusSwapKernel frequencyQ frequencyP time1 time2 =
      -secondMagnusSwapKernel frequencyP frequencyQ time1 time2 := by
  unfold secondMagnusSwapKernel
  ring

/-- Exchanging the two time slots reverses the orientation of the slot
kernel. -/
theorem second_magnus_swap_kernel_swap_time
    (frequencyP frequencyQ time1 time2 : ℝ) :
    secondMagnusSwapKernel frequencyP frequencyQ time2 time1 =
      -secondMagnusSwapKernel frequencyP frequencyQ time1 time2 := by
  unfold secondMagnusSwapKernel
  ring

/-- The two-slot kernel vanishes on the equal-time diagonal. -/
theorem second_magnus_swap_kernel_equal_times
    (frequencyP frequencyQ time : ℝ) :
    secondMagnusSwapKernel frequencyP frequencyQ time time = 0 := by
  unfold secondMagnusSwapKernel
  ring

/-- The two-slot kernel vanishes on the equal-frequency diagonal. -/
theorem second_magnus_swap_kernel_equal_frequencies
    (frequency time1 time2 : ℝ) :
    secondMagnusSwapKernel frequency frequency time1 time2 = 0 := by
  unfold secondMagnusSwapKernel
  ring

/-- A difference of two unit-modulus phase products has norm at most two. -/
theorem second_magnus_swap_kernel_norm_le_two
    (frequencyP frequencyQ time1 time2 : ℝ) :
    ‖secondMagnusSwapKernel frequencyP frequencyQ time1 time2‖ ≤ 2 := by
  have hP1 : ‖fourierPhase frequencyP time1‖ = 1 :=
    (fourier_phase_character_laws frequencyP 0 time1 0).2.2.2.1
  have hP2 : ‖fourierPhase frequencyP time2‖ = 1 :=
    (fourier_phase_character_laws frequencyP 0 time2 0).2.2.2.1
  have hQ1 : ‖fourierPhase frequencyQ time1‖ = 1 :=
    (fourier_phase_character_laws frequencyQ 0 time1 0).2.2.2.1
  have hQ2 : ‖fourierPhase frequencyQ time2‖ = 1 :=
    (fourier_phase_character_laws frequencyQ 0 time2 0).2.2.2.1
  unfold secondMagnusSwapKernel
  calc
    ‖fourierPhase frequencyP time1 * fourierPhase frequencyQ time2 -
        fourierPhase frequencyQ time1 * fourierPhase frequencyP time2‖ ≤
      ‖fourierPhase frequencyP time1 * fourierPhase frequencyQ time2‖ +
        ‖fourierPhase frequencyQ time1 * fourierPhase frequencyP time2‖ :=
      norm_sub_le _ _
    _ = 2 := by
      rw [norm_mul, norm_mul, hP1, hP2, hQ1, hQ2]
      norm_num

private theorem first_slot_center_factorization
    (frequencyP frequencyQ time1 time2 : ℝ) :
    fourierPhase frequencyP time1 * fourierPhase frequencyQ time2 =
      fourierPhase ((frequencyP + frequencyQ) / 2) (time1 + time2) *
        fourierPhase ((frequencyP - frequencyQ) / 2) (time1 - time2) := by
  unfold fourierPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem second_slot_center_factorization
    (frequencyP frequencyQ time1 time2 : ℝ) :
    fourierPhase frequencyQ time1 * fourierPhase frequencyP time2 =
      fourierPhase ((frequencyP + frequencyQ) / 2) (time1 + time2) *
        fourierPhase (-((frequencyP - frequencyQ) / 2))
          (time1 - time2) := by
  unfold fourierPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Mean and relative coordinates separate the common unitary phase from the
alternating relative-frequency bracket. -/
theorem second_magnus_swap_kernel_center_decomposition
    (frequencyP frequencyQ time1 time2 : ℝ) :
    secondMagnusSwapKernel frequencyP frequencyQ time1 time2 =
      fourierPhase ((frequencyP + frequencyQ) / 2) (time1 + time2) *
        (fourierPhase ((frequencyP - frequencyQ) / 2) (time1 - time2) -
          fourierPhase (-((frequencyP - frequencyQ) / 2))
            (time1 - time2)) := by
  unfold secondMagnusSwapKernel
  rw [first_slot_center_factorization frequencyP frequencyQ time1 time2,
    second_slot_center_factorization frequencyP frequencyQ time1 time2]
  ring

private theorem fourier_phase_sub_neg_frequency_sine
    (frequency time : ℝ) :
    fourierPhase frequency time - fourierPhase (-frequency) time =
      (-2 * Complex.I) *
        Complex.sin (((time * frequency : ℝ) : ℂ)) := by
  let x : ℂ := ((time * frequency : ℝ) : ℂ)
  have hLeft :
      -Complex.I * (time : ℂ) * (frequency : ℂ) =
        -x * Complex.I := by
    dsimp [x]
    push_cast
    ring
  have hRight :
      -Complex.I * (time : ℂ) * ((-frequency : ℝ) : ℂ) =
        x * Complex.I := by
    dsimp [x]
    push_cast
    ring
  unfold fourierPhase
  rw [hLeft, hRight]
  calc
    Complex.exp (-x * Complex.I) - Complex.exp (x * Complex.I) =
        ((Complex.exp (-x * Complex.I) -
            Complex.exp (x * Complex.I)) * Complex.I) *
          (-Complex.I) := by
      rw [mul_assoc]
      simp [Complex.I_mul_I]
    _ = (2 * Complex.sin x) * (-Complex.I) := by
      rw [← Complex.two_sin]
    _ = (-2 * Complex.I) * Complex.sin x := by ring

/-- The centered bracket is the odd sine of half the time-frequency area. -/
theorem second_magnus_swap_kernel_sine_form
    (frequencyP frequencyQ time1 time2 : ℝ) :
    secondMagnusSwapKernel frequencyP frequencyQ time1 time2 =
      (-2 * Complex.I) *
        Complex.exp
          (-Complex.I * ((time1 + time2 : ℝ) : ℂ) *
            (((frequencyP + frequencyQ) / 2 : ℝ) : ℂ)) *
        Complex.sin
          ((((time1 - time2) *
            ((frequencyP - frequencyQ) / 2) : ℝ) : ℂ)) := by
  rw [second_magnus_swap_kernel_center_decomposition]
  rw [fourier_phase_sub_neg_frequency_sine]
  unfold fourierPhase
  ring

/-- The finite second-Magnus energy is nonnegative and never exceeds four
copies of the underlying finite holonomy energy. -/
theorem finite_second_magnus_energy_bound
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ)
    (curvature : ι → ι → ℂ)
    (time1 time2 : ℝ) :
    0 ≤ finiteSecondMagnusEnergy frequency curvature time1 time2 ∧
    finiteSecondMagnusEnergy frequency curvature time1 time2 ≤
      4 * finiteHolonomyEnergy curvature := by
  classical
  have hTermBound (p q : ι) :
      ‖secondMagnusSwapKernel
          (frequency p) (frequency q) time1 time2 * curvature p q‖ ^ 2 ≤
        4 * ‖curvature p q‖ ^ 2 := by
    rw [norm_mul]
    have hKernel :
        ‖secondMagnusSwapKernel
          (frequency p) (frequency q) time1 time2‖ ≤ 2 :=
      second_magnus_swap_kernel_norm_le_two
        (frequency p) (frequency q) time1 time2
    have hProduct :
        ‖secondMagnusSwapKernel
            (frequency p) (frequency q) time1 time2‖ *
            ‖curvature p q‖ ≤
          2 * ‖curvature p q‖ :=
      mul_le_mul_of_nonneg_right hKernel (norm_nonneg _)
    calc
      (‖secondMagnusSwapKernel
            (frequency p) (frequency q) time1 time2‖ *
          ‖curvature p q‖) ^ 2 ≤
          (2 * ‖curvature p q‖) ^ 2 := by
        exact
          (sq_le_sq₀
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg (by norm_num) (norm_nonneg _))).2 hProduct
      _ = 4 * ‖curvature p q‖ ^ 2 := by ring
  have hEnergyNonnegative :
      0 ≤ finiteSecondMagnusEnergy frequency curvature time1 time2 := by
    unfold finiteSecondMagnusEnergy
    exact Finset.sum_nonneg fun p hp =>
      Finset.sum_nonneg fun q hq => sq_nonneg _
  have hEnergyBound :
      finiteSecondMagnusEnergy frequency curvature time1 time2 ≤
        4 * finiteHolonomyEnergy curvature := by
    unfold finiteSecondMagnusEnergy finiteHolonomyEnergy
    calc
      (∑ p : ι, ∑ q : ι,
          ‖secondMagnusSwapKernel
              (frequency p) (frequency q) time1 time2 *
              curvature p q‖ ^ 2) ≤
          ∑ p : ι, ∑ q : ι, 4 * ‖curvature p q‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hTermBound p q
      _ = 4 * (∑ p : ι, ∑ q : ι, ‖curvature p q‖ ^ 2) := by
        simp only [Finset.mul_sum]
  exact ⟨hEnergyNonnegative, hEnergyBound⟩

/-- Composing the kernel estimate with the existing residual envelope theorem
makes residual decay sufficient for finite second-Magnus energy decay. -/
theorem stable_residual_second_magnus_energy_bound
    {ι : Type u} [Fintype ι]
    (stable : ℂ)
    (residual channel : ι → ℂ)
    (frequency : ι → ℝ)
    (time1 time2 envelope : ℝ)
    (hEnvelope : 0 ≤ envelope)
    (hChannel : ∀ p, ‖channel p‖ ≤ 1)
    (hResidual : ∀ p, ‖residual p‖ ≤ envelope) :
    0 ≤ stableResidualSecondMagnusEnergy
      stable residual channel frequency time1 time2 ∧
    stableResidualSecondMagnusEnergy
        stable residual channel frequency time1 time2 ≤
      4 * ((Fintype.card ι : ℝ) ^ 2 *
        (2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2) ^ 2) ∧
    (envelope = 0 →
      stableResidualSecondMagnusEnergy
        stable residual channel frequency time1 time2 = 0) := by
  have hSecond :=
    finite_second_magnus_energy_bound frequency
      (fun p q =>
        stableResidualSwapCurvature stable
          (residual p) (residual q) (channel p) (channel q))
      time1 time2
  have hHolonomy :=
    finite_stable_holonomy_energy_bound
      stable residual channel envelope hEnvelope hChannel hResidual
  have hNonnegative :
      0 ≤ stableResidualSecondMagnusEnergy
        stable residual channel frequency time1 time2 := by
    simpa [stableResidualSecondMagnusEnergy] using hSecond.1
  have hKernelToHolonomy :
      stableResidualSecondMagnusEnergy
          stable residual channel frequency time1 time2 ≤
        4 * stableResidualHolonomyEnergy stable residual channel := by
    simpa [stableResidualSecondMagnusEnergy,
      stableResidualHolonomyEnergy] using hSecond.2
  have hUpper :
      stableResidualSecondMagnusEnergy
          stable residual channel frequency time1 time2 ≤
        4 * ((Fintype.card ι : ℝ) ^ 2 *
          (2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2) ^ 2) := by
    calc
      stableResidualSecondMagnusEnergy
          stable residual channel frequency time1 time2 ≤
          4 * stableResidualHolonomyEnergy stable residual channel :=
        hKernelToHolonomy
      _ ≤ 4 * ((Fintype.card ι : ℝ) ^ 2 *
          (2 * ‖stable - 1‖ * envelope + 2 * envelope ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hHolonomy.2.1 (by norm_num)
  have hZeroEnvelope :
      envelope = 0 →
        stableResidualSecondMagnusEnergy
          stable residual channel frequency time1 time2 = 0 := by
    intro hEnvelopeZero
    have hHolonomyZero := hHolonomy.2.2.2 hEnvelopeZero
    have hUpperZero :
        stableResidualSecondMagnusEnergy
            stable residual channel frequency time1 time2 ≤ 0 := by
      calc
        stableResidualSecondMagnusEnergy
            stable residual channel frequency time1 time2 ≤
            4 * stableResidualHolonomyEnergy stable residual channel :=
          hKernelToHolonomy
        _ = 0 := by rw [hHolonomyZero]; norm_num
    exact le_antisymm hUpperZero hNonnegative
  exact ⟨hNonnegative, hUpper, hZeroEnvelope⟩

#print axioms second_magnus_swap_kernel_swap_frequency
#print axioms second_magnus_swap_kernel_swap_time
#print axioms second_magnus_swap_kernel_equal_times
#print axioms second_magnus_swap_kernel_equal_frequencies
#print axioms second_magnus_swap_kernel_norm_le_two
#print axioms second_magnus_swap_kernel_center_decomposition
#print axioms second_magnus_swap_kernel_sine_form
#print axioms finite_second_magnus_energy_bound
#print axioms stable_residual_second_magnus_energy_bound

end

end D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

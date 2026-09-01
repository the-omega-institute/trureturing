/- GID: D5/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge
   generality: I
   mirror-B: D5/B/S3/Observer/Chronology/PrimeFourierMagnusCommutatorBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two-channel Fourier commutator is the second-Magnus swap kernel times the interpreted free-Lie bracket. -/

import D5.S3.Observer.Chronology.StepTwoFreeLieBridge
import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Prime Fourier-Magnus commutator bridge

Given two matrix channels `Bₚ,B_q`, form the Fourier-modulated generator

`A(t) = chi_p(t) • Bₚ + chi_q(t) • B_q`.

Its two-time commutator factors exactly as

`[A(t₁),A(t₂)] = K_pq(t₁,t₂) • [Bₚ,B_q]`,

where `K_pq` is the frozen second-Magnus swap kernel.  The channel commutator
is also the image of the universal free-Lie degree-two word under the matrix
interpretation.  This provides the missing finite bridge from Fourier time
and chronological orientation to an actual noncommutative transport algebra.

The theorem is finite and two-channel.  It does not sum an infinite prime
family, integrate over a time simplex, establish convergence of a Magnus
series, or connect the resulting matrix spectrum to zeta zeros.
-/

/- Library-search audit trail (2026-09-01):
   * `SecondMagnusSwapCurvature` owns the alternating scalar slot kernel.
   * `StepTwoFreeLieBridge` owns the universal degree-two event bracket and its
     interpretation law.
   * Repository search found no theorem identifying the commutator of two
     Fourier-modulated matrix channels with the frozen kernel times the
     channel commutator.
   * Pinned Mathlib supplies finite matrix multiplication, scalar action, and
     the associative-algebra Lie structure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Chronology.PrimeFourierMagnusCommutatorBridge

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
open D5.S3.Observer.Chronology.StepTwoFreeLieBridge

noncomputable section

universe u v

/-- Associative matrix commutator. -/
def matrixCommutator
    {n : Type u} [Fintype n] [DecidableEq n]
    (left right : Matrix n n ℂ) : Matrix n n ℂ :=
  left * right - right * left

/-- Two Fourier-modulated matrix channels. -/
def twoChannelFourierGenerator
    {n : Type u} [Fintype n] [DecidableEq n]
    (frequencyP frequencyQ : ℝ)
    (channelP channelQ : Matrix n n ℂ)
    (time : ℝ) : Matrix n n ℂ :=
  fourierPhase frequencyP time • channelP +
    fourierPhase frequencyQ time • channelQ

/-- The matrix Lie bracket is the associative matrix commutator. -/
theorem matrix_lie_bracket_eq_commutator
    {n : Type u} [Fintype n] [DecidableEq n]
    (left right : Matrix n n ℂ) :
    ⁅left, right⁆ = matrixCommutator left right := by
  rfl

/-- The universal free-Lie pair maps to the matrix commutator of its two
channel interpretations. -/
theorem free_lie_degree_two_matrix_lift
    {Event : Type v} {n : Type u}
    [Fintype n] [DecidableEq n]
    (channel : Event → Matrix n n ℂ)
    (first second : Event) :
    FreeLieAlgebra.lift ℂ channel
        (freeLieDegreeTwo (R := ℂ) first second) =
      matrixCommutator (channel first) (channel second) := by
  rw [free_lie_degree_two_lift]
  rfl

/-- Exact two-channel Magnus factorization: the scalar alternating Fourier
kernel is the coefficient of the channel commutator. -/
theorem two_channel_fourier_commutator_factorization
    {n : Type u} [Fintype n] [DecidableEq n]
    (frequencyP frequencyQ time1 time2 : ℝ)
    (channelP channelQ : Matrix n n ℂ) :
    matrixCommutator
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time1)
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time2) =
      secondMagnusSwapKernel frequencyP frequencyQ time1 time2 •
        matrixCommutator channelP channelQ := by
  ext i j
  simp [matrixCommutator, twoChannelFourierGenerator,
    secondMagnusSwapKernel, Matrix.mul_apply, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul]
  ring

/-- The exact factorization written directly through the universal free-Lie
word and its matrix interpretation. -/
theorem two_channel_fourier_commutator_free_lie
    {Event : Type v} {n : Type u}
    [Fintype n] [DecidableEq n]
    (frequency : Event → ℝ)
    (channel : Event → Matrix n n ℂ)
    (first second : Event) (time1 time2 : ℝ) :
    matrixCommutator
        (twoChannelFourierGenerator
          (frequency first) (frequency second)
          (channel first) (channel second) time1)
        (twoChannelFourierGenerator
          (frequency first) (frequency second)
          (channel first) (channel second) time2) =
      secondMagnusSwapKernel
          (frequency first) (frequency second) time1 time2 •
        FreeLieAlgebra.lift ℂ channel
          (freeLieDegreeTwo (R := ℂ) first second) := by
  rw [two_channel_fourier_commutator_factorization,
    free_lie_degree_two_matrix_lift]

/-- Equal time slots erase the matrix second-Magnus commutator. -/
theorem two_channel_fourier_commutator_equal_time
    {n : Type u} [Fintype n] [DecidableEq n]
    (frequencyP frequencyQ time : ℝ)
    (channelP channelQ : Matrix n n ℂ) :
    matrixCommutator
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time)
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time) = 0 := by
  rw [two_channel_fourier_commutator_factorization,
    second_magnus_swap_kernel_equal_times]
  simp

/-- Commuting matrix channels erase the second-Magnus response at all times. -/
theorem two_channel_fourier_commutator_eq_zero_of_channels_commute
    {n : Type u} [Fintype n] [DecidableEq n]
    (frequencyP frequencyQ time1 time2 : ℝ)
    (channelP channelQ : Matrix n n ℂ)
    (hCommute : channelP * channelQ = channelQ * channelP) :
    matrixCommutator
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time1)
        (twoChannelFourierGenerator frequencyP frequencyQ
          channelP channelQ time2) = 0 := by
  rw [two_channel_fourier_commutator_factorization]
  have hZero : matrixCommutator channelP channelQ = 0 := by
    simp [matrixCommutator, hCommute]
  rw [hZero]
  simp

example :
    matrixCommutator
      (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [matrixCommutator]

#print axioms matrix_lie_bracket_eq_commutator
#print axioms free_lie_degree_two_matrix_lift
#print axioms two_channel_fourier_commutator_factorization
#print axioms two_channel_fourier_commutator_free_lie
#print axioms two_channel_fourier_commutator_equal_time
#print axioms two_channel_fourier_commutator_eq_zero_of_channels_commute

end

end D5.S3.Observer.Chronology.PrimeFourierMagnusCommutatorBridge

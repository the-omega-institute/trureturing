/- GID: D5/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/PrimeFourierMagnusCommutatorBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The second-Magnus Fourier swap kernel is exactly the scalar coefficient of the two-channel Lie commutator. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import D5.S3.Observer.Chronology.StepTwoFreeLieBridge
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-!
# Prime Fourier Magnus commutator bridge

For two frequency channels with Lie generators `Bₚ` and `B_q`, define the
Fourier-driven generator

`A(t) = χₚ(t) • Bₚ + χ_q(t) • B_q`.

Bilinearity and antisymmetry of the Lie bracket give the exact identity

`[A(t₁),A(t₂)] = Kₚq(t₁,t₂) • [Bₚ,B_q]`,

where `Kₚq` is the already frozen second-Magnus swap kernel. Thus the scalar
kernel is precisely the coefficient of the degree-two Lie direction. Taking
frequencies to be logarithms specializes the result to prime or natural
address channels.

This module proves an exact two-channel finite identity. It does not sum an
infinite prime family, integrate over a time simplex, prove Magnus-series
convergence, provide a nonresonance lower bound, locate zeta zeros, or prove
RH.
-/

/- Library-search audit trail (2026-09-01):
   * `SecondMagnusSwapCurvature` owns the alternating scalar kernel and its
     finite energy estimate.
   * `StepTwoFreeLieBridge` identifies the degree-two tensor alternant with the
     represented free Lie bracket.
   * Pinned Mathlib supplies bilinearity, scalar compatibility, self
     vanishing, and skew-symmetry of Lie brackets.
   * Repository search found no existing theorem making the frozen Fourier
     kernel the exact coefficient of a Lie commutator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencyHolonomy.PrimeFourierMagnusCommutatorBridge

open D5.S3.Observer.AgencyHolonomy.PrimeFrequencyPhaseFlow
open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

noncomputable section

universe u

variable {L : Type u}
variable [LieRing L] [Module ℂ L] [LieAlgebra ℂ L]

/-- Fourier-driven generator formed from two frequency channels. -/
def twoChannelFourierGenerator
    (frequencyP frequencyQ : ℝ)
    (generatorP generatorQ : L)
    (time : ℝ) : L :=
  fourierPhase frequencyP time • generatorP +
    fourierPhase frequencyQ time • generatorQ

/-- The second-Magnus swap kernel is exactly the coefficient of the
cross-channel Lie bracket. -/
theorem two_channel_fourier_lie_bracket
    (frequencyP frequencyQ time1 time2 : ℝ)
    (generatorP generatorQ : L) :
    ⁅twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time1,
      twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time2⁆ =
      secondMagnusSwapKernel frequencyP frequencyQ time1 time2 •
        ⁅generatorP, generatorQ⁆ := by
  simp only [twoChannelFourierGenerator, add_lie, lie_add,
    smul_lie, lie_smul, lie_self, smul_zero, zero_add, add_zero]
  rw [show ⁅generatorQ, generatorP⁆ = -⁅generatorP, generatorQ⁆ by
    simpa using (lie_skew generatorQ generatorP).symm]
  simp only [smul_neg, ← sub_smul, smul_smul]
  unfold secondMagnusSwapKernel
  congr 1
  ring

/-- Equal times make the two-channel Lie commutator vanish. -/
theorem two_channel_fourier_lie_bracket_equal_times
    (frequencyP frequencyQ time : ℝ)
    (generatorP generatorQ : L) :
    ⁅twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time,
      twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time⁆ = 0 := by
  simp

/-- Equal frequencies make the two-channel Fourier generator collinear at all
times, so the cross-time Lie commutator vanishes. -/
theorem two_channel_fourier_lie_bracket_equal_frequencies
    (frequency time1 time2 : ℝ)
    (generatorP generatorQ : L) :
    ⁅twoChannelFourierGenerator frequency frequency
        generatorP generatorQ time1,
      twoChannelFourierGenerator frequency frequency
        generatorP generatorQ time2⁆ = 0 := by
  rw [two_channel_fourier_lie_bracket]
  simp [second_magnus_swap_kernel_equal_frequencies]

/-- Commuting channel generators have no second-Magnus Lie curvature for any
frequency or time slots. -/
theorem two_channel_fourier_lie_bracket_eq_zero_of_commute
    (frequencyP frequencyQ time1 time2 : ℝ)
    (generatorP generatorQ : L)
    (hCommute : ⁅generatorP, generatorQ⁆ = 0) :
    ⁅twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time1,
      twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time2⁆ = 0 := by
  rw [two_channel_fourier_lie_bracket, hCommute, smul_zero]

/-- Reversing the two time slots negates the complete two-channel Lie
curvature. -/
theorem two_channel_fourier_lie_bracket_swap_time
    (frequencyP frequencyQ time1 time2 : ℝ)
    (generatorP generatorQ : L) :
    ⁅twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time2,
      twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time1⁆ =
      -⁅twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time1,
      twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time2⁆ := by
  simpa using
    (lie_skew
      (twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time2)
      (twoChannelFourierGenerator frequencyP frequencyQ
        generatorP generatorQ time1)).symm

/-- Natural address channels use logarithmic frequencies. Prime addresses are
the prime specialization of this exact identity. -/
theorem log_address_two_channel_lie_bracket
    (addressP addressQ : ℕ)
    (time1 time2 : ℝ)
    (generatorP generatorQ : L) :
    ⁅twoChannelFourierGenerator
        (Real.log (addressP : ℝ)) (Real.log (addressQ : ℝ))
        generatorP generatorQ time1,
      twoChannelFourierGenerator
        (Real.log (addressP : ℝ)) (Real.log (addressQ : ℝ))
        generatorP generatorQ time2⁆ =
      secondMagnusSwapKernel
        (Real.log (addressP : ℝ)) (Real.log (addressQ : ℝ))
        time1 time2 • ⁅generatorP, generatorQ⁆ := by
  exact two_channel_fourier_lie_bracket _ _ _ _ _ _

example :
    ⁅twoChannelFourierGenerator 0 0
        (0 : FreeLieAlgebra ℂ Bool) 0 0,
      twoChannelFourierGenerator 0 0
        (0 : FreeLieAlgebra ℂ Bool) 0 0⁆ = 0 := by
  simp

#print axioms two_channel_fourier_lie_bracket
#print axioms two_channel_fourier_lie_bracket_equal_times
#print axioms two_channel_fourier_lie_bracket_equal_frequencies
#print axioms two_channel_fourier_lie_bracket_eq_zero_of_commute
#print axioms two_channel_fourier_lie_bracket_swap_time
#print axioms log_address_two_channel_lie_bracket

end

end D5.S3.Observer.AgencyHolonomy.PrimeFourierMagnusCommutatorBridge

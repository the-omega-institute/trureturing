/- GID: D5/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery
   generality: I
   mirror-B: D5/B/S3/FluidDynamics/Fourier/AugmentedReadoutRecovery
   mirror-E: none(waiver:exact-symbolic-Fourier-family)
   anchors: []
   utility: none
   digest: One instantaneous transverse acceleration reading recovers the hidden amplitude on the two-parameter Fourier witness family exactly when the visible amplitude is nonzero. -/

import D5.S3.FluidDynamics.Fourier.LowModeReversalWitness
import Mathlib.Tactic.FieldSimp

/-!
# Recovery from an instantaneous augmented readout

This is recovery on the two-parameter witness family from an instantaneous
augmented readout. It is not recovery of arbitrary five-mode states, not recovery
from finite-time histories, and not PDE observability.

The low observation at mode (1,0), component 1, exposes alpha/2. The additional
acceleration at mode (0,1), component 0, has imaginary part -alpha*beta/4.
Thus alpha is always recovered, and beta is recovered exactly off alpha = 0.
At alpha = 0 every beta gives the same augmented readout.

These are the original family readings, related to the bundled Galerkin field
by `AdvectionClosureInstance.family_observation` and
`AdvectionClosureInstance.family_acceleration`.
All declarations concern identities and fibres for continuous real parameters;
they do not provide bounded enumeration, a checker, a numerical reduction, or
a certified finite instance. The results are derived from the repository family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.FluidDynamics.Fourier.AugmentedReadoutRecovery

open LowModeReversalWitness

/-- The low observation at mode (1,0), component 1, is exactly alpha/2. -/
theorem low_observation_visible (alpha beta : ℝ) :
    lowObservation alpha beta (1, 0) 1 = (alpha : ℂ) / 2 := by
  simp only [lowObservation, coefficient, Fin.sum_univ_four]
  norm_num [frequencySquared, frequency, inputAmplitude, Prod.mk.injEq, Fin.ext_iff]

/-- The complete low observation paired with one instantaneous transverse acceleration component. -/
def augmentedReadout (nu alpha beta : ℝ) : (Mode → Amplitude) × ℂ :=
  (lowObservation alpha beta, acceleration nu alpha beta (0, 1) 0)

/-- Twice the real part of the visible observation recovers alpha. -/
theorem alpha_recovery (nu alpha beta : ℝ) :
    alpha = 2 * ((augmentedReadout nu alpha beta).1 (1, 0) 1).re := by
  change alpha = 2 * (lowObservation alpha beta (1, 0) 1).re
  rw [low_observation_visible]
  simp only [Complex.div_ofNat_re, Complex.ofReal_re]
  ring

/-- The imaginary part of the additional reading is -alpha*beta/4. -/
theorem augmented_readout_im (nu alpha beta : ℝ) :
    (augmentedReadout nu alpha beta).2.im = -alpha * beta / 4 := by
  change (acceleration nu alpha beta (0, 1) 0).im = _
  rw [transverse_acceleration]
  norm_num [Complex.mul_im]

/-- For nonzero alpha, the additional reading recovers beta by explicit division. -/
theorem beta_recovery (nu alpha beta : ℝ) (halpha : alpha ≠ 0) :
    beta = -4 * (augmentedReadout nu alpha beta).2.im / alpha := by
  rw [augmented_readout_im]
  field_simp

/-- For nonzero alpha, both readings alone explicitly reconstruct beta. -/
theorem beta_recovery_from_readout (nu alpha beta : ℝ) (halpha : alpha ≠ 0) :
    beta = -4 * (augmentedReadout nu alpha beta).2.im /
      (2 * ((augmentedReadout nu alpha beta).1 (1, 0) 1).re) := by
  rw [← alpha_recovery]
  exact beta_recovery nu alpha beta halpha

/-- At alpha = 0, every beta gives the same low observation and zero additional reading. -/
theorem augmented_readout_zero (nu beta : ℝ) :
    augmentedReadout nu 0 beta = (lowObservation 0 0, 0) := by
  apply Prod.ext
  · exact lowObservation_independent 0 beta 0
  · change acceleration nu 0 beta (0, 1) 0 = 0
    rw [transverse_acceleration]
    simp

/-- Two augmented readouts agree exactly when alpha agrees and either alpha is zero or beta agrees. -/
theorem augmentedReadout_eq_iff (nu alpha beta alpha' beta' : ℝ) :
    augmentedReadout nu alpha beta = augmentedReadout nu alpha' beta' ↔
      alpha = alpha' ∧ (alpha = 0 ∨ beta = beta') := by
  constructor
  · intro h
    have ha : alpha = alpha' := by
      rw [alpha_recovery nu alpha beta, h, ← alpha_recovery nu alpha' beta']
    refine ⟨ha, ?_⟩
    by_cases hz : alpha = 0
    · exact Or.inl hz
    · right
      subst alpha'
      rw [beta_recovery nu alpha beta hz, h, ← beta_recovery nu alpha beta' hz]
  · rintro ⟨ha, hz | hb⟩
    · subst alpha'
      subst alpha
      rw [augmented_readout_zero, augmented_readout_zero]
    · subst alpha'
      subst beta'
      rfl

#print axioms low_observation_visible
#print axioms augmentedReadout
#print axioms alpha_recovery
#print axioms augmented_readout_im
#print axioms beta_recovery
#print axioms beta_recovery_from_readout
#print axioms augmented_readout_zero
#print axioms augmentedReadout_eq_iff

end D5.S3.FluidDynamics.Fourier.AugmentedReadoutRecovery

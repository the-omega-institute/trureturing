/- GID: D5/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FourierFibers/GoldenScaleCharacterDeckBlindness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Integer golden Fourier characters are blind to one full scale deck
     step even though the golden helix level changes. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import Mathlib

/-!
The repository already keeps the universal-cover data of the golden scale
circle in `GoldenHelixState`.  This module proves the corresponding quotient
fact: an integer Fourier character sees the scale coordinate modulo one period,
while the helix level remembers which deck sheet the observer occupies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ObserverMemory.FourierFibers.GoldenScaleCharacterDeckBlindness

open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix

/-- Integer Fourier character on a normalized real scale coordinate. -/
def normalizedScaleCharacter (mode : ℤ) (coordinate : ℝ) : ℂ :=
  Complex.exp
    ((mode : ℂ) * (coordinate : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I))

/-- Integer Fourier characters are periodic under a unit deck translation. -/
theorem normalized_scale_character_add_one
    (mode : ℤ) (coordinate : ℝ) :
    normalizedScaleCharacter mode (coordinate + 1) =
      normalizedScaleCharacter mode coordinate := by
  unfold normalizedScaleCharacter
  have hExponent :
      (mode : ℂ) * ((coordinate + 1 : ℝ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) =
        (mode : ℂ) * (coordinate : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I) +
          (mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hExponent, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Lifted golden scale divided by one positive golden period. -/
def normalizedHelixScale (state : GoldenHelixState) : ℝ :=
  state.scaleLift / goldenScalePeriod

/-- One golden helix step advances the normalized scale by one. -/
theorem normalized_helix_scale_step (state : GoldenHelixState) :
    normalizedHelixScale (goldenHelixStep state) =
      normalizedHelixScale state + 1 := by
  unfold normalizedHelixScale
  rw [goldenHelixStep_scaleLift]
  have hPeriod : goldenScalePeriod ≠ 0 :=
    ne_of_gt golden_scale_period_pos
  field_simp [hPeriod]
  ring

/-- Fourier readout of the golden scale quotient. -/
def goldenHelixFourierReadout (mode : ℤ) (state : GoldenHelixState) : ℂ :=
  normalizedScaleCharacter mode (normalizedHelixScale state)

/-- A full golden deck step is invisible to every integer Fourier mode. -/
theorem golden_helix_fourier_readout_step
    (mode : ℤ) (state : GoldenHelixState) :
    goldenHelixFourierReadout mode (goldenHelixStep state) =
      goldenHelixFourierReadout mode state := by
  unfold goldenHelixFourierReadout
  rw [normalized_helix_scale_step,
    normalized_scale_character_add_one]

/-- The same deck step is visible in the universal-cover level coordinate. -/
theorem golden_helix_step_changes_level (state : GoldenHelixState) :
    (goldenHelixStep state).level ≠ state.level := by
  rw [goldenHelixStep_level]
  omega

/-- Character-only observation cannot reconstruct the golden helix sheet. -/
theorem golden_helix_fourier_readout_not_injective (mode : ℤ) :
    ¬ Function.Injective (goldenHelixFourierReadout mode) := by
  intro hInjective
  let state : GoldenHelixState :=
    { level := 0
      scaleLift := 0
      orientation := false }
  have hState : goldenHelixStep state = state :=
    hInjective (golden_helix_fourier_readout_step mode state)
  exact golden_helix_step_changes_level state
    (congrArg GoldenHelixState.level hState)

/-- Adding the level coordinate detects every single deck step. -/
theorem level_fourier_joint_readout_detects_step
    (mode : ℤ) (state : GoldenHelixState) :
    ((goldenHelixStep state).level,
        goldenHelixFourierReadout mode (goldenHelixStep state)) ≠
      (state.level, goldenHelixFourierReadout mode state) := by
  intro h
  exact golden_helix_step_changes_level state (congrArg Prod.fst h)

#print axioms normalized_scale_character_add_one
#print axioms normalized_helix_scale_step
#print axioms golden_helix_fourier_readout_step
#print axioms golden_helix_step_changes_level
#print axioms golden_helix_fourier_readout_not_injective
#print axioms level_fourier_joint_readout_detects_step

end D5.S3.ObserverMemory.FourierFibers.GoldenScaleCharacterDeckBlindness

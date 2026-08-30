/- GID: D5/S3/PrimeObserver/ChargeTomography/GoldenC2ChargeTomography
   generality: G
   mirror-B: D5/B/S3/PrimeObserver/ChargeTomography/GoldenC2ChargeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Neutral and quadratic charge channels form invertible two-channel
     tomography, while the neutral channel alone loses the distinction. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for neutral/charge Hadamard tomography, split/inert
     synthesis, and a two-channel golden prime decoder found no exact owner.
   * `GoldenPrimeClassification` supplies the arithmetic interpretation of the
     two sectors; this module owns only their finite linear tomography.
   * Pinned Mathlib supplies elementary product and real-field algebra. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeObserver.ChargeTomography.GoldenC2ChargeTomography

/-- Neutral and quadratic-charge observations of split and inert populations. -/
def analyzeCharge (population : ℝ × ℝ) : ℝ × ℝ :=
  (population.1 + population.2, population.1 - population.2)

/-- Fourier inversion on the two-element charge group. -/
def synthesizePopulation (channels : ℝ × ℝ) : ℝ × ℝ :=
  ((channels.1 + channels.2) / 2, (channels.1 - channels.2) / 2)

/-- Two-element Fourier synthesis exactly recovers the split and inert
populations. -/
theorem synthesize_analyze (population : ℝ × ℝ) :
    synthesizePopulation (analyzeCharge population) = population := by
  rcases population with ⟨split, inert⟩
  ext
  · dsimp [analyzeCharge, synthesizePopulation]
    ring
  · dsimp [analyzeCharge, synthesizePopulation]
    ring

/-- Analysis exactly recovers the neutral and charge channels after synthesis. -/
theorem analyze_synthesize (channels : ℝ × ℝ) :
    analyzeCharge (synthesizePopulation channels) = channels := by
  rcases channels with ⟨neutral, charge⟩
  ext
  · dsimp [analyzeCharge, synthesizePopulation]
    ring
  · dsimp [analyzeCharge, synthesizePopulation]
    ring

/-- The joint neutral-plus-charge observer is faithful. -/
theorem analyze_charge_injective :
    Function.Injective analyzeCharge := by
  intro x y h
  have hDecoded := congrArg synthesizePopulation h
  simpa only [synthesize_analyze] using hDecoded

/-- The joint observer is also surjective. -/
theorem analyze_charge_surjective :
    Function.Surjective analyzeCharge := by
  intro channels
  exact ⟨synthesizePopulation channels, analyze_synthesize channels⟩

/-- The joint observer is a bijective coordinate change. -/
theorem analyze_charge_bijective :
    Function.Bijective analyzeCharge :=
  ⟨analyze_charge_injective, analyze_charge_surjective⟩

/-- The neutral channel forgets how total mass is divided between the two
charge sectors. -/
def neutralChannel (population : ℝ × ℝ) : ℝ :=
  population.1 + population.2

/-- Explicit information-loss witness for the neutral channel. -/
theorem neutral_channel_not_injective :
    ¬ Function.Injective neutralChannel := by
  intro hInjective
  have hSame : neutralChannel (1, 0) = neutralChannel (0, 1) := by
    norm_num [neutralChannel]
  have hPairs : ((1, 0) : ℝ × ℝ) = (0, 1) := hInjective hSame
  have hFirst := congrArg Prod.fst hPairs
  norm_num at hFirst

/-- A zero charge channel means equal split and inert populations. -/
theorem charge_channel_eq_zero_iff (split inert : ℝ) :
    (analyzeCharge (split, inert)).2 = 0 ↔ split = inert := by
  change split - inert = 0 ↔ split = inert
  exact sub_eq_zero

/-- The split population is half the sum of the neutral and charge channels. -/
theorem split_from_channels (split inert : ℝ) :
    split = ((analyzeCharge (split, inert)).1 +
      (analyzeCharge (split, inert)).2) / 2 := by
  change split = (split + inert + (split - inert)) / 2
  ring

/-- The inert population is half the difference of the neutral and charge
channels. -/
theorem inert_from_channels (split inert : ℝ) :
    inert = ((analyzeCharge (split, inert)).1 -
      (analyzeCharge (split, inert)).2) / 2 := by
  change inert = (split + inert - (split - inert)) / 2
  ring

/-- The hypotheses and carrier are inhabited by a nontrivial population. -/
example : analyzeCharge (3, 1) = (4, 2) := by
  norm_num [analyzeCharge]

#print axioms synthesize_analyze
#print axioms analyze_synthesize
#print axioms analyze_charge_injective
#print axioms analyze_charge_surjective
#print axioms neutral_channel_not_injective
#print axioms charge_channel_eq_zero_iff
#print axioms split_from_channels
#print axioms inert_from_channels

end D5.S3.PrimeObserver.ChargeTomography.GoldenC2ChargeTomography

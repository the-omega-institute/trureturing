/- GID: D5/S3/Observer/GoldenCoding/GoldenSamplingDiskAtom
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenSamplingDiskAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden negative-time sampling sends positive-height modes inside the unit disk. -/

import D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom and its three chain atoms are in `residual-open`, have empty
     `coverage_gids`, and have no formalization receipts.
   * Searches of the seven existing `GoldenCoding` modules and the wider D5 tree
     found no theorem combining golden negative-time sampling, unit-disk
     interior, boundary norm, and reciprocal exterior. The closest radial and
     character results are `golden_critical_radius_reflection`,
     `golden_transfer_gain_neg`, and `mellin_character_norm`.
   * `GoldenScaleHelix.goldenScalePeriod` and `golden_scale_period_pos` are the
     canonical period and positivity results and are reused here. Pinned Mathlib
     supplies `Complex.norm_exp`, `Real.exp_lt_one_iff`,
     `Real.rpow_def_of_pos`, and `one_lt_inv₀`; installed non-Mathlib packages
     contain no matching golden-sampling result.
   * The source's inverse-Fourier residue formula depends on a transform
     convention not defined by this atom. This module proves its self-contained
     pointwise consequence for the displayed multiplier `q_j`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenSamplingDiskAtom

open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix

/-- The atomic multiplier obtained by sampling a mode of frequency `frequency`
and height `height` at one negative golden period. -/
def goldenSamplingAtom (frequency height : ℝ) : ℂ :=
  (Real.exp (-goldenScalePeriod * height) : ℂ) *
    Complex.exp (-Complex.I * ((goldenScalePeriod * frequency : ℝ) : ℂ))

/-- The radial exponential is the corresponding real power of the golden ratio. -/
private theorem golden_decay_eq_rpow (height : ℝ) :
    Real.exp (-goldenScalePeriod * height) =
      Real.goldenRatio ^ (-2 * height) := by
  rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
  unfold goldenScalePeriod
  congr 1
  ring

/-- The phase has unit norm, so the atom's norm is exactly its radial decay. -/
theorem golden_sampling_atom_norm (frequency height : ℝ) :
    ‖goldenSamplingAtom frequency height‖ =
      Real.exp (-goldenScalePeriod * height) := by
  simp [goldenSamplingAtom, Complex.norm_exp]

/-- A mode strictly above the observer height becomes an atom inside the unit
disk. At the birth boundary its norm is one, and its reciprocal lies outside
the unit disk. -/
theorem golden_sampling_disk_atom
    (frequency observerHeight modeHeight : ℝ)
    (hAbove : observerHeight < modeHeight) :
    let height := modeHeight - observerHeight
    let q := goldenSamplingAtom frequency height
    q = ((Real.goldenRatio ^ (-2 * height) : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((goldenScalePeriod * frequency : ℝ) : ℂ)) ∧
      ‖q‖ = Real.goldenRatio ^ (-2 * height) ∧
      ‖q‖ < 1 ∧
      ‖goldenSamplingAtom frequency 0‖ = 1 ∧
      1 < ‖q⁻¹‖ := by
  dsimp only
  have hHeight : 0 < modeHeight - observerHeight := sub_pos.mpr hAbove
  have hNorm := golden_sampling_atom_norm frequency (modeHeight - observerHeight)
  have hDecay := golden_decay_eq_rpow (modeHeight - observerHeight)
  have hArgument :
      -goldenScalePeriod * (modeHeight - observerHeight) < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos golden_scale_period_pos) hHeight
  have hInside :
      Real.exp (-goldenScalePeriod * (modeHeight - observerHeight)) < 1 := by
    exact Real.exp_lt_one_iff.mpr hArgument
  refine ⟨?_, hNorm.trans hDecay, hNorm ▸ hInside, ?_, ?_⟩
  · simp only [goldenSamplingAtom]
    rw [hDecay]
  · simpa using golden_sampling_atom_norm frequency 0
  · rw [norm_inv, hNorm]
    exact (one_lt_inv₀ (Real.exp_pos _)).2 hInside

-- Concrete positive-height witness: one golden-sampled mode lies in the open disk.
example : ‖goldenSamplingAtom 0 (1 - 0)‖ < 1 := by
  simpa using (golden_sampling_disk_atom 0 0 1 (by norm_num)).2.2.1

-- Boundary probe: without strict positive height, the open-disk conclusion fails.
example (frequency level : ℝ) :
    ¬ ‖goldenSamplingAtom frequency (level - level)‖ < 1 := by
  rw [sub_self, golden_sampling_atom_norm]
  norm_num

#print axioms golden_sampling_disk_atom

end D5.S3.Observer.GoldenCoding.GoldenSamplingDiskAtom

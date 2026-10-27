/- GID: D5/S3/QuantumChannels/GeneralizedPauliVolumeRatios
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/GeneralizedPauliVolumeRatios
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Generalized Pauli channel regions have three explicit volume ratios. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

noncomputable section

namespace D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios

open MeasureTheory Set
open scoped BigOperators

def boxRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {λ | ∀ i, -1 / ((d : ℝ) - 1) ≤ λ i ∧ λ i ≤ 1}

def cpRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {λ | -1 / ((d : ℝ) - 1) ≤ ∑ i, λ i ∧ ∀ j, ∑ i, λ i ≤ 1 + (d : ℝ) * λ j}

def generatorRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  cpRegion d ∩ {λ | ∀ i, 0 ≤ λ i}

def ebRegion (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  generatorRegion d ∩ {λ | ∑ i, λ i ≤ 1}

def channelVolume (d : ℕ) (s : Set (Fin (d + 1) → ℝ)) : ℝ :=
  (Real.sqrt ((d : ℝ) - 1) / (d : ℝ)) ^ (d + 1) * (volume s).toReal

private def standardRegion (n : ℕ) : Set (Fin n → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1}

private def affineSimplex (d : ℕ) (c : ℝ) : Set (Fin (d + 1) → ℝ) :=
  (fun t i => 1 + c * (t i - ∑ j, t j)) '' standardRegion (d + 1)

private lemma standard_volume (n : ℕ) :
    volume (standardRegion n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  sorry

private lemma affine_simplex_volume (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    volume (affineSimplex d c) =
      ENNReal.ofReal ((d : ℝ) * c ^ (d + 1) / ((d + 1).factorial : ℝ)) := by
  have hs := standard_volume (d + 1)
  sorry

private lemma cp_eq_affine (d : ℕ) (hd : 2 ≤ d) :
    cpRegion d = affineSimplex d ((d : ℝ) / ((d : ℝ) - 1)) := by
  sorry

private lemma generator_eq_union (d : ℕ) (hd : 2 ≤ d) :
    generatorRegion d = standardRegion (d + 1) ∪ affineSimplex d 1 := by
  sorry

private lemma simplex_overlap_null (d : ℕ) (hd : 2 ≤ d) :
    volume (standardRegion (d + 1) ∩ affineSimplex d 1) = 0 := by
  sorry

private lemma generator_volume (d : ℕ) (hd : 2 ≤ d) :
    volume (generatorRegion d) =
      ENNReal.ofReal (((d : ℝ) + 1) / ((d + 1).factorial : ℝ)) := by
  have hs := standard_volume (d + 1)
  have hq := affine_simplex_volume d hd 1 zero_lt_one
  have hu := generator_eq_union d hd
  have hn := simplex_overlap_null d hd
  sorry

private lemma eb_eq_standard (d : ℕ) (hd : 2 ≤ d) :
    ebRegion d = standardRegion (d + 1) := by
  sorry

private lemma box_volume (d : ℕ) (hd : 2 ≤ d) :
    volume (boxRegion d) = ENNReal.ofReal (((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1)) := by
  sorry

private lemma ratios_from_volumes (d : ℕ) (hd : 2 ≤ d)
    (hp : volume (boxRegion d) =
      ENNReal.ofReal (((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1)))
    (hc : volume (cpRegion d) =
      ENNReal.ofReal ((d : ℝ) * ((d : ℝ) / ((d : ℝ) - 1)) ^ (d + 1) /
        ((d + 1).factorial : ℝ)))
    (hg : volume (generatorRegion d) =
      ENNReal.ofReal (((d : ℝ) + 1) / ((d + 1).factorial : ℝ)))
    (he : volume (ebRegion d) = ENNReal.ofReal (1 / ((d + 1).factorial : ℝ))) :
    channelVolume d (cpRegion d) / channelVolume d (boxRegion d) =
        (d : ℝ) / ((d + 1).factorial : ℝ) ∧
    channelVolume d (generatorRegion d) / channelVolume d (cpRegion d) =
        (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) / (d : ℝ)) ^ d ∧
    channelVolume d (ebRegion d) / channelVolume d (generatorRegion d) =
        1 / ((d : ℝ) + 1) := by
  sorry

theorem result : ∀ d : ℕ, 2 ≤ d →
    channelVolume d (cpRegion d) / channelVolume d (boxRegion d) =
        (d : ℝ) / ((d + 1).factorial : ℝ) ∧
    channelVolume d (generatorRegion d) / channelVolume d (cpRegion d) =
        (((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 2) * (((d : ℝ) - 1) / (d : ℝ)) ^ d ∧
    channelVolume d (ebRegion d) / channelVolume d (generatorRegion d) =
        1 / ((d : ℝ) + 1) := by
  intro d hd
  apply ratios_from_volumes d hd (box_volume d hd)
  · rw [cp_eq_affine d hd]
    exact affine_simplex_volume d hd _ (div_pos (by positivity) (by norm_cast; omega))
  · exact generator_volume d hd
  · rw [eb_eq_standard d hd]
    exact standard_volume (d + 1)

end D5.S3.QuantumChannels.GeneralizedPauliVolumeRatios

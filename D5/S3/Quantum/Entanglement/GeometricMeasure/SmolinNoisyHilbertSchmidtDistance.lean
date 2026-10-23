/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/SmolinNoisyHilbertSchmidtDistance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact Hilbert–Schmidt distances of noisy Smolin states for four partitions. -/

import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.Convex.Hull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma sigma_properties)
open D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence (IsSeparable)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance

abbrev Q := Fin 2 × Fin 2 × Fin 2 × Fin 2

private def four (j : Fin 4) : Matrix Q Q ℂ :=
  sigma j ⊗ₖ (sigma j ⊗ₖ (sigma j ⊗ₖ sigma j))

private def S : Matrix Q Q ℂ := four 1 + four 2 + four 3

def smolin : Matrix Q Q ℂ := (1 / 16 : ℂ) • (1 + S)

def noisy (p : ℝ) : Matrix Q Q ℂ :=
  p • smolin + (1 - p) • ((1 / 16 : ℂ) • 1)

def SepOneThree : Set (Matrix Q Q ℂ) := {ρ | IsSeparable ρ}

def SepOneOneTwo : Set (Matrix Q Q ℂ) :=
  convexHull ℝ {ρ | ∃ (a b : Matrix (Fin 2) (Fin 2) ℂ)
    (c : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
    IsDensity a ∧ IsDensity b ∧ IsDensity c ∧ ρ = a ⊗ₖ (b ⊗ₖ c)}

def SepFull : Set (Matrix Q Q ℂ) :=
  convexHull ℝ {ρ | ∃ (a b c d : Matrix (Fin 2) (Fin 2) ℂ),
    IsDensity a ∧ IsDensity b ∧ IsDensity c ∧ IsDensity d ∧
      ρ = a ⊗ₖ (b ⊗ₖ (c ⊗ₖ d))}

def SepTwoTwo : Set (Matrix Q Q ℂ) :=
  {ρ | IsSeparable (ρ.submatrix (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2))
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2 × Fin 2)))}

def hsDist (X Y : Matrix Q Q ℂ) : ℝ :=
  Real.sqrt (Matrix.trace ((X - Y)ᴴ * (X - Y))).re

def f (p : ℝ) : ℝ :=
  if p ≤ 1 / 3 then 0 else Real.sqrt 3 / 4 * (p - 1 / 3)

def claim : Prop := ∀ p ∈ Set.Icc (0 : ℝ) 1,
  IsLeast {d | ∃ σ ∈ SepOneThree, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepOneOneTwo, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepFull, d = hsDist (noisy p) σ} (f p) ∧
  IsLeast {d | ∃ σ ∈ SepTwoTwo, d = hsDist (noisy p) σ} 0

private theorem hsDist_nonneg (X Y : Matrix Q Q ℂ) : 0 ≤ hsDist X Y := by
  sorry

private theorem hsDist_self (X : Matrix Q Q ℂ) : hsDist X X = 0 := by
  sorry

private theorem full_subset_oneOneTwo : SepFull ⊆ SepOneOneTwo := by
  sorry

private theorem oneOneTwo_subset_oneThree : SepOneOneTwo ⊆ SepOneThree := by
  sorry

private theorem full_subset_twoTwo : SepFull ⊆ SepTwoTwo := by
  sorry

private theorem boundary_full : noisy (1 / 3) ∈ SepFull := by
  sorry

private theorem low_full (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1 / 3) :
    noisy p ∈ SepFull := by
  sorry

private theorem trace_S : Matrix.trace S = 0 := by
  sorry

private theorem trace_S_sq : Matrix.trace (S * S) = 48 := by
  sorry

private theorem trace_S_noisy (p : ℝ) : (Matrix.trace (S * noisy p)).re = 3 * p := by
  sorry

private theorem witness_product (a : Matrix (Fin 2) (Fin 2) ℂ)
    (b : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ)
    (ha : IsDensity a) (hb : IsDensity b) :
    (Matrix.trace (S * (a ⊗ₖ b))).re ≤ 1 := by
  sorry

private theorem witness_separable (σ : Matrix Q Q ℂ) (hσ : σ ∈ SepOneThree) :
    (Matrix.trace (S * σ)).re ≤ 1 := by
  sorry

private theorem witness_cauchy (X : Matrix Q Q ℂ) :
    (Matrix.trace (S * X)).re ≤ Real.sqrt 48 * hsDist X 0 := by
  sorry

private theorem distance_lower (p : ℝ) (σ : Matrix Q Q ℂ)
    (hσ : σ ∈ SepOneThree) : f p ≤ hsDist (noisy p) σ := by
  sorry

private theorem boundary_distance (p : ℝ) :
    hsDist (noisy p) (noisy (1 / 3)) = Real.sqrt 3 / 4 * |p - 1 / 3| := by
  sorry

private theorem noisy_twoTwo (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    noisy p ∈ SepTwoTwo := by
  sorry

private theorem least_refinement (K : Set (Matrix Q Q ℂ))
    (hFK : SepFull ⊆ K) (hK : K ⊆ SepOneThree)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    IsLeast {d | ∃ σ ∈ K, d = hsDist (noisy p) σ} (f p) := by
  constructor
  · by_cases h : p ≤ 1 / 3
    · refine ⟨noisy p, hFK (low_full p hp.1 h), ?_⟩
      rw [f, if_pos h, hsDist_self]
    · refine ⟨noisy (1 / 3), hFK boundary_full, ?_⟩
      rw [f, if_neg h, boundary_distance, abs_of_pos (by linarith)]
  · rintro d ⟨σ, hσ, rfl⟩
    exact distance_lower p σ (hK hσ)

theorem result : claim := by
  intro p hp
  have hF : SepFull ⊆ SepOneThree :=
    full_subset_oneOneTwo.trans oneOneTwo_subset_oneThree
  refine ⟨least_refinement SepOneThree hF (fun _ h => h) p hp,
    least_refinement SepOneOneTwo full_subset_oneOneTwo oneOneTwo_subset_oneThree p hp,
    least_refinement SepFull (fun _ h => h) hF p hp, ?_⟩
  constructor
  · exact ⟨noisy p, noisy_twoTwo p hp, (hsDist_self _).symm⟩
  · rintro d ⟨σ, _, rfl⟩
    exact hsDist_nonneg _ _

end D5.S3.Quantum.Entanglement.GeometricMeasure.SmolinNoisyHilbertSchmidtDistance

/- GID: D5/S3/SpectralTopology/HalfFluxHofstadterMassGap
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/HalfFluxHofstadterMassGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The nonzero mass Hofstadter bands have a uniform gap at the Fermi energy. -/

import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import D5.S3.SpectralTopology.PointGapExactInertia
import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

noncomputable section

open Matrix Complex

namespace D5.S3.SpectralTopology.HalfFluxHofstadterMassGap

/-- The source Bloch Hamiltonian, including its overall minus sign, with `d = 2 + m`. -/
def bloch (k₁ k₂ m : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  let d : ℂ := ((2 + m : ℝ) : ℂ)
  -!![d, 1 - I * exp (2 * I * k₁), 1 - I * exp (2 * I * k₂), 0;
      1 + I * exp (-2 * I * k₁), 0, 0, -I + exp (2 * I * k₂);
      1 + I * exp (-2 * I * k₂), 0, 0, 1 + I * exp (2 * I * k₁);
      0, I + exp (-2 * I * k₂), 1 - I * exp (-2 * I * k₁), -d]

theorem bloch_isHermitian (k₁ k₂ m : ℝ) : (bloch k₁ k₂ m).IsHermitian := by
  sorry

/-- `band k₁ k₂ m j` is the source's `λ_{j+1}`, in increasing order with multiplicity. -/
def band (k₁ k₂ m : ℝ) (j : Fin 4) : ℝ :=
  (bloch_isHermitian k₁ k₂ m).eigenvalues₀ j.rev

/-- The source's Fermi energy `μ = λ₃(π/4, π/4; 0)`. -/
def fermiEnergy : ℝ := band (Real.pi / 4) (Real.pi / 4) 0 2

def claim : Prop :=
  band (Real.pi / 4) (Real.pi / 4) 0 3 = fermiEnergy ∧
    ∀ m : ℝ, -2 ≤ m → m ≤ 2 → m ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ k₁ k₂ : ℝ,
        fermiEnergy + δ ≤ band k₁ k₂ m 3 ∧
          band k₁ k₂ m 2 ≤ fermiEnergy - δ

private theorem fermi_bands :
    band (Real.pi / 4) (Real.pi / 4) 0 2 = 2 ∧
      band (Real.pi / 4) (Real.pi / 4) 0 3 = 2 := by
  sorry

private theorem band_signs (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (hm : m ≠ 0) :
    band k₁ k₂ m 2 < 2 ∧ 2 < band k₁ k₂ m 3 := by
  sorry

private theorem band_distance (k₁ k₂ m : ℝ)
    (hm₁ : -2 ≤ m) (hm₂ : m ≤ 2) (j : Fin 4) :
    m ^ 2 / 500 ≤ |band k₁ k₂ m j - 2| := by
  sorry

theorem result : claim := by
  have hf : fermiEnergy = 2 := fermi_bands.1
  refine ⟨fermi_bands.2.trans hf.symm, ?_⟩
  intro m hm₁ hm₂ hm
  refine ⟨m ^ 2 / 500, div_pos (sq_pos_of_ne_zero hm) (by norm_num), ?_⟩
  intro k₁ k₂
  obtain ⟨hlo, hhi⟩ := band_signs k₁ k₂ m hm₁ hm₂ hm
  have h₃ := band_distance k₁ k₂ m hm₁ hm₂ 3
  have h₂ := band_distance k₁ k₂ m hm₁ hm₂ 2
  rw [abs_of_pos (sub_pos.mpr hhi)] at h₃
  rw [abs_of_neg (sub_neg.mpr hlo)] at h₂
  rw [hf]
  constructor <;> linarith

end D5.S3.SpectralTopology.HalfFluxHofstadterMassGap

/- GID: D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=none
   digest: The Appendix A.1 tuple of arXiv:2512.17706 is feasible on the full interval. -/

import D5.S3.Constants.Radicals.SqrtThreeThreshold
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness

noncomputable section

open Matrix
open scoped ComplexOrder

def X₁ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]
def X₂ : Matrix (Fin 2) (Fin 2) ℝ := !![-2, 0; 0, 1]
def X₃ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; Real.sin θ, -Real.cos θ]
def γ : ℝ := 4 / (1 + Real.sqrt 3)
def β (θ : ℝ) : ℝ :=
  Real.sqrt 3 * Real.sqrt ((6 - 4 * Real.sqrt 3) * Real.sin θ +
    6 * Real.cos θ - 4 * Real.sqrt 3 + 13)
def C₁ : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / Real.sqrt 3 - 1 / 2 : ℝ) • !![1, 1; 1, 1]
def C₂ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 12 : ℝ) •
    !![3 * Real.cos θ + 8 * Real.sqrt 3 - 9 - β θ, 3 * Real.sin θ - 2 * Real.sqrt 3 + 3;
       3 * Real.sin θ - 2 * Real.sqrt 3 + 3, -3 * Real.cos θ + 8 * Real.sqrt 3 - 3 - β θ]
def C₃ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -C₁ - C₂ θ + (1 / 2 : ℝ) • X₃ θ + (γ / 2) • 1
def C₄ : Matrix (Fin 2) (Fin 2) ℝ :=
  -C₁ + (1 / 3 : ℝ) • X₁ + (1 / 3 : ℝ) • X₂ + (γ / 3) • 1
def C₅ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -C₂ θ - (1 / 3 : ℝ) • X₁ + (γ / 3) • 1
def C₆ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  C₁ + C₂ θ - (1 / 3 : ℝ) • X₂ - (1 / 2 : ℝ) • X₃ θ - (γ / 6) • 1
def C (i : Fin 6) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![C₁, C₂ θ, C₃ θ, C₄, C₅ θ, C₆ θ] i

def claim : Prop := ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
  (∀ i : Fin 6, ((C i θ).map (↑) : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef) ∧
  C 0 θ - 2 • C 1 θ + C 2 θ + C 3 θ - 2 • C 4 θ + C 5 θ = X₁ ∧
  C 0 θ + C 1 θ - 2 • C 2 θ + C 3 θ + C 4 θ - 2 • C 5 θ = X₂ ∧
  C 0 θ + C 1 θ + C 2 θ - C 3 θ - C 4 θ - C 5 θ = X₃ θ ∧
  ∑ i, C i θ = γ • 1

private theorem posSemidef_of_trace_det (u v w : ℝ)
    (ht : 0 < u + w) (hd : 0 ≤ u * w - v ^ 2) :
    ((!![u, v; v, w]).map (↑) : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
  have hu : 0 ≤ u := by
    by_contra h
    have hn : u < 0 := lt_of_not_ge h
    have hw : 0 < w := by linarith
    have hp := mul_neg_of_neg_of_pos hn hw
    nlinarith [sq_nonneg v]
  have hq (x y : ℝ) : 0 ≤ u * x ^ 2 + 2 * v * x * y + w * y ^ 2 := by
    rcases hu.eq_or_lt with hz | hp
    · have hv : v = 0 := by nlinarith [sq_nonneg v]
      have hw : 0 ≤ w := by linarith
      simp only [← hz, hv, zero_mul, mul_zero, zero_add]
      exact mul_nonneg hw (sq_nonneg y)
    · apply nonneg_of_mul_nonneg_right (a := u) ?_ hp
      nlinarith only [sq_nonneg (u * x + v * y), mul_nonneg hd (sq_nonneg y)]
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose]
  · intro z
    rw [Complex.nonneg_iff]
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im]
    constructor
    · nlinarith only [hq (z 0).re (z 1).re, hq (z 0).im (z 1).im]
    · ring

private theorem affine_eqs (θ : ℝ) :
    C 0 θ - 2 • C 1 θ + C 2 θ + C 3 θ - 2 • C 4 θ + C 5 θ = X₁ ∧
    C 0 θ + C 1 θ - 2 • C 2 θ + C 3 θ + C 4 θ - 2 • C 5 θ = X₂ ∧
    C 0 θ + C 1 θ + C 2 θ - C 3 θ - C 4 θ - C 5 θ = X₃ θ ∧
    ∑ i, C i θ = γ • 1 := by
  simp only [two_smul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [C, C₃, C₄, C₅, C₆, C₁, C₂, X₁, X₂, X₃, Fin.sum_univ_six, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.neg_apply, smul_eq_mul, Matrix.one_apply] <;> ring

end

end D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness

/- GID: D5/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/FreeSpectrahedronFeasibilityWitness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
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
def C₄ (_θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -C₁ + (1 / 3 : ℝ) • X₁ + (1 / 3 : ℝ) • X₂ + (γ / 3) • 1
def C₅ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -C₂ θ - (1 / 3 : ℝ) • X₁ + (γ / 3) • 1
def C₆ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  C₁ + C₂ θ - (1 / 3 : ℝ) • X₂ - (1 / 2 : ℝ) • X₃ θ - (γ / 6) • 1
def C (i : Fin 6) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![C₁, C₂ θ, C₃ θ, C₄ θ, C₅ θ, C₆ θ] i

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
    simp [C, C₃, C₄, C₅, C₆, C₁, C₂, X₁, X₂, X₃, Fin.sum_univ_six,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

private theorem scalar_bounds (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    0 < β θ ∧
    (β θ) ^ 2 = 9 * (Real.cos θ + 1) ^ 2 +
      (3 * Real.sin θ - 2 * Real.sqrt 3 + 3) ^ 2 ∧
    0 < 8 * Real.sqrt 3 - 6 - β θ ∧
    0 ≤ (36 * Real.cos θ + 228 - 96 * Real.sqrt 3) -
      (16 * Real.sqrt 3 - 12) * β θ := by
  let r := Real.sqrt 3
  let s := Real.sin θ
  let c := Real.cos θ
  let b := β θ
  let d := (6 - 4 * r) * s + 6 * c - 4 * r + 13
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 3
  have hrlo : 3 / 2 < r := by
    have h := D5.S3.Constants.Radicals.SqrtThreeThreshold.three_lt_two_mul_sqrt_three
    dsimp [r]
    linarith
  have hrhi : r < 7 / 4 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hs0 : 0 ≤ s := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs1 : s ≤ 1 := Real.sin_le_one θ
  have hc1 : c ≤ 1 := Real.cos_le_one θ
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hd0 : 0 < d := by
    dsimp [d]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * r - 6) (sub_nonneg.mpr hs1)]
  have hb0 : 0 < b := mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.sqrt_pos.mpr hd0)
  have hb2 : b ^ 2 = 3 * d := by
    dsimp [b, β, d, r, s, c]
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hd0.le]
  have hupper : 3 * d ≤ 57 - 12 * r := by
    dsimp [d]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * r - 6) hs0]
  have htrace : 0 < 8 * r - 6 - b := by
    have hsq : b ^ 2 < (8 * r - 6) ^ 2 := by nlinarith
    nlinarith
  have hrank : b ^ 2 = 9 * (c + 1) ^ 2 + (3 * s - 2 * r + 3) ^ 2 := by
    dsimp [d] at hb2
    linear_combination hb2 - 4 * hr2 - 9 * hsc
  let A := 36 * c + 228 - 96 * r
  let B := 16 * r - 12
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hk : 0 < 219 - 124 * r := by
    have h : r < 219 / 124 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith
  have hid : A ^ 2 - B ^ 2 * b ^ 2 = 144 * (1 - s) * (219 + 9 * s - 124 * r) := by
    dsimp [A, B, d] at *
    linear_combination (-256 * r ^ 2 + 384 * r - 144) * hb2 +
      (-4608 * c + 3072 * r * s + 3072 * r - 9216 * s - 5376) * hr2 + 1296 * hsc
  have hsq : 0 ≤ A ^ 2 - B ^ 2 * b ^ 2 := by
    rw [hid]
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs1)) (by linarith)
  have hdet : 0 ≤ A - B * b := by
    have hBb : 0 ≤ B * b := mul_nonneg hB.le hb0.le
    exact sub_nonneg.mpr ((sq_le_sq₀ hBb hA.le).mp (by nlinarith only [hsq]))
  exact ⟨hb0, hrank, htrace, hdet⟩

private theorem matrix_forms (θ : ℝ) :
    C₁ = !![Real.sqrt 3 / 3 - 1 / 2, Real.sqrt 3 / 3 - 1 / 2;
             Real.sqrt 3 / 3 - 1 / 2, Real.sqrt 3 / 3 - 1 / 2] ∧
    C₂ θ = !![(3 * Real.cos θ + 8 * Real.sqrt 3 - 9 - β θ) / 12,
                (3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12;
              (3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12,
                (-3 * Real.cos θ + 8 * Real.sqrt 3 - 3 - β θ) / 12] ∧
    C₃ θ = !![(β θ + 3 * (Real.cos θ + 1)) / 12,
                (3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12;
              (3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12,
                (β θ - 3 * (Real.cos θ + 1)) / 12] ∧
    C₄ θ = !![Real.sqrt 3 / 3 - 1 / 2, -(Real.sqrt 3 / 3 - 1 / 2);
               -(Real.sqrt 3 / 3 - 1 / 2), Real.sqrt 3 / 3 - 1 / 2] ∧
    C₅ θ = !![(β θ - 3 * (Real.cos θ + 1)) / 12,
                -(3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12;
              -(3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12,
                (β θ + 3 * (Real.cos θ + 1)) / 12] ∧
    C₆ θ = !![(-3 * Real.cos θ + 8 * Real.sqrt 3 - 3 - β θ) / 12,
                -(3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12;
              -(3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12,
                (3 * Real.cos θ + 8 * Real.sqrt 3 - 9 - β θ) / 12] := by
  have hr2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hi : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := (Real.sqrt_div_self').symm
  have hg : γ = 2 * Real.sqrt 3 - 2 := by
    unfold γ
    apply (div_eq_iff (by positivity : 1 + Real.sqrt 3 ≠ 0)).mpr
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [C₁, C₂, C₃, C₄, C₅, C₆, X₁, X₂, X₃, hi, hg, Matrix.smul_apply,
      smul_eq_mul] <;> ring

/-- The Appendix A.1 tuple satisfies SDP (37) for every angle in the closed interval. -/
theorem result : claim := by
  intro θ hθ
  refine ⟨?_, affine_eqs θ⟩
  obtain ⟨hC₁, hC₂, hC₃, hC₄, hC₅, hC₆⟩ := matrix_forms θ
  obtain ⟨hb0, hrank, htrace, hdet⟩ := scalar_bounds θ hθ
  have hr2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ha : 0 < Real.sqrt 3 / 3 - 1 / 2 := by
    linarith [D5.S3.Constants.Radicals.SqrtThreeThreshold.three_lt_two_mul_sqrt_three]
  have hd₂ : 0 ≤
      ((3 * Real.cos θ + 8 * Real.sqrt 3 - 9 - β θ) / 12) *
        ((-3 * Real.cos θ + 8 * Real.sqrt 3 - 3 - β θ) / 12) -
      ((3 * Real.sin θ - 2 * Real.sqrt 3 + 3) / 12) ^ 2 := by
    nlinarith only [hr2, hrank, hdet]
  intro i
  fin_cases i <;> dsimp only [C]
  · rw [hC₁]
    apply posSemidef_of_trace_det
    · linarith
    · nlinarith
  · rw [hC₂]
    apply posSemidef_of_trace_det
    · linarith
    · exact hd₂
  · rw [hC₃]
    apply posSemidef_of_trace_det
    · linarith
    · nlinarith only [hrank]
  · rw [hC₄]
    apply posSemidef_of_trace_det
    · linarith
    · nlinarith
  · rw [hC₅]
    apply posSemidef_of_trace_det
    · linarith
    · nlinarith only [hrank]
  · rw [hC₆]
    apply posSemidef_of_trace_det
    · linarith
    · nlinarith only [hd₂]

#print axioms result

end

end D5.S3.Quantum.Measurement.FreeSpectrahedronFeasibilityWitness

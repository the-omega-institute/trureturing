/- GID: D5/S3/Quantum/Thermal/PositiveOneModeWilliamson
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/PositiveOneModeWilliamson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive one-mode quadratic energy has an explicit positive symplectic normal form. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Thermal.PositiveOneModeWilliamson

/-- The physical `q,p` Poisson convention, opposite to Mathlib's `Matrix.J` sign. -/
def physicalJ2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- A positive one-mode energy admits a symplectic change of coordinates with
positive oscillator frequency. This is the explicit two-dimensional case of
the normal-mode construction. -/
theorem positive_one_mode_williamson (a b c : ℝ)
    (hS : (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    ∃ (ω : ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ),
      0 < ω ∧ M.transpose * physicalJ2 * M = physicalJ2 ∧
      M.transpose * !![a, b; b, c] * M = ω • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  let e0 : Fin 2 → ℝ := Pi.single 0 1
  have he0 : e0 ≠ 0 := by
    intro h
    have hx := congrFun h (0 : Fin 2)
    norm_num [e0] at hx
  have ha : 0 < a := by
    have h := hS.re_dotProduct_pos he0
    simpa [e0, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hδ : 0 < a * c - b ^ 2 := by
    have h := hS.det_pos
    simpa [Matrix.det_fin_two, pow_two] using h
  let ω := Real.sqrt (a * c - b ^ 2)
  have hω : 0 < ω := Real.sqrt_pos.2 hδ
  have hω2 : ω ^ 2 = a * c - b ^ 2 := Real.sq_sqrt hδ.le
  let u := Real.sqrt (ω / a)
  have hu : 0 < u := Real.sqrt_pos.2 (div_pos hω ha)
  have hu2 : u ^ 2 = ω / a := Real.sq_sqrt (div_pos hω ha).le
  have hau2 : a * u ^ 2 = ω := by rw [hu2]; field_simp
  have hau2ω : a * u ^ 2 * ω = ω ^ 2 := by rw [hau2]; ring
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![u, -b / (a * u); 0, 1 / u]
  refine ⟨ω, M, hω, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, physicalJ2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply, hu.ne'] <;>
      field_simp <;> nlinarith [hau2]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply, hu.ne'] <;>
      field_simp <;> nlinarith [hau2, hau2ω, hω2]

#print axioms positive_one_mode_williamson

end D5.S3.Quantum.Thermal.PositiveOneModeWilliamson

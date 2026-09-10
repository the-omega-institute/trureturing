/- GID: D5/S3/FluidDynamics/Cone/ConePositivity
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Cone/ConePositivity
   mirror-E: none
   anchors: []
   utility: none
   digest: The Navier--Stokes cone condition is equivalent to positive definiteness of an explicit symmetric two-by-two real matrix. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace D5.S3.FluidDynamics.Cone

/-! Port of `true_cone_iff` and its algebraic prerequisites from the upstream
repository `openai/NavierStokesAndEuler`, commit
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, file
`NavierStokes/ConeAlgebra.lean`, licensed under Apache-2.0.
This is a port rather than an import because upstream pins Lean v4.34.0-rc2,
this repository pins v4.33.0, and a repository-wide toolchain change for one
research line is not acceptable.
The matrix positivity bridge and its composition are proved locally. -/

noncomputable def coneBound (P J : ℝ) : ℝ :=
  P + J ^ 2 / 4 - |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

noncomputable def rootTerm (P J : ℝ) : ℝ :=
  |J| * Real.sqrt ((P - 2) / 2 + J ^ 2 / 16)

theorem rootTerm_nonneg (P J : ℝ) : 0 ≤ rootTerm P J := by
  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem rootTerm_sq {P J : ℝ} (hP : 2 < P) :
    rootTerm P J ^ 2 = J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) := by
  have hrad : 0 ≤ (P - 2) / 2 + J ^ 2 / 16 := by nlinarith [sq_nonneg J]
  unfold rootTerm
  rw [mul_pow, sq_abs, Real.sq_sqrt hrad]

theorem rootTerm_ge_quarter {P J : ℝ} (hP : 2 < P) : J ^ 2 / 4 ≤ rootTerm P J := by
  have hs := rootTerm_sq (J := J) hP
  have hn := rootTerm_nonneg P J
  nlinarith [sq_nonneg (J ^ 2 - 4 * rootTerm P J)]

theorem coneBound_le_parameter {P J : ℝ} (hP : 2 < P) : coneBound P J ≤ P := by
  change P + J ^ 2 / 4 - rootTerm P J ≤ P
  linarith [rootTerm_ge_quarter (J := J) hP]

theorem coneBound_gt_two {P J : ℝ} (hP : 2 < P) : 2 < coneBound P J := by
  change 2 < P + J ^ 2 / 4 - rootTerm P J
  have hs := rootTerm_sq (J := J) hP
  have hn := rootTerm_nonneg P J
  nlinarith [sq_nonneg (J ^ 2 - 4 * rootTerm P J)]

theorem relaxed_cone_of_le_two {P J v : ℝ} (hP : 2 < P) (hv : v ≤ 2) :
    v < coneBound P J := by
  exact lt_of_le_of_lt hv (coneBound_gt_two hP)

theorem boundary_polynomial (P J v : ℝ) :
    2 * (P - v) ^ 2 - (v - 2) * J ^ 2 =
      2 * v ^ 2 - (4 * P + J ^ 2) * v + 2 * P ^ 2 + 2 * J ^ 2 := by
  ring

theorem square_difference (P J v : ℝ) :
    (P + J ^ 2 / 4 - v) ^ 2 - J ^ 2 * ((P - 2) / 2 + J ^ 2 / 16) =
      (P - v) ^ 2 - (v - 2) * J ^ 2 / 2 := by
  ring

theorem true_cone_iff {P J v : ℝ} (hv : 2 < v) :
    (2 < P ∧ v < coneBound P J) ↔
      (v < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2) := by
  constructor
  · rintro ⟨hP, hcone⟩
    have hvP : v < P := lt_of_lt_of_le hcone (coneBound_le_parameter hP)
    refine ⟨hvP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by
      change v < P + J ^ 2 / 4 - rootTerm P J at hcone
      linarith
    have hdiff := mul_pos (sub_pos.mpr hlt)
      (show 0 < P + J ^ 2 / 4 - v + rootTerm P J by linarith)
    nlinarith
  · rintro ⟨hvP, hquad⟩
    have hP : 2 < P := lt_trans hv hvP
    refine ⟨hP, ?_⟩
    have hsq := rootTerm_sq (J := J) hP
    have hr := rootTerm_nonneg P J
    have hid := square_difference P J v
    have hpos : 0 < P + J ^ 2 / 4 - v := by nlinarith [sq_nonneg J]
    have hlt : rootTerm P J < P + J ^ 2 / 4 - v := by nlinarith
    change v < P + J ^ 2 / 4 - rootTerm P J
    linarith

def coneMatrix (P J v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (P - v) * (v - 2), J * (v - 2); J * (v - 2), P - v]

theorem coneMatrix_posDef_iff {P J v : ℝ} (hv : 2 < v) :
    (coneMatrix P J v).PosDef ↔
      (v < P ∧ (v - 2) * J ^ 2 < 2 * (P - v) ^ 2) := by
  classical
  let a := P - v
  let c := v - 2
  have hc : 0 < c := sub_pos.mpr hv
  have hdet_eq : (coneMatrix P J v).det = c * (2 * a ^ 2 - J ^ 2 * c) := by
    simp [coneMatrix, Matrix.det_fin_two, a, c]
    ring
  constructor
  · intro hM
    have he : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ≠ 0 := by
      intro hz
      have hz0 := congrFun hz 0
      norm_num at hz0
    have h00 : 0 < 2 * a * c := by
      simpa [coneMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, a, c] using
        hM.dotProduct_mulVec_pos he
    have ha : 0 < a := by nlinarith
    have hdet := hM.det_pos
    rw [hdet_eq] at hdet
    have hquad : 0 < 2 * a ^ 2 - J ^ 2 * c := (mul_pos_iff_of_pos_left hc).mp hdet
    exact ⟨sub_pos.mp ha, by dsimp [a, c] at hquad; nlinarith⟩
  · rintro ⟨hvp, hi⟩
    have ha : 0 < a := sub_pos.mpr hvp
    have h00 : 0 < 2 * a * c := mul_pos (mul_pos (by norm_num) ha) hc
    have hdet : 0 < 2 * a ^ 2 * c - (J * c) ^ 2 := by
      have hquad : 0 < 2 * a ^ 2 - J ^ 2 * c := by dsimp [a, c]; nlinarith
      nlinarith [mul_pos hc hquad]
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [coneMatrix, Matrix.conjTranspose_apply]
    · intro x hx
      have hcomplete :
          x 0 * (2 * a * c * x 0 + J * c * x 1) +
            x 1 * (J * c * x 0 + a * x 1) =
          (2 * a * c) * (x 0 + J * c * x 1 / (2 * a * c)) ^ 2 +
            ((2 * a ^ 2 * c - (J * c) ^ 2) / (2 * a * c)) * x 1 ^ 2 := by
        field_simp
        ring
      have hfirst : 0 ≤ (2 * a * c) * (x 0 + J * c * x 1 / (2 * a * c)) ^ 2 :=
        mul_nonneg h00.le (sq_nonneg _)
      have hform : 0 < x 0 * (2 * a * c * x 0 + J * c * x 1) +
          x 1 * (J * c * x 0 + a * x 1) := by
        by_cases hx1 : x 1 = 0
        · have hx0 : x 0 ≠ 0 := by
            intro hz
            apply hx
            funext i
            fin_cases i
            · exact hz
            · exact hx1
          simpa [hx1, pow_two, mul_assoc, mul_left_comm, mul_comm] using
            mul_pos h00 (sq_pos_of_ne_zero hx0)
        · rw [hcomplete]
          exact add_pos_of_nonneg_of_pos hfirst
            (mul_pos (div_pos hdet h00) (sq_pos_of_ne_zero hx1))
      simpa [coneMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, a, c] using hform

theorem cone_condition_iff_posDef {P J v : ℝ} (hv : 2 < v) :
    (2 < P ∧ v < coneBound P J) ↔ (coneMatrix P J v).PosDef := by
  rw [true_cone_iff hv, coneMatrix_posDef_iff hv]

#print axioms coneBound
#print axioms rootTerm
#print axioms rootTerm_nonneg
#print axioms rootTerm_sq
#print axioms rootTerm_ge_quarter
#print axioms coneBound_le_parameter
#print axioms coneBound_gt_two
#print axioms relaxed_cone_of_le_two
#print axioms boundary_polynomial
#print axioms square_difference
#print axioms true_cone_iff
#print axioms coneMatrix
#print axioms coneMatrix_posDef_iff
#print axioms cone_condition_iff_posDef

end D5.S3.FluidDynamics.Cone

/- GID: D5/S3/Quantum/Matrix/NormalModulusTriangleConstant
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/NormalModulusTriangleConstant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.claim; result=D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.result; claim=D5/S3/Quantum/Matrix/NormalModulusTriangleConstant.claim
   digest: A rational 2×2 normal-matrix witness refutes every constant below one quarter. -/

/- Source: Bourin–Lee, arXiv:2602.19607, §4, Corollary 4.2.
   admission_basis: open-problem-resolution (#15672; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Definitions:
     IsModulus: proof_shape definition; consumers=claim, modulus_A, modulus_M, modulus_PS, result
     IsNormalMatrix: proof_shape definition; consumers=claim, normal_A, normal_B
     claim: proof_shape definition; consumer=result
     A: proof_shape definition; consumers=D, A_eq_conjTranspose_mul_self, modulus_A, modulus_PS, normal_A, d_quad, d_upper, result
     M: proof_shape definition; consumers=B, D, M_eq_smul_conjTranspose_mul_self, modulus_M, modulus_PS, normal_B, d_quad, d_upper, result
     B: proof_shape definition; consumers=modulus_M, modulus_PS, normal_B, result
     PS: proof_shape definition; consumers=modulus_PS, ps_quad, result
     D: proof_shape definition; consumers=d_pos, d_quad, d_upper, conjugation_quad, result
     x: proof_shape definition; consumers=d_quad, ps_quad, conjugation_quad, result
   Per-declaration proof_shape and live consumers:
     A_eq_conjTranspose_mul_self: bind-only; consumer=modulus_A
     M_eq_smul_conjTranspose_mul_self: bind-only; consumer=modulus_M
     modulus_A: bind-only; consumers=d_pos, result
     modulus_M: bind-only; consumers=d_pos, result
     modulus_PS: bind-only; consumer=result
     normal_A: bind-only; consumer=result
     normal_B: bind-only; consumer=result
     d_pos: bind-only; consumer=result
     d_quad: bind-only; consumer=result
     ps_quad: bind-only; consumer=result
     d_upper: bind-only; consumer=result
     conjugation_quad: bind-only; consumer=result
     result: bind-only; designated refutation conclusion
   The explicit rational matrices give a quadratic-form obstruction at x=(1,2).
   Unitary conjugation preserves the norm, while D and (8/5)I-D bound the
   conjugated quadratic form between zero and eight. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Quantum.Matrix.NormalModulusTriangleConstant

/-- `P` is the modulus `|X| = (X^* X)^{1/2}`: positive semidefinite with `P * P = Xᴴ * X`. -/
def IsModulus (X P : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  P.PosSemidef ∧ P * P = Xᴴ * X

/-- `X` is normal. -/
def IsNormalMatrix (X : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Xᴴ * X = X * Xᴴ

def claim : Prop :=
  ∃ c : ℝ, c < 1 / 4 ∧
    ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, IsNormalMatrix A → IsNormalMatrix B →
      ∀ PA PB PS : Matrix (Fin 2) (Fin 2) ℂ,
        IsModulus A PA → IsModulus B PB → IsModulus (A + B) PS →
          ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
            (PA + PB + (c : ℂ) • (V * (PA + PB) * Vᴴ) - PS).PosSemidef

private def A : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private def M : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 25 : ℂ) • !![9, -12; -12, 16]
private def B : Matrix (Fin 2) (Fin 2) ℂ := -M
private def PS : Matrix (Fin 2) (Fin 2) ℂ := (4 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
private def D : Matrix (Fin 2) (Fin 2) ℂ := A + M
private def x : Fin 2 → ℂ := ![1, 2]

private lemma A_eq_conjTranspose_mul_self :
    A = (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![1, 0; 0, 0] := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  all_goals rw [starRingEnd_apply] <;> norm_num

private lemma M_eq_smul_conjTranspose_mul_self :
    M = (1 / 25 : ℂ) •
      ((!![3, -4; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![3, -4; 0, 0]) := by
  let W : Matrix (Fin 2) (Fin 2) ℂ := !![3, -4; 0, 0]
  have hW : Wᴴ = Wᵀ := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [W, Matrix.conjTranspose_apply]
  rw [show (!![3, -4; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = W by rfl,
    show (!![3, -4; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = Wᴴ by rfl, hW]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [M, W, Matrix.mul_apply, Fin.sum_univ_two]

private lemma modulus_A : IsModulus A A := by
  refine ⟨?_, ?_⟩
  · rw [A_eq_conjTranspose_mul_self]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [A_eq_conjTranspose_mul_self]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    all_goals rw [starRingEnd_apply] <;> norm_num

private lemma modulus_M : IsModulus B M := by
  refine ⟨?_, ?_⟩
  · rw [M_eq_smul_conjTranspose_mul_self]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num [Complex.le_def])
  · have hMstar : Mᴴ = M := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [M, Matrix.conjTranspose_apply]
    change M * M = (-M)ᴴ * (-M)
    simp [map_neg, hMstar]

private lemma modulus_PS : IsModulus (A + B) PS := by
  refine ⟨?_, ?_⟩
  · exact Matrix.PosSemidef.smul Matrix.PosSemidef.one (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 4 / 5)
  · have hAstar : Aᴴ = A := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [A, Matrix.conjTranspose_apply]
    have hMstar : Mᴴ = M := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [M, Matrix.conjTranspose_apply]
    change PS * PS = (A + -M)ᴴ * (A + -M)
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_neg, hAstar, hMstar]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [A, M, PS, Matrix.mul_apply, Fin.sum_univ_two]

private lemma normal_A : IsNormalMatrix A := by
  have hAstar : Aᴴ = A := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [A, Matrix.conjTranspose_apply]
  rw [IsNormalMatrix]
  rw [hAstar]

private lemma normal_B : IsNormalMatrix B := by
  have hMstar : Mᴴ = M := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [M, Matrix.conjTranspose_apply]
  rw [IsNormalMatrix]
  simp [B, hMstar]

private lemma d_pos : D.PosSemidef := by
  exact modulus_A.1.add modulus_M.1

private lemma d_quad : RCLike.re (star x ⬝ᵥ (D *ᵥ x)) = 2 := by
  norm_num [x, D, A, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff, Complex.star_def]

private lemma ps_quad : RCLike.re (star x ⬝ᵥ (PS *ᵥ x)) = 4 := by
  norm_num [x, PS, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff, Complex.star_def]

private lemma d_upper : ((8 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - D).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self
      (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
  have hs := h.smul (by norm_num [Complex.le_def] : (0 : ℂ) ≤ 6 / 25)
  rw [show ((8 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - D) =
      (6 / 25 : ℂ) •
        ((!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * !![1, 2; 0, 0]) by
    let W : Matrix (Fin 2) (Fin 2) ℂ := !![1, 2; 0, 0]
    have hW : Wᴴ = Wᵀ := by
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [W, Matrix.conjTranspose_apply]
    rw [show (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = W by rfl,
      show (!![1, 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = Wᴴ by rfl, hW]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [D, A, M, W, Matrix.mul_apply, Fin.sum_univ_two]]
  exact hs

private lemma conjugation_quad (V : Matrix (Fin 2) (Fin 2) ℂ) :
    let y := Vᴴ *ᵥ x
    RCLike.re (star x ⬝ᵥ ((V * D * Vᴴ) *ᵥ x)) =
      RCLike.re (star y ⬝ᵥ (D *ᵥ y)) := by
  dsimp
  simp only [Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]

theorem result : ¬ claim := by
  intro hclaim
  rcases hclaim with ⟨c, hc, hmain⟩
  obtain ⟨V, hV, hQ⟩ := hmain A B normal_A normal_B A M PS modulus_A modulus_M modulus_PS
  have hqpos : (0 : ℝ) ≤ RCLike.re (star (Vᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Vᴴ *ᵥ x))) := by
    rw [← conjugation_quad V]
    exact (d_pos.mul_mul_conjTranspose_same V).re_dotProduct_nonneg x
  have hq : RCLike.re (star x ⬝ᵥ ((V * D * Vᴴ) *ᵥ x)) =
      RCLike.re (star (Vᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Vᴴ *ᵥ x))) := conjugation_quad V
  have hqupper : RCLike.re (star (Vᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Vᴴ *ᵥ x))) ≤ 8 := by
    have hu := d_upper.mul_mul_conjTranspose_same V
    have hconj : V * ((8 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - D) * Vᴴ =
        (8 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - V * D * Vᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      have hunit : V * Vᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) :=
        Matrix.mem_unitaryGroup_iff.mp hV
      simp [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_mul_assoc, hunit]
    have hu' : (((8 / 5 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
        V * D * Vᴴ)).PosSemidef := by rw [← hconj]; exact hu
    have hi := hu'.re_dotProduct_nonneg x
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub] at hi
    simp only [map_sub] at hi
    have hscalar : RCLike.re (star x ⬝ᵥ ((8 / 5 : ℂ) • x)) = 8 := by
      norm_num [x, dotProduct, Fin.sum_univ_two, Complex.ext_iff, Complex.star_def]
    rw [hscalar, hq] at hi
    linarith
  have hnonneg : 0 ≤ RCLike.re (star x ⬝ᵥ
      ((D + (c : ℂ) • (V * D * Vᴴ) - PS) *ᵥ x)) := by
    simpa [D] using hQ.re_dotProduct_nonneg x
  have hcalc : RCLike.re (star x ⬝ᵥ
      ((D + (c : ℂ) • (V * D * Vᴴ) - PS) *ᵥ x)) =
      -2 + c * RCLike.re (star (Vᴴ *ᵥ x) ⬝ᵥ (D *ᵥ (Vᴴ *ᵥ x))) := by
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_add, dotProduct_smul, map_add, map_sub]
    rw [d_quad, ps_quad]
    have hsmul : RCLike.re ((c : ℂ) • (star x ⬝ᵥ ((V * D * Vᴴ) *ᵥ x))) =
        c * RCLike.re (star x ⬝ᵥ ((V * D * Vᴴ) *ᵥ x)) := by
      change ((c : ℂ) * (star x ⬝ᵥ ((V * D * Vᴴ) *ᵥ x))).re = _
      rw [Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    rw [hsmul, hq]
    ring
  rw [hcalc] at hnonneg
  by_cases hc0 : 0 ≤ c
  · have : (1 / 4 : ℝ) ≤ c := by nlinarith [hqpos, hqupper]
    linarith
  · have hcneg : c < 0 := lt_of_not_ge hc0
    nlinarith [hqpos, hnonneg]

end D5.S3.Quantum.Matrix.NormalModulusTriangleConstant

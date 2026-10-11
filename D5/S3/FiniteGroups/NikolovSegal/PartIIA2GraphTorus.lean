/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIA2GraphTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option maxHeartbeats 1500000

/-! Actual SL3 graph automorphism and the isolating torus from Nikolov--Segal,
On finitely generated profinite groups II, printed pp260--261, equation (9).
All constructions and root laws hold over every field, including characteristics 2 and 3.
The optional two-step calculation assumes only its two explicitly named root-transport
laws; it makes no assertion about arbitrary automorphism classification or coverage. -/

namespace NikolovSegal.PartIIA2GraphTorus
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private def reverseTranspose (g : SL(3,F)) : SL(3,F) :=
  ⟨Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose, by
    rw [Matrix.det_reindex_self, Matrix.det_transpose, g.property]⟩

private theorem reverseTranspose_mul (g h : SL(3,F)) :
    reverseTranspose (g*h) = reverseTranspose h * reverseTranspose g := by
  apply Subtype.ext
  change Matrix.reindex Fin.revPerm Fin.revPerm (g.val*h.val).transpose =
    Matrix.reindex Fin.revPerm Fin.revPerm h.val.transpose *
    Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv h.val.transpose g.val.transpose
    Fin.revPerm.symm Fin.revPerm.symm Fin.revPerm.symm).symm

private theorem reverseTranspose_inv (g : SL(3,F)) :
    reverseTranspose g⁻¹ = (reverseTranspose g)⁻¹ := by
  apply Subtype.ext
  change Matrix.reindex Fin.revPerm Fin.revPerm (Matrix.adjugate g.val).transpose =
    Matrix.adjugate (Matrix.reindex Fin.revPerm Fin.revPerm g.val.transpose)
  rw [Matrix.adjugate_reindex, Matrix.adjugate_transpose]

private theorem reverseTranspose_twice (g : SL(3,F)) :
    reverseTranspose (reverseTranspose g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [reverseTranspose, Matrix.reindex_apply, Matrix.submatrix_apply, Fin.revPerm]

private def graphAction (g : SL(3,F)) : SL(3,F) := reverseTranspose g⁻¹

private theorem graphAction_twice (g : SL(3,F)) : graphAction (graphAction g) = g := by
  simp only [graphAction, reverseTranspose_inv, inv_inv, reverseTranspose_twice]

/-- The actual positive graph automorphism: inverse-transpose with coordinates reversed. -/
def tau : MulAut SL(3,F) where
  toFun := graphAction
  invFun := graphAction
  left_inv := graphAction_twice
  right_inv := graphAction_twice
  map_mul' g h := by
    change reverseTranspose (g*h)⁻¹ = reverseTranspose g⁻¹ * reverseTranspose h⁻¹
    rw [mul_inv_rev, reverseTranspose_mul]

/-- Literal matrix realization, equivalent to conjugation by the reversing permutation J. -/
theorem tau_coe (g : SL(3,F)) :
    (tau g).val = Matrix.reindex Fin.revPerm Fin.revPerm (g⁻¹).val.transpose := rfl

theorem tau_involutive : Function.Involutive (tau (F := F)) := graphAction_twice

theorem tau_sq : (tau (F := F))^2 = 1 := by
  apply MulEquiv.ext
  intro g
  exact tau_involutive g

theorem tau_T01 (t : F) :
    tau (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
      transvection (show (1:Fin 3) ≠ 2 by decide) (-t) := by
  apply Subtype.ext
  rw [tau_coe, transvection_inv]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.revPerm, transvection_coe]

theorem tau_T12 (t : F) :
    tau (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 1 by decide) (-t) := by
  apply Subtype.ext
  rw [tau_coe, transvection_inv]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.revPerm, transvection_coe]

theorem tau_T02 (t : F) :
    tau (transvection (show (0:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 2 by decide) (-t) := by
  apply Subtype.ext
  rw [tau_coe, transvection_inv]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.reindex_apply, Matrix.submatrix_apply,
    Fin.revPerm, transvection_coe]

/-- The determinant-one isolating torus, with weight 3 on T01 and weight 0 on T12. -/
def H (lambda : F) (hlambda : lambda ≠ 0) : SL(3,F) :=
  ⟨Matrix.diagonal ![lambda^2,lambda⁻¹,lambda⁻¹], by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ]
    field_simp [hlambda]⟩

theorem H_coe (lambda : F) (hlambda : lambda ≠ 0) :
    (H lambda hlambda).val = Matrix.diagonal ![lambda^2,lambda⁻¹,lambda⁻¹] := rfl

theorem H_det (lambda : F) (hlambda : lambda ≠ 0) :
    Matrix.det (Matrix.diagonal ![lambda^2,lambda⁻¹,lambda⁻¹]) = 1 :=
  (H lambda hlambda).property

private theorem H_inv (lambda : F) (hlambda : lambda ≠ 0) :
    (H lambda hlambda)⁻¹ = H lambda⁻¹ (inv_ne_zero hlambda) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1:Matrix (Fin 3) (Fin 3) F)
  rw [Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_one.mpr
  funext i
  fin_cases i
  all_goals simp [hlambda, pow_two]
  all_goals field_simp [hlambda]

theorem H_inv_coe (lambda : F) (hlambda : lambda ≠ 0) :
    ((H lambda hlambda)⁻¹).val = Matrix.diagonal ![(lambda⁻¹)^2,lambda,lambda] := by
  rw [H_inv, H_coe]
  simp only [inv_inv]

theorem H_conj_T01 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    MulAut.conj (H lambda hlambda) (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
      transvection (show (0:Fin 3) ≠ 1 by decide) (lambda^3*t) := by
  apply Subtype.ext
  change (H lambda hlambda).val * (transvection _ t).val * ((H lambda hlambda)⁻¹).val = _
  rw [H_coe, H_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.diagonal_mul, Matrix.mul_diagonal, transvection_coe,
    hlambda, pow_succ]
  all_goals field_simp [hlambda]

theorem H_conj_T12 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    MulAut.conj (H lambda hlambda) (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
      transvection (show (1:Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  change (H lambda hlambda).val * (transvection _ t).val * ((H lambda hlambda)⁻¹).val = _
  rw [H_coe, H_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.diagonal_mul, Matrix.mul_diagonal, transvection_coe,
    hlambda, pow_succ]
  all_goals field_simp [hlambda]

theorem H_conj_T02 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    MulAut.conj (H lambda hlambda) (transvection (show (0:Fin 3) ≠ 2 by decide) t) =
      transvection (show (0:Fin 3) ≠ 2 by decide) (lambda^3*t) := by
  apply Subtype.ext
  change (H lambda hlambda).val * (transvection _ t).val * ((H lambda hlambda)⁻¹).val = _
  rw [H_coe, H_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.diagonal_mul, Matrix.mul_diagonal, transvection_coe,
    hlambda, pow_succ]
  all_goals field_simp [hlambda]

/-- Exact two-step graph-orbit scalar calculation in the actual group. Multiplication
of MulAut is left-function composition. The hypotheses are literal root transport
laws for this beta, rather than a classification assumption for arbitrary beta. -/
theorem isolating_graph_square (lambda : F) (hlambda : lambda ≠ 0)
    (beta : MulAut SL(3,F)) (chi0 chi1 : F) (phi : RingAut F)
    (transport01 : ∀ t : F,
      beta (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
        transvection (show (1:Fin 3) ≠ 2 by decide) (chi0*phi t))
    (transport12 : ∀ t : F,
      beta (transvection (show (1:Fin 3) ≠ 2 by decide) t) =
        transvection (show (0:Fin 3) ≠ 1 by decide) (chi1*phi t)) (t : F) :
    ((MulAut.conj (H lambda hlambda)*beta)^2)
      (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
        transvection (show (0:Fin 3) ≠ 1 by decide)
          (lambda^3*chi1*phi chi0*(phi^2) t) := by
  change MulAut.conj (H lambda hlambda)
    (beta (MulAut.conj (H lambda hlambda)
      (beta (transvection (show (0:Fin 3) ≠ 1 by decide) t)))) = _
  rw [transport01, H_conj_T12, transport12, H_conj_T01, map_mul]
  congr 1
  change lambda^3*(chi1*(phi chi0*phi (phi t))) = lambda^3*chi1*phi chi0*phi (phi t)
  simp only [mul_assoc]

/-- The conditional two-step formula is consumed by the constructed graph automorphism:
the two minus signs cancel and the exact isolating weight is lambda cubed. -/
theorem isolating_tau_square_T01 (lambda : F) (hlambda : lambda ≠ 0) (t : F) :
    ((MulAut.conj (H lambda hlambda)*tau (F := F))^2)
      (transvection (show (0:Fin 3) ≠ 1 by decide) t) =
        transvection (show (0:Fin 3) ≠ 1 by decide) (lambda^3*t) := by
  simpa using isolating_graph_square lambda hlambda tau (-1) (-1) (1:RingAut F)
    (fun s => by simpa using tau_T01 s)
    (fun s => by simpa using tau_T12 s) t

end NikolovSegal.PartIIA2GraphTorus

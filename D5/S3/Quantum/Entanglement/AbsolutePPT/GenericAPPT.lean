/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/GenericAPPT
   mirror-E: none(waiver:symbolic-matrix-identities)
   anchors: []
   utility: none
   digest: Shared partial transpose, absolute PPT and unitary transport in arbitrary finite dimensions. -/

/-
The original namespaces retain the shared declarations' external names.
These are existing definitions and consumed algebraic helpers, not new claims.
The unitary extensions, conjugation identities and positivity implication are
symbolic over arbitrary finite index types. The two square-root coefficient
identities normalize the same symbolic Bell rotation in every dimension;
they are consumed by QutritSpectralReduction.bell_pt_principal and
UniformSchmidtBell.pairMatrix_unitary / pair_conjugate_diagonal, not a
standalone numerical certificate or reduction with numerical premises.
No declaration provides bounded enumeration, a checker, a numerical reduction
or a certified instance as independent new mathematical content.
The existing unfinished audit context remains #16011 and #17689.
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

/-- Partial transposition on the B factor, allowing unequal factor dimensions. -/
def partialTranspose {A B : Type*} (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := fun p q => ρ (p.1,q.2) (q.1,p.2)

end D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

def APPT {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Matrix (A × B) (A × B) ℂ) : Prop :=
  ∀ U : unitaryGroup (A × B) ℂ, partialTranspose ((U : Matrix _ _ ℂ) * M * (U : Matrix _ _ ℂ)ᴴ) |>.PosSemidef

end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction
open QutritPerturbationAttainment
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

noncomputable def extendUnitaryAlong {I J C : Type}
    [Fintype I] [Fintype J] [Fintype C]
    [DecidableEq I] [DecidableEq J] [DecidableEq C]
    (e : (J ⊕ C) ≃ I) (V : unitaryGroup J ℂ) : unitaryGroup I ℂ :=
  ⟨(fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm, by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_submatrix,
      submatrix_mul_equiv _ _ _ e.symm _]
    have hv : (V : Matrix J J ℂ) * (V : Matrix J J ℂ)ᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using mem_unitaryGroup_iff.mp V.property
    simp [fromBlocks_conjTranspose, fromBlocks_multiply, hv, fromBlocks_one]⟩

theorem extendUnitaryAlong_diagonal {I J C : Type}
    [Fintype I] [Fintype J] [Fintype C]
    [DecidableEq I] [DecidableEq J] [DecidableEq C]
    (e : (J ⊕ C) ≃ I) (V : unitaryGroup J ℂ) (x : J → ℂ) (y : C → ℂ) :
    (extendUnitaryAlong e V : Matrix I I ℂ) *
      diagonal (fun i => Sum.elim x y (e.symm i)) *
      (extendUnitaryAlong e V : Matrix I I ℂ)ᴴ =
    (fromBlocks ((V : Matrix J J ℂ) * diagonal x * (V : Matrix J J ℂ)ᴴ)
      0 0 (diagonal y)).submatrix e.symm e.symm := by
  change ((fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm) *
    diagonal (fun i => Sum.elim x y (e.symm i)) *
    ((fromBlocks (V : Matrix J J ℂ) 0 0 (1 : Matrix C C ℂ)).submatrix e.symm e.symm)ᴴ = _
  have hd : diagonal (fun i => Sum.elim x y (e.symm i)) =
      (diagonal (Sum.elim x y)).submatrix e.symm e.symm := by
    simpa only [Function.comp_def] using
      (Matrix.submatrix_diagonal_equiv (Sum.elim x y) e.symm).symm
  rw [hd, conjTranspose_submatrix, submatrix_mul_equiv _ _ _ e.symm _,
    submatrix_mul_equiv _ _ _ e.symm _, ← fromBlocks_diagonal x y]
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_one,
    conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, one_mul, mul_one]

noncomputable def permutationU {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) : unitaryGroup I ℂ := ⟨e.permMatrix ℂ, by
  rw [mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp⟩

theorem c_square : (Real.sqrt 2 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)=2 := by
    norm_cast
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [← mul_inv, h]
  norm_num

theorem c_star : star (Real.sqrt 2 : ℂ)⁻¹=(Real.sqrt 2 : ℂ)⁻¹ := by simp

theorem appt_conjugate {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {M : Matrix (A × B) (A × B) ℂ} (h : APPT M) (V : unitaryGroup (A × B) ℂ) :
    APPT ((V : Matrix (A × B) (A × B) ℂ)*M*(V : Matrix (A × B) (A × B) ℂ)ᴴ) := by
  intro U
  have hp := h (U*V)
  simpa only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hp

theorem real_psd_of_complex {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℝ) (h : (M.map Complex.ofReal).PosSemidef) : M.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have he := congrFun (congrFun h.isHermitian i) j
    have hr := congrArg Complex.re he
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply] using hr
  · intro x
    have hp := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have he : star (fun i => (x i : ℂ)) ⬝ᵥ ((M.map Complex.ofReal) *ᵥ (fun i => (x i : ℂ))) =
        ((star x ⬝ᵥ (M *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
        ← Complex.ofReal_sum, ← Complex.ofReal_mul]
    rw [he] at hp
    exact Complex.zero_le_real.mp hp

theorem permutation_conjugate {I : Type} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (M : Matrix I I ℂ) :
    (permutationU e : Matrix I I ℂ)*M*(permutationU e : Matrix I I ℂ)ᴴ=M.submatrix e e := by
  change e.permMatrix ℂ*M*(e.permMatrix ℂ)ᴴ=M.submatrix e e
  rw [Matrix.conjTranspose_permMatrix]
  change e.toPEquiv.toMatrix*M*(e⁻¹).toPEquiv.toMatrix=M.submatrix e e
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  rfl

end D5.S3.Quantum.Entanglement.AbsolutePPT.QutritSpectralReduction

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

theorem product_partialTranspose {A B C D : Type}
    (a : C → A) (b : D → B) (M : Matrix (A × B) (A × B) ℂ) :
    (partialTranspose M).submatrix (Prod.map a b) (Prod.map a b) =
      partialTranspose (M.submatrix (Prod.map a b) (Prod.map a b)) := rfl

end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitQuintitMaximumPurity

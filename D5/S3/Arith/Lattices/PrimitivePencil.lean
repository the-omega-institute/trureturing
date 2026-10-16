/- GID: D5/S3/Arith/Lattices/PrimitivePencil
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PrimitivePencil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One perturbation makes every integer pencil parameter primitive. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none; mathematical owners are pinned Mathlib.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/17570.
smithRect: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation, smith_staircase_gcd, matrix_smith_form, smith_staircase_minor.
transpose_smith_bases: proof_shape: bind-only; escape_witness: none; consumers: matrix_smith_form.
matrix_smith_form: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation.
staircase: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation, smith_staircase_gcd, smith_staircase_minor.
smith_staircase_minor: proof_shape: bind-only; escape_witness: none; consumers: smith_staircase_gcd.
smith_staircase_gcd: proof_shape: bind-only; escape_witness: none; consumers: primitive_pencil_perturbation.
primitive_pencil_perturbation: proof_shape: content; escape_witness: D5.S3.Arith.Lattices.PrimitivePencil.primitive_pencil_perturbation; consumers: exists_asymptotic_lower_family.
-/

import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
namespace D5.S3.Arith.Lattices.PrimitivePencil
open D5.S3.Arith.Lattices.CofactorKernel

open scoped BigOperators
open Matrix Module

private def smithRect {d : ℕ} (a : Fin d → ℤ) : Matrix (Fin d) (Fin (d+1)) ℤ :=
  fun i j => if j = i.castSucc then a i else 0

private theorem transpose_smith_bases {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hM : Function.Injective (fun x : Fin d → ℤ => M.transpose *ᵥ x)) :
    ∃ (b : Basis (Fin d) ℤ (Fin d → ℤ))
      (c : Basis (Fin (d+1)) ℤ (Fin (d+1) → ℤ)) (a : Fin d → ℤ),
      ∀ i : Fin d, M.transpose *ᵥ b i = a i • c i.castSucc := by
  classical
  let f : (Fin d → ℤ) →ₗ[ℤ] (Fin (d+1) → ℤ) := M.transpose.mulVecLin
  let e : (Fin d → ℤ) ≃ₗ[ℤ] LinearMap.range f := LinearEquiv.ofInjective f hM
  obtain ⟨n, s⟩ := (LinearMap.range f).smithNormalForm (Pi.basisFun ℤ (Fin (d+1)))
  let q : Fin n ≃ Fin d := s.bN.indexEquiv ((Pi.basisFun ℤ (Fin d)).map e)
  let emb : Fin d ↪ Fin (d+1) := q.symm.toEmbedding.trans s.f
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair emb
    (fun i : Fin d => i.castSucc) emb.injective (Fin.castSucc_injective d)
  refine ⟨(s.bN.map e.symm).reindex q, s.bM.reindex σ,
    fun i => s.a (q.symm i), fun i => ?_⟩
  have hemb : σ.symm i.castSucc = emb i := by
    rw [← hσ i]
    simp
  simp only [Basis.reindex_apply, Basis.map_apply, hemb]
  change f (e.symm (s.bN (q.symm i))) = _
  have he : f (e.symm (s.bN (q.symm i))) = (s.bN (q.symm i) : Fin (d+1) → ℤ) := by
    exact congrArg Subtype.val (e.apply_symm_apply (s.bN (q.symm i)))
  rw [he, s.snf]
  rfl


private theorem matrix_smith_form {d : ℕ}
    (M : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hM : Function.Injective (fun x : Fin d → ℤ => M.transpose *ᵥ x)) :
    ∃ (U : Matrix (Fin d) (Fin d) ℤ)
      (W : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (a : Fin d → ℤ),
      IsUnit U.det ∧ IsUnit W.det ∧ U * M * W = smithRect a := by
  classical
  obtain ⟨b,c,a,hbc⟩ := transpose_smith_bases M hM
  let sd := Pi.basisFun ℤ (Fin d)
  let sk := Pi.basisFun ℤ (Fin (d+1))
  let P := sd.toMatrix b
  let Q := c.toMatrix sk
  have hP : IsUnit P.det := Matrix.isUnit_det_of_left_inverse
    (b.toMatrix_mul_toMatrix_flip sd)
  have hQ : IsUnit Q.det := Matrix.isUnit_det_of_left_inverse
    (sk.toMatrix_mul_toMatrix_flip c)
  refine ⟨P.transpose,Q.transpose,a,?_,?_,?_⟩
  · simpa only [Matrix.det_transpose] using hP
  · simpa only [Matrix.det_transpose] using hQ
  · have he : Q * M.transpose * P = (smithRect a).transpose := by
      have hstd : LinearMap.toMatrix sd sk M.transpose.mulVecLin = M.transpose := by
        ext i j
        simp [LinearMap.toMatrix_apply, sd, sk, Matrix.mulVecLin_apply]
      change c.toMatrix sk * M.transpose * sd.toMatrix b = _
      rw [← hstd, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
      ext i j
      rw [LinearMap.toMatrix_apply]
      change c.repr (M.transpose *ᵥ b j) i = _
      rw [hbc j]
      rw [map_smul, Basis.repr_self]
      simp [smithRect, Matrix.transpose_apply, Finsupp.single_apply, eq_comm]
    have ht := congrArg Matrix.transpose he
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] using ht

open scoped BigOperators
open Matrix

private def staircase (d : ℕ) : Matrix (Fin d) (Fin (d+1)) ℤ :=
  fun i j => if j = i.succ then 1 else 0

private theorem smith_staircase_minor {d : ℕ} (a : Fin d → ℤ) (t : ℤ) :
    ((t • smithRect a + staircase d).submatrix id Fin.succ).det = 1 := by
  let N := (t • smithRect a + staircase d).submatrix id Fin.succ
  have hN : N.IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have h1 : j.succ ≠ i.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.coe_castSucc] at hv
      omega
    have h2 : j.succ ≠ i.succ := by
      exact Fin.succ_inj.ne.mpr (ne_of_gt hij')
    simp only [N, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      smithRect, staircase, id_eq, if_neg h1, if_neg h2, smul_eq_mul, mul_zero, add_zero]
  rw [Matrix.det_of_isLowerTriangular N hN]
  apply Finset.prod_eq_one
  intro i hi
  have h1 : i.succ ≠ i.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc] at hv
    omega
  simp [N, Matrix.submatrix, smithRect, staircase, h1]

private theorem smith_staircase_gcd {d : ℕ} (a : Fin d → ℤ) (t : ℤ) :
    Finset.univ.gcd (cofactor (t • smithRect a + staircase d)) = 1 := by
  have hc : cofactor (t • smithRect a + staircase d) 0 = 1 := by
    simpa [cofactor] using smith_staircase_minor a t
  have hd : Finset.univ.gcd (cofactor (t • smithRect a + staircase d)) ∣ 1 := by
    rw [← hc]
    exact Finset.gcd_dvd (Finset.mem_univ 0)
  have hu := (isUnit_iff_dvd_one.mpr hd)
  have he := normalize_eq_one.mpr hu
  simpa only [Finset.normalize_gcd] using he

open scoped BigOperators
open Matrix

theorem primitive_pencil_perturbation {d : ℕ}
    (A : Matrix (Fin d) (Fin (d+1)) ℤ)
    (hA : Function.Injective (fun x : Fin d → ℤ => A.transpose *ᵥ x)) :
    ∃ B : Matrix (Fin d) (Fin (d+1)) ℤ,
      ∀ t : ℤ, Finset.univ.gcd (cofactor (t • A + B)) = 1 := by
    obtain ⟨U,W,a,hU,hW,hS⟩ := matrix_smith_form A hA
    let B := U⁻¹ * staircase d * W⁻¹
    refine ⟨B, fun t => ?_⟩
    have hAU : U⁻¹ * smithRect a * W⁻¹ = A := by
      rw [← hS]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv W hW,
        Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left U _ hU]
    have he : t • A + B = U⁻¹ * (t • smithRect a + staircase d) * W⁻¹ := by
      rw [Matrix.mul_add, Matrix.add_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul, hAU]
    rw [he]
    exact cofactor_gcd_one_mul_right _ _ (Matrix.isUnit_nonsing_inv_det W hW)
      (cofactor_gcd_one_mul_left _ _ (Matrix.isUnit_nonsing_inv_det U hU)
        (smith_staircase_gcd a t))

end D5.S3.Arith.Lattices.PrimitivePencil

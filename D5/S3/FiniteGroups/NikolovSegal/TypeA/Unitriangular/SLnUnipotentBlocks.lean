/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NikolovSegal.SLnUnipotentWidth
open Matrix
universe u
variable {F : Type u} [Field F]

def Upper {n : ℕ} (A : SpecialLinearGroup (Fin n) F) : Prop :=
  (∀ i j : Fin n, j < i → A.val i j = 0) ∧ (∀ i : Fin n, A.val i i = 1)

def Lower {n : ℕ} (A : SpecialLinearGroup (Fin n) F) : Prop :=
  (∀ i j : Fin n, i < j → A.val i j = 0) ∧ (∀ i : Fin n, A.val i i = 1)

def reindexSL {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) : SpecialLinearGroup ι F ≃* SpecialLinearGroup κ F where
  toFun A := ⟨Matrix.reindex e e A.val, by rw [det_reindex_self,A.property]⟩
  invFun A := ⟨Matrix.reindex e.symm e.symm A.val, by rw [det_reindex_self,A.property]⟩
  left_inv A := Subtype.ext (by simp [Matrix.reindex_apply,Matrix.submatrix_submatrix])
  right_inv A := Subtype.ext (by simp [Matrix.reindex_apply,Matrix.submatrix_submatrix])
  map_mul' A B := Subtype.ext ((Matrix.reindexRingEquiv F e).map_mul A.val B.val)

variable {r : ℕ}
abbrev BlockSL (r : ℕ) (F : Type u) [Field F] := SpecialLinearGroup (Fin r ⊕ Fin 1) F

/-- Genuine determinant-one Levi embedding, with the last coordinate fixed. -/
def embed : SpecialLinearGroup (Fin r) F →* BlockSL r F where
  toFun B := ⟨fromBlocks B.val 0 0 1, by simp [det_fromBlocks_zero₂₁,B.property]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' B C := Subtype.ext (by simp [SpecialLinearGroup.coe_mul,fromBlocks_multiply])

/-- Actual last-column upper unipotent matrices. -/
def upperRad (v : Fin r → F) : BlockSL r F :=
  ⟨fromBlocks 1 (fun i _ => v i) 0 1, by simp [det_fromBlocks_zero₂₁]⟩

/-- Actual last-row lower unipotent matrices. -/
def lowerRad (v : Fin r → F) : BlockSL r F :=
  ⟨fromBlocks 1 0 (fun _ i => v i) 1, by simp [det_fromBlocks_zero₁₂]⟩

@[simp] theorem upperRad_zero : upperRad (0 : Fin r → F) = 1 := by
  apply Subtype.ext
  change fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (1 : Matrix (Fin 1) (Fin 1) F) = 1
  exact fromBlocks_one

@[simp] theorem lowerRad_zero : lowerRad (0 : Fin r → F) = 1 := by
  apply Subtype.ext
  change fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (1 : Matrix (Fin 1) (Fin 1) F) = 1
  exact fromBlocks_one

theorem upperRad_add (v w : Fin r → F) : upperRad (v+w) = upperRad v * upperRad w := by
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,upperRad,fromBlocks_multiply]
  ext i j
  simp [add_comm]

theorem lowerRad_add (v w : Fin r → F) : lowerRad (v+w) = lowerRad v * lowerRad w := by
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,lowerRad,fromBlocks_multiply]
  ext i j
  rfl

@[simp] theorem upperRad_inv (v : Fin r → F) : (upperRad v)⁻¹ = upperRad (-v) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← upperRad_add,neg_add_cancel,upperRad_zero]

@[simp] theorem lowerRad_inv (v : Fin r → F) : (lowerRad v)⁻¹ = lowerRad (-v) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← lowerRad_add,neg_add_cancel,lowerRad_zero]

/-- Every actual Levi element normalizes the full last-column radical. -/
theorem embed_conjugate_upperRad (B : SpecialLinearGroup (Fin r) F) (v : Fin r → F) :
    embed B * upperRad v * (embed B)⁻¹ = upperRad (B.val *ᵥ v) := by
  rw [← (embed (F := F)).map_inv B]
  have hBB : B.val * (B⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel B)
  simp only [SpecialLinearGroup.coe_inv] at hBB
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,embed,upperRad,fromBlocks_multiply,hBB]
  ext i j
  simp [Matrix.mul_apply,Matrix.mulVec,dotProduct]

/-- Every actual Levi element normalizes the full last-row radical. -/
theorem embed_conjugate_lowerRad (B : SpecialLinearGroup (Fin r) F) (v : Fin r → F) :
    embed B * lowerRad v * (embed B)⁻¹ = lowerRad (v ᵥ* (B⁻¹).val) := by
  rw [← (embed (F := F)).map_inv B]
  have hBB : B.val * (B⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel B)
  simp only [SpecialLinearGroup.coe_inv] at hBB
  apply Subtype.ext
  simp [SpecialLinearGroup.coe_mul,embed,lowerRad,fromBlocks_multiply,hBB]
  ext i j
  simp [Matrix.mul_apply,Matrix.vecMul,dotProduct]

theorem upperRad_mul_embed (B : SpecialLinearGroup (Fin r) F) (v : Fin r → F) :
    upperRad v * embed B = embed B * upperRad ((B⁻¹).val *ᵥ v) := by
  have h := embed_conjugate_upperRad B⁻¹ v
  simp only [map_inv,inv_inv] at h
  calc
    upperRad v * embed B = embed B * ((embed B)⁻¹ * upperRad v * embed B) := by group
    _ = embed B * upperRad ((B⁻¹).val *ᵥ v) := by rw [h]

/-- Upper-triangular Levi factors and upper radicals remain literally upper
unitriangular in the canonical Fin(r+1) coordinates. -/
theorem embed_mul_upper (B : SpecialLinearGroup (Fin r) F) (hB : Upper B)
    (v : Fin r → F) :
    Upper (reindexSL (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1))
      (embed B * upperRad v)) := by
  constructor
  · intro i j hij
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective i
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [SpecialLinearGroup.coe_mul,reindexSL,embed,upperRad,lowerRad,fromBlocks_multiply] using hB.1 i j hij
      | inr j => simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
          Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd] at hij; omega
    | inr i =>
      cases j with
      | inl j => simp [SpecialLinearGroup.coe_mul,reindexSL,embed,upperRad,fromBlocks_multiply]
      | inr j => have hi : i = j := Subsingleton.elim _ _; subst hi; exact False.elim (lt_irrefl _ hij)
  · intro i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective i
    cases i with
    | inl i => simpa [SpecialLinearGroup.coe_mul,reindexSL,embed,upperRad,fromBlocks_multiply] using hB.2 i
    | inr i => simp [SpecialLinearGroup.coe_mul,reindexSL,embed,upperRad,fromBlocks_multiply]

theorem embed_mul_lower (B : SpecialLinearGroup (Fin r) F) (hB : Lower B)
    (v : Fin r → F) :
    Lower (reindexSL (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1))
      (embed B * lowerRad v)) := by
  constructor
  · intro i j hij
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective i
    obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective j
    cases i with
    | inl i =>
      cases j with
      | inl j => simpa [SpecialLinearGroup.coe_mul,reindexSL,embed,upperRad,lowerRad,fromBlocks_multiply] using hB.1 i j hij
      | inr j => simp [SpecialLinearGroup.coe_mul,reindexSL,embed,lowerRad,fromBlocks_multiply]
    | inr i =>
      cases j with
      | inl j => simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
          Fin.lt_def,Fin.val_castAdd,Fin.val_natAdd] at hij; omega
      | inr j => have hi : i = j := Subsingleton.elim _ _; subst hi; exact False.elim (lt_irrefl _ hij)
  · intro i
    obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r+1)).surjective i
    cases i with
    | inl i => simpa [SpecialLinearGroup.coe_mul,reindexSL,embed,lowerRad,fromBlocks_multiply] using hB.2 i
    | inr i => simp [SpecialLinearGroup.coe_mul,reindexSL,embed,lowerRad,fromBlocks_multiply]

end NikolovSegal.SLnUnipotentWidth

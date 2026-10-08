/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIA2Orbital
import D5.S3.FiniteGroups.NikolovSegal.PartIISL2RootSylow

set_option autoImplicit false

/-! Literal SL3 upper-unitriangular geometry and the lower two-dimensional
action of the first-vector stabilizer. The owner's actual upper3/upperUnipotent
and their matrix group laws are reused from their completed frozen module. -/
namespace NikolovSegal.PartIISL3UnipotentSylow
open NikolovSegal.PartIIA2Orbital Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

/-- The owner's actual SL3 upper-unipotent subgroup, with literal carrier below. -/
abbrev U3 : Subgroup SL(3,F) := upperUnipotent

theorem mem_U3_iff (A : SL(3,F)) :
    A ∈ U3 ↔ (∀ i j : Fin 3, j < i → A i j = 0) ∧ (∀ i : Fin 3, A i i = 1) := by
  constructor
  · rintro ⟨a,b,c,rfl⟩
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [upper3]
    · intro i
      fin_cases i <;> simp [upper3]
  · rintro ⟨ht,hd⟩
    refine ⟨A 0 1,A 1 2,A 0 2,?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [upper3,hd,ht 1 0 (by decide),ht 2 0 (by decide),ht 2 1 (by decide)]

/-- Actual three-field coordinates, not an abstract replacement group. -/
def upperCoordinateEquiv : (Fin 3 → F) ≃ U3 (F := F) where
  toFun v := ⟨upper3 (v 0) (v 1) (v 2),v 0,v 1,v 2,rfl⟩
  invFun A := ![A.val 0 1,A.val 1 2,A.val 0 2]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv A := by
    apply Subtype.ext
    obtain ⟨a,b,c,h⟩ := A.property
    change upper3 (A.val 0 1) (A.val 1 2) (A.val 0 2) = A.val
    rw [← h]
    rfl

theorem card_U3 : Nat.card (U3 (F := F)) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (upperCoordinateEquiv (F := F)),Nat.card_fun,Nat.card_fin]

theorem first_column_of_fix (A : SL(3,F))
    (hA : A • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1) :
    ∀ i : Fin 3, A i 0 = if i = 0 then 1 else 0 := by
  intro i
  simpa [Matrix.SpecialLinearGroup.smul_def,Matrix.smul_eq_mulVec,Matrix.mulVec_single,
    Pi.single_apply,eq_comm]
    using congrFun hA i

/-- The literal bottom-right block of an actual determinant-one matrix. -/
def bottomBlock (A : SL(3,F)) : Matrix (Fin 2) (Fin 2) F :=
  A.val.submatrix Fin.succ Fin.succ

theorem bottomBlock_det (A : SL(3,F))
    (hA : A • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1) :
    (bottomBlock A).det = 1 := by
  have hc := first_column_of_fix A hA
  have hd := A.property
  rw [Matrix.det_fin_three] at hd
  rw [Matrix.det_fin_two]
  simpa [bottomBlock,hc 0,hc 1,hc 2] using hd

/-- A genuine SL2 representation of any subgroup fixing the first vector. -/
def bottomBlockHom (H : Subgroup SL(3,F))
    (hH : ∀ A : H, (A : SL(3,F)) • (Pi.single 0 1 : Fin 3 → F) = Pi.single 0 1) :
    H →* SL(2,F) where
  toFun A := ⟨bottomBlock A.val,bottomBlock_det A.val (hH A)⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    simp [bottomBlock,Matrix.one_apply]
  map_mul' A B := by
    apply Subtype.ext
    change bottomBlock (A.val*B.val) = bottomBlock A.val * bottomBlock B.val
    have hc := first_column_of_fix A.val (hH A)
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [bottomBlock,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,
      Fin.sum_univ_succ,hc 1,hc 2]

end NikolovSegal.PartIISL3UnipotentSylow

/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Actual upper unitriangular and upper triangular subgroups of SLn.
Native block-triangular multiplication and inversion are reused. -/
namespace NikolovSegal.SLnNormalizer
open Matrix
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- The literal zero entries strictly below the diagonal. -/
def Upper (g : SpecialLinearGroup (Fin n) F) : Prop :=
  ∀ r c : Fin n, c.val < r.val → g.val r c = 0

theorem upper_one : Upper (1 : SpecialLinearGroup (Fin n) F) := by
  intro r c h
  have hne : r ≠ c := fun he => by subst c; omega
  simp [SpecialLinearGroup.coe_one, hne]

theorem upper_mul {g h : SpecialLinearGroup (Fin n) F}
    (hg : Upper g) (hh : Upper h) : Upper (g*h) := by
  exact fun r c hrc => Matrix.BlockTriangular.mul
    (show g.val.BlockTriangular Fin.val from fun {_ _} ht => hg _ _ ht)
    (show h.val.BlockTriangular Fin.val from fun {_ _} ht => hh _ _ ht) hrc

theorem upper_inv {g : SpecialLinearGroup (Fin n) F} (hg : Upper g) :
    Upper g⁻¹ := by
  letI : Invertible g.val := (SpecialLinearGroup.toGL g).invertible
  have hinv : (g⁻¹).val = g.val⁻¹ :=
    GeneralLinearGroup.coe_inv (SpecialLinearGroup.toGL g)
  intro r c hrc
  rw [hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular
    (show g.val.BlockTriangular Fin.val from fun {_ _} ht => hg _ _ ht) hrc

/-- Diagonal multiplication uses only the native literal triangular entries. -/
theorem upper_mul_diag {g h : SpecialLinearGroup (Fin n) F}
    (hg : Upper g) (hh : Upper h) (i : Fin n) :
    (g*h).val i i = g.val i i * h.val i i := by
  change ∑ j : Fin n, g.val i j * h.val j i = _
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_cases hj : j.val < i.val
    · simp [hg i j hj]
    · have hij : i.val < j.val := by
        have hne : j.val ≠ i.val := fun he => hji (Fin.ext he)
        omega
      simp [hh j i hij]
  · simp

/-- The actual full upper-unitriangular subgroup, in every rank and field. -/
def Uplus (n : ℕ) (F : Type u) [Field F] :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | Upper g ∧ ∀ i : Fin n, g.val i i = 1}
  one_mem' := ⟨upper_one, by intro i; simp⟩
  mul_mem' := by
    intro g h hg hh
    refine ⟨upper_mul hg.1 hh.1, ?_⟩
    intro i
    rw [upper_mul_diag hg.1 hh.1 i, hg.2 i, hh.2 i, one_mul]
  inv_mem' := by
    intro g hg
    refine ⟨upper_inv hg.1, ?_⟩
    intro i
    have he := upper_mul_diag hg.1 (upper_inv hg.1) i
    simpa [hg.2 i] using he.symm

theorem mem_Uplus_iff (g : SpecialLinearGroup (Fin n) F) :
    g ∈ Uplus n F ↔
      (∀ r c : Fin n, c.val < r.val → g.val r c = 0) ∧
      ∀ i : Fin n, g.val i i = 1 := Iff.rfl

/-- The actual determinant-one upper triangular subgroup. -/
def Borel (n : ℕ) (F : Type u) [Field F] :
    Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | Upper g}
  one_mem' := upper_one
  mul_mem' := upper_mul
  inv_mem' := upper_inv

theorem transvection_mem_Uplus {i j : Fin n} (hij : i.val < j.val) (b : F) :
    SpecialLinearGroup.transvection (ne_of_lt (show i < j from hij)) b ∈ Uplus n F := by
  refine ⟨?_, ?_⟩
  · exact Matrix.blockTriangular_transvection (b := Fin.val) hij.le b
  · intro k
    change (1 + Matrix.single i j b : Matrix (Fin n) (Fin n) F) k k = 1
    have hne : i ≠ j := ne_of_lt (show i < j from hij)
    simp only [Matrix.add_apply, Matrix.one_apply_eq]
    rw [Matrix.single_apply_of_ne]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact hne rfl

end NikolovSegal.SLnNormalizer

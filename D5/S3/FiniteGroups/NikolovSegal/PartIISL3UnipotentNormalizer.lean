/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIISL3UnipotentNormalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual SL3 root geometry and ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentStructure
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false

/-! The normalizer of the actual SL3 upper-unitriangular subgroup is the
actual upper-triangular determinant-one subgroup, over every field.
The accepted upper3 chart and literal carrier adapter are reused unchanged. -/
namespace NikolovSegal.PartIISL3UnipotentNormalizer
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIISL3UnipotentSylow
open Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]

private theorem upper_inv (g : SL(3,F))
    (hg : ∀ i j : Fin 3, j < i → g i j = 0) :
    ∀ i j : Fin 3, j < i → g⁻¹ i j = 0 := by
  intro i j hij
  change (Matrix.adjugate g.val) i j = 0
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j
  all_goals simp_all [hg 1 0 (by decide),hg 2 0 (by decide),hg 2 1 (by decide)]

private theorem upper_mul (g h : SL(3,F))
    (hg : ∀ i j : Fin 3, j < i → g i j = 0)
    (hh : ∀ i j : Fin 3, j < i → h i j = 0) :
    ∀ i j : Fin 3, j < i → (g*h) i j = 0 := by
  exact fun i j hij => Matrix.BlockTriangular.mul
    (show g.val.IsUpperTriangular from fun {_ _} h => hg _ _ h)
    (show h.val.IsUpperTriangular from fun {_ _} h => hh _ _ h) hij

private theorem upper_mul_diag (g h : SL(3,F))
    (hg : ∀ i j : Fin 3, j < i → g i j = 0)
    (hh : ∀ i j : Fin 3, j < i → h i j = 0) (i : Fin 3) :
    (g*h) i i = g i i * h i i := by
  fin_cases i
  all_goals simp [coe_mul,Matrix.mul_apply,Fin.sum_univ_succ,
    hg 1 0 (by decide),hg 2 0 (by decide),hg 2 1 (by decide),
    hh 1 0 (by decide),hh 2 0 (by decide),hh 2 1 (by decide)]

/-- A normalizer element preserves the actual first line and first-two-coordinate
plane. Two actual upper3 elements detect the three entries below the diagonal. -/
theorem below_diagonal_zero_of_normalizer (g : SL(3,F))
    (hg : g ∈ (Subgroup.normalizer (U3 (F := F) : Set SL(3,F)))) :
    ∀ i j : Fin 3, j < i → g i j = 0 := by
  have hu01 : upper3 (1:F) 0 0 ∈ U3 := ⟨1,0,0,rfl⟩
  have hu12 : upper3 (0:F) 1 0 ∈ U3 := ⟨0,1,0,rfl⟩
  have hv := (Subgroup.mem_normalizer_iff''.mp hg _).mp hu01
  obtain ⟨a,b,c,hv⟩ := hv
  have heq : g * upper3 a b c = upper3 (1:F) 0 0 * g := by
    rw [hv]
    simp [mul_assoc]
  have h10 : g 1 0 = 0 := by
    have he := congrArg (fun A : SL(3,F) => A 0 0) heq
    change (g.val * (upper3 a b c).val) 0 0 =
      ((upper3 (1:F) 0 0).val * g.val) 0 0 at he
    have he' : g 0 0 = g 0 0 + g 1 0 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_succ,upper3] using he
    exact add_eq_left.mp he'.symm
  have hw01 := (Subgroup.mem_normalizer_iff.mp hg _).mp hu01
  obtain ⟨a01,b01,c01,hw01⟩ := hw01
  have heq01 : upper3 a01 b01 c01 * g = g * upper3 (1:F) 0 0 := by
    rw [hw01]
    simp [mul_assoc]
  have h20 : g 2 0 = 0 := by
    have he := congrArg (fun A : SL(3,F) => A 2 1) heq01
    change ((upper3 a01 b01 c01).val * g.val) 2 1 =
      (g.val * (upper3 (1:F) 0 0).val) 2 1 at he
    have he' : g 2 1 = g 2 0 + g 2 1 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_succ,upper3] using he
    exact add_eq_right.mp he'.symm
  have hw12 := (Subgroup.mem_normalizer_iff.mp hg _).mp hu12
  obtain ⟨a12,b12,c12,hw12⟩ := hw12
  have heq12 : upper3 a12 b12 c12 * g = g * upper3 (0:F) 1 0 := by
    rw [hw12]
    simp [mul_assoc]
  have h21 : g 2 1 = 0 := by
    have he := congrArg (fun A : SL(3,F) => A 2 2) heq12
    change ((upper3 a12 b12 c12).val * g.val) 2 2 =
      (g.val * (upper3 (0:F) 1 0).val) 2 2 at he
    have he' : g 2 2 = g 2 1 + g 2 2 := by
      simpa [Matrix.mul_apply,Fin.sum_univ_succ,upper3] using he
    exact add_eq_right.mp he'.symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Genuine upper-triangular conjugation preserves the literal unitriangular
carrier, including its unit diagonal. -/
theorem conjugate_mem_U3_of_upper (g : SL(3,F))
    (hg : ∀ i j : Fin 3, j < i → g i j = 0)
    (h : SL(3,F)) (hh : h ∈ U3) : g*h*g⁻¹ ∈ U3 := by
  obtain ⟨hht,hhd⟩ := (mem_U3_iff h).mp hh
  have hgi := upper_inv g hg
  have hgh := upper_mul g h hg hht
  apply (mem_U3_iff _).mpr
  refine ⟨upper_mul (g*h) g⁻¹ hgh hgi,?_⟩
  intro i
  rw [upper_mul_diag (g*h) g⁻¹ hgh hgi i,upper_mul_diag g h hg hht i,hhd i,
    mul_one,← upper_mul_diag g g⁻¹ hg hgi i,mul_inv_cancel]
  simp [coe_one]

/-- Literal SL3 normalizer/Borel recognition over every field. -/
theorem mem_normalizer_iff_upper (g : SL(3,F)) :
    g ∈ (Subgroup.normalizer (U3 (F := F) : Set SL(3,F))) ↔
      ∀ i j : Fin 3, j < i → g i j = 0 := by
  refine ⟨below_diagonal_zero_of_normalizer g,fun hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conjugate_mem_U3_of_upper g hg h
  · intro hh
    have hmem := conjugate_mem_U3_of_upper g⁻¹ (upper_inv g hg) _ hh
    simpa [mul_assoc] using hmem

/-- A bare automorphism preserving U3 preserves its actual Borel normalizer.
This is native normalizer functoriality applied to the actual subgroup. -/
theorem automorphism_normalizer_map (beta : MulAut SL(3,F))
    (hbeta : (U3 (F := F)).map beta.toMonoidHom = U3) :
    (Subgroup.normalizer (U3 (F := F) : Set SL(3,F))).map beta.toMonoidHom =
      Subgroup.normalizer (U3 (F := F) : Set SL(3,F)) := by
  rw [Subgroup.map_equiv_normalizer_eq,hbeta]

/-- Consequently the same bare automorphism preserves the literal
upper-triangular matrix condition, without any coordinate/classification law. -/
theorem automorphism_upper_iff (beta : MulAut SL(3,F))
    (hbeta : (U3 (F := F)).map beta.toMonoidHom = U3) (g : SL(3,F)) :
    (∀ i j : Fin 3, j < i → beta g i j = 0) ↔
      ∀ i j : Fin 3, j < i → g i j = 0 := by
  rw [← mem_normalizer_iff_upper,← mem_normalizer_iff_upper]
  have hm : beta g ∈ (Subgroup.normalizer (U3 (F := F) : Set SL(3,F))).map
      beta.toMonoidHom ↔ g ∈ Subgroup.normalizer (U3 (F := F) : Set SL(3,F)) :=
    Subgroup.mem_map_iff_mem beta.injective
  rwa [automorphism_normalizer_map beta hbeta] at hm

end NikolovSegal.PartIISL3UnipotentNormalizer

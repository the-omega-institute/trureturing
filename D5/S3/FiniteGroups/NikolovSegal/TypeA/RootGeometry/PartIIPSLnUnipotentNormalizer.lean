/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentNormalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnUnipotentNormalizer
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The actual projective upper-unitriangular normalizer in every rank,
over every field. The accepted actual SLn normalizer proof is imported
unchanged. Characteristic polynomials eliminate central discrepancies
without any rank, characteristic, finiteness or automorphism-lift premise. -/
namespace NikolovSegal.PSLnNormalizer
open Matrix Polynomial
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)

/-- The actual central-quotient image of the full SLn upper unitriangular subgroup. -/
def projectiveUplus (n : ℕ) (F : Type u) [Field F] :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) F) :=
  (Uplus n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))

/-- Native triangular characteristic-polynomial recognition applied to
the actual scalar multiple of a literal unitriangular matrix. -/
theorem scalar_unitriangular_charpoly (z : F) (y : G) (hy : y ∈ Uplus n F) :
    (Matrix.scalar (Fin n) z * y.val).charpoly = (X-C z)^n := by
  obtain ⟨hyt,hyd⟩ := (mem_Uplus_iff y).mp hy
  have ht : (Matrix.scalar (Fin n) z * y.val).IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal (fun _ : Fin n => z)).mul
      (show y.val.IsUpperTriangular from fun {_ _} h => hyt _ _ h)
  rw [Matrix.charpoly_of_isUpperTriangular _ ht]
  simp [hyd]

/-- Equality of projective conjugates of actual unitriangular matrices
lifts to actual SLn equality. The rank0/1 cases use native subsingletons;
in positive higher ranks evaluation of the actual charpoly at1 forces the
central scalar z to equal1, even when the characteristic divides the rank. -/
theorem conjugate_eq_of_quotient_eq (A x y : G) (hx : x ∈ Uplus n F)
    (hy : y ∈ Uplus n F) (hq : π (A*x*A⁻¹) = π y) : A*x*A⁻¹ = y := by
  by_cases hn : n = 0
  · subst n
    exact Subsingleton.elim _ _
  by_cases hn1 : n = 1
  · subst n
    exact Subsingleton.elim _ _
  let c := (A*x*A⁻¹)/y
  have hc : c ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp hq
  obtain ⟨z,_,hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hm : A*x*A⁻¹ = c*y := by simp [c]
  have hxpoly : x.val.charpoly = (X-1)^n := by
    simpa using scalar_unitriangular_charpoly (1:F) x hx
  have hcp : (A*x*A⁻¹).val.charpoly = (X-1)^n := by
    have hi : (A⁻¹).val = A.val⁻¹ :=
      GeneralLinearGroup.coe_inv (SpecialLinearGroup.toGL A)
    change (A.val*x.val*(A⁻¹).val).charpoly = _
    rw [hi]
    exact (Matrix.charpoly_units_conj (SpecialLinearGroup.toGL A) x.val).trans hxpoly
  have hcpz : (A*x*A⁻¹).val.charpoly = (X-C z)^n := by
    rw [hm]
    change (c.val*y.val).charpoly = _
    rw [← hsc]
    exact scalar_unitriangular_charpoly z y hy
  have he : (1-z)^n = (0:F) := by
    have he := congrArg (Polynomial.eval (1:F)) (hcpz.symm.trans hcp)
    simpa [hn] using he
  have hz1 : z = 1 := (sub_eq_zero.mp ((pow_eq_zero_iff hn).mp he)).symm
  have hc1 : c = 1 := by
    apply Subtype.ext
    change c.val = (1 : Matrix (Fin n) (Fin n) F)
    rw [← hsc,hz1]
    simp
  simpa [hc1] using hm

/-- Projective conjugation membership lifts on the actual unitriangular carrier. -/
theorem projective_conjugate_mem_iff (A x : G) (hx : x ∈ Uplus n F) :
    π (A*x*A⁻¹) ∈ projectiveUplus n F ↔ A*x*A⁻¹ ∈ Uplus n F := by
  constructor
  · intro h
    obtain ⟨y,hy,hq⟩ := Subgroup.mem_map.mp h
    rw [conjugate_eq_of_quotient_eq A x y hx hy hq.symm]
    exact hy
  · intro h
    exact Subgroup.mem_map.mpr ⟨A*x*A⁻¹,h,rfl⟩

private theorem lift_normalizer_conjugate (A : G)
    (hA : π A ∈ Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)))
    (x : G) (hx : x ∈ Uplus n F) : A*x*A⁻¹ ∈ Uplus n F := by
  apply (projective_conjugate_mem_iff A x hx).mp
  have hp : π x ∈ projectiveUplus n F := Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  have hc := (Subgroup.mem_normalizer_iff.mp hA (π x)).mp hp
  simpa only [map_mul,map_inv] using hc

/-- Exact normalizer preimage under the actual central quotient. -/
theorem quotient_mem_normalizer_iff (A : G) :
    π A ∈ Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)) ↔
      A ∈ Subgroup.normalizer (Uplus n F : Set G) := by
  constructor
  · intro hA
    have hi : π A⁻¹ ∈ Subgroup.normalizer
        (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)) := by
      simpa only [map_inv] using
        (Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F))).inv_mem hA
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · exact lift_normalizer_conjugate A hA x
    · intro hx
      have h := lift_normalizer_conjugate A⁻¹ hi (A*x*A⁻¹) hx
      simpa [mul_assoc] using h
  · intro hA
    have hm : π A ∈ (Subgroup.normalizer (Uplus n F : Set G)).map π :=
      Subgroup.mem_map.mpr ⟨A,hA,rfl⟩
    exact Subgroup.le_normalizer_map π hm

/-- Literal every-field/all-rank recognition of projective normalization. -/
theorem quotient_mem_normalizer_iff_upper (A : G) :
    π A ∈ Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)) ↔
      ∀ r c : Fin n, c.val < r.val → A.val r c = 0 :=
  (quotient_mem_normalizer_iff A).trans (mem_normalizer_iff_upper A)

/-- An actual projective element normalizes precisely when it admits an
actual determinant-one upper triangular representative. -/
theorem mem_projective_normalizer_iff_upper (g : ProjectiveSpecialLinearGroup (Fin n) F) :
    g ∈ Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)) ↔
      ∃ A : G, π A = g ∧ ∀ r c : Fin n, c.val < r.val → A.val r c = 0 := by
  constructor
  · intro hg
    obtain ⟨A,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) g
    exact ⟨A,rfl,(quotient_mem_normalizer_iff_upper A).mp hg⟩
  · rintro ⟨A,rfl,hA⟩
    exact (quotient_mem_normalizer_iff_upper A).mpr hA

/-- Equality of actual subgroups: the projective normalizer is the quotient
image of the literal determinant-one Borel, in every rank and field. -/
theorem projective_normalizer_eq_map_Borel :
    Subgroup.normalizer (projectiveUplus n F : Set (ProjectiveSpecialLinearGroup (Fin n) F)) =
      (Borel n F).map π := by
  ext g
  rw [mem_projective_normalizer_iff_upper]
  exact ⟨fun ⟨A,he,hA⟩ => Subgroup.mem_map.mpr ⟨A,hA,he⟩,
    fun h => by obtain ⟨A,hA,he⟩ := Subgroup.mem_map.mp h; exact ⟨A,he,hA⟩⟩

end NikolovSegal.PSLnNormalizer

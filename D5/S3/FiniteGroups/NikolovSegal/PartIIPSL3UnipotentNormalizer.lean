/- GID: D5/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/PartIIPSL3UnipotentNormalizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual PSL3 quotient geometry and corrected ordered product supply. -/

import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3UnipotentGeometry
import D5.S3.FiniteGroups.NikolovSegal.PartIISL3UnipotentNormalizer
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

/-! Actual PSL3 upper-unipotent normalizer/Borel recognition over every field.
Central discrepancies in conjugation are eliminated using native trace
conjugacy and scalar-center recognition, including characteristic three. -/
namespace NikolovSegal.PartIIPSL3UnipotentNormalizer
open NikolovSegal.PartIIA2Orbital NikolovSegal.PartIISL3UnipotentSylow
open NikolovSegal.PartIIPSL3Unipotent Matrix.SpecialLinearGroup
open scoped MatrixGroups
universe u
variable {F : Type u} [Field F]
local notation "π₃" => QuotientGroup.mk' (Subgroup.center SL(3,F))

private theorem trace_U3 (x : SL(3,F)) (hx : x ∈ U3) : Matrix.trace x.val = 3 := by
  obtain ⟨a,b,c,rfl⟩ := hx
  simp [Matrix.trace,Matrix.diag,upper3,Fin.sum_univ_succ]
  ring

private theorem scalar_one (z : F) (hz : z^3 = 1) (ht : (3:F)*z = 3) : z = 1 := by
  by_cases h3 : (3:F) = 0
  · have hi : (z-1)^3 = z^3-1-3*z*(z-1) := by ring
    have hn : (z-1)^3 = 0 := by rw [hi,hz,h3]; ring
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hn)
  · apply mul_left_cancel₀ h3
    simpa using ht

/-- Equality of actual projective conjugates of U3 elements lifts to actual
SL3 equality. The central scalar is forced to one by trace and determinant. -/
theorem conjugate_eq_of_quotient_eq (A x y : SL(3,F)) (hx : x ∈ U3) (hy : y ∈ U3)
    (hq : π₃ (A*x*A⁻¹) = π₃ y) : A*x*A⁻¹ = y := by
  let c := (A*x*A⁻¹)/y
  have hc : c ∈ Subgroup.center SL(3,F) := QuotientGroup.eq_iff_div_mem.mp hq
  obtain ⟨z,hz,hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hz3 : z^3 = 1 := by simpa using hz
  have hmult : A*x*A⁻¹ = c*y := by simp [c]
  have ht : Matrix.trace (A*x*A⁻¹).val = 3 :=
    (Matrix.trace_units_conj (toGL A) x.val).trans (trace_U3 x hx)
  have hty : Matrix.trace (A*x*A⁻¹).val = z*3 := by
    rw [hmult]
    change Matrix.trace (c.val*y.val) = z*3
    rw [← hsc,Matrix.scalar_apply,← Matrix.smul_eq_diagonal_mul,
      Matrix.trace_smul,trace_U3 y hy]
    rfl
  have hz1 : z = 1 := scalar_one z hz3 (by simpa [mul_comm] using hty.symm.trans ht)
  have hc1 : c = 1 := by
    apply Subtype.ext
    change c.val = (1 : Matrix (Fin 3) (Fin 3) F)
    rw [← hsc,hz1]
    simp
  simpa [hc1] using hmult

/-- Projective conjugation membership lifts on the actual upper-unipotent
carrier; no assumption about the conjugating matrix or its flag occurs. -/
theorem projective_conjugate_mem_iff (A x : SL(3,F)) (hx : x ∈ U3) :
    π₃ (A*x*A⁻¹) ∈ projectiveUpperUnipotent ↔ A*x*A⁻¹ ∈ U3 := by
  constructor
  · intro h
    obtain ⟨y,hy,hq⟩ := Subgroup.mem_map.mp h
    rw [conjugate_eq_of_quotient_eq A x y hx hy hq.symm]
    exact hy
  · intro h
    exact Subgroup.mem_map.mpr ⟨A*x*A⁻¹,h,rfl⟩

private theorem lift_normalizer_conjugate (A : SL(3,F))
    (hA : π₃ A ∈ Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)))
    (x : SL(3,F)) (hx : x ∈ U3) : A*x*A⁻¹ ∈ U3 := by
  apply (projective_conjugate_mem_iff A x hx).mp
  have hp : π₃ x ∈ projectiveUpperUnipotent := Subgroup.mem_map.mpr ⟨x,hx,rfl⟩
  have hc := (Subgroup.mem_normalizer_iff.mp hA (π₃ x)).mp hp
  simpa only [map_mul,map_inv] using hc

/-- Exact preimage recognition for the actual central quotient, every field. -/
theorem quotient_mem_normalizer_iff (A : SL(3,F)) :
    π₃ A ∈ Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) ↔
      A ∈ Subgroup.normalizer (U3 (F := F) : Set SL(3,F)) := by
  constructor
  · intro hA
    have hi : π₃ A⁻¹ ∈ Subgroup.normalizer
        (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) := by
      simpa only [map_inv] using
        (Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F))).inv_mem hA
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · exact lift_normalizer_conjugate A hA x
    · intro hx
      have h := lift_normalizer_conjugate A⁻¹ hi (A*x*A⁻¹) hx
      simpa [mul_assoc] using h
  · intro hA
    have hm : π₃ A ∈ (Subgroup.normalizer (U3 (F := F) : Set SL(3,F))).map π₃ :=
      Subgroup.mem_map.mpr ⟨A,hA,rfl⟩
    exact Subgroup.le_normalizer_map π₃ hm

/-- The actual projective Borel consists exactly of projective classes
admitting an actual upper-triangular determinant-one representative. -/
theorem mem_projective_normalizer_iff_upper (g : PSL(3,F)) :
    g ∈ Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) ↔
      ∃ A : SL(3,F), π₃ A = g ∧ ∀ i j : Fin 3, j < i → A i j = 0 := by
  constructor
  · intro hg
    obtain ⟨A,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) g
    exact ⟨A,rfl,(NikolovSegal.PartIISL3UnipotentNormalizer.mem_normalizer_iff_upper A).mp
      ((quotient_mem_normalizer_iff A).mp hg)⟩
  · rintro ⟨A,rfl,hA⟩
    exact (quotient_mem_normalizer_iff A).mpr
      ((NikolovSegal.PartIISL3UnipotentNormalizer.mem_normalizer_iff_upper A).mpr hA)

/-- Native normalizer functoriality for a bare projective automorphism which
preserves the actual projective U3. No SL3 automorphism lift is assumed. -/
theorem automorphism_projective_normalizer_map (beta : MulAut PSL(3,F))
    (hbeta : (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom = projectiveUpperUnipotent) :
    (Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F))).map
      beta.toMonoidHom = Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) := by
  rw [Subgroup.map_equiv_normalizer_eq,hbeta]

/-- The same bare automorphism preserves the literal upper-triangular
representative criterion in the actual quotient. -/
theorem automorphism_upper_representative_iff (beta : MulAut PSL(3,F))
    (hbeta : (projectiveUpperUnipotent (F := F)).map beta.toMonoidHom = projectiveUpperUnipotent)
    (g : PSL(3,F)) :
    (∃ A : SL(3,F), π₃ A = beta g ∧ ∀ i j : Fin 3, j < i → A i j = 0) ↔
      ∃ A : SL(3,F), π₃ A = g ∧ ∀ i j : Fin 3, j < i → A i j = 0 := by
  rw [← mem_projective_normalizer_iff_upper,← mem_projective_normalizer_iff_upper]
  have hm : beta g ∈ (Subgroup.normalizer
      (projectiveUpperUnipotent (F := F) : Set PSL(3,F))).map beta.toMonoidHom ↔
      g ∈ Subgroup.normalizer (projectiveUpperUnipotent (F := F) : Set PSL(3,F)) :=
    Subgroup.mem_map_iff_mem beta.injective
  rwa [automorphism_projective_normalizer_map beta hbeta] at hm

end NikolovSegal.PartIIPSL3UnipotentNormalizer

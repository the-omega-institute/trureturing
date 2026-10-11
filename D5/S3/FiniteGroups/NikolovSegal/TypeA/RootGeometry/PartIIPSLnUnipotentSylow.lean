/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnUnipotentSylow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnUnipotentSylow
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnUnipotentNormalizer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Actual arbitrary-rank projective Uplus Sylow recognition. The accepted
SLn Sylow is transported through the actual surjective center quotient by
native Sylow.mapSurjective; no projective group order is recomputed. -/
namespace NikolovSegal.PSLnSylow
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnSylow NikolovSegal.PSLnNormalizer
universe u
variable {F : Type u} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Native surjective Sylow transport through the literal SLn center quotient. -/
def projectiveUplusSylow (n : ℕ) : Sylow p (ProjectiveSpecialLinearGroup (Fin n) F) :=
  (UplusSylow (F := F) p n).mapSurjective
    (QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F)))

/-- The actual underlying subgroup is exactly the accepted projective Uplus. -/
theorem projectiveUplusSylow_toSubgroup (n : ℕ) :
    (projectiveUplusSylow (F := F) p n).toSubgroup = projectiveUplus n F := by
  change ((UplusSylow (F := F) p n).mapSurjective
    (QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin n) F))) :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) F)) = _
  rw [Sylow.coe_mapSurjective, UplusSylow_toSubgroup]
  rfl

/-- Every prime, finite field of characteristic p, and rank, without a cutoff. -/
theorem exists_projectiveUplus_sylow (n : ℕ) :
    ∃ P : Sylow p (ProjectiveSpecialLinearGroup (Fin n) F),
      P.toSubgroup = projectiveUplus n F :=
  ⟨projectiveUplusSylow p n, projectiveUplusSylow_toSubgroup p n⟩

/-- Literal membership recognition by actual unitriangular determinant-one
representatives, retaining the genuine quotient and both entry conditions. -/
theorem mem_projectiveUplusSylow_iff (n : ℕ) (g : ProjectiveSpecialLinearGroup (Fin n) F) :
    g ∈ projectiveUplusSylow (F := F) p n ↔
      ∃ A : SpecialLinearGroup (Fin n) F,
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)) A = g ∧
        (∀ r c : Fin n, c.val < r.val → A.val r c = 0) ∧
          ∀ r : Fin n, A.val r r = 1 := by
  change g ∈ (projectiveUplusSylow p n).toSubgroup ↔ _
  rw [projectiveUplusSylow_toSubgroup]
  constructor
  · intro hg
    obtain ⟨A,hA,he⟩ := Subgroup.mem_map.mp hg
    exact ⟨A,he,(mem_Uplus_iff A).mp hA⟩
  · rintro ⟨A,he,hA⟩
    exact Subgroup.mem_map.mpr ⟨A,(mem_Uplus_iff A).mpr hA,he⟩

end NikolovSegal.PSLnSylow

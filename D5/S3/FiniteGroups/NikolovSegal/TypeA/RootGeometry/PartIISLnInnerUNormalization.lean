/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnInnerUNormalization
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnInnerUNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnUnipotentSylow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! A pre-target inner correction preserves actual full U and Borel in SLn
and PSLn. Native Sylow conjugacy and normalizer functoriality are consumed;
the accepted carrier, Sylow and normalizer proofs remain unchanged. No
automorphism/root/field/graph classification is asserted. -/
namespace NikolovSegal.InnerUNormalization
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnSylow
open NikolovSegal.PSLnNormalizer NikolovSegal.PSLnSylow
universe u

-- Native finite Sylow conjugacy, with Q=alpha(P) conjugated BACK to P.
-- MulAut multiplication is composition: (conj c * alpha)(g)=c*alpha(g)*c^-1.
private theorem sylow_inner_correction {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (alpha : MulAut G) :
    ∃ c : G, let beta : MulAut G := (MulAut.conj c)*alpha
      P.toSubgroup.map beta.toMonoidHom = P.toSubgroup ∧
      (∀ g : G, beta g ∈ P.toSubgroup ↔ g ∈ P.toSubgroup) ∧
      (Subgroup.normalizer (P.toSubgroup : Set G)).map beta.toMonoidHom =
        Subgroup.normalizer (P.toSubgroup : Set G) ∧
      (∀ g : G, beta g ∈ Subgroup.normalizer (P.toSubgroup : Set G) ↔
        g ∈ Subgroup.normalizer (P.toSubgroup : Set G)) := by
  let Q := P.mapSurjective (f := alpha.toMonoidHom) alpha.surjective
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq G Q P
  let beta : MulAut G := (MulAut.conj c)*alpha
  have he := congrArg (fun R : Sylow p G => R.toSubgroup) hc
  change (P.toSubgroup.map alpha.toMonoidHom).map (MulAut.conj c).toMonoidHom =
    P.toSubgroup at he
  have hU : P.toSubgroup.map beta.toMonoidHom = P.toSubgroup := by
    change P.toSubgroup.map ((MulAut.conj c).toMonoidHom.comp alpha.toMonoidHom) = _
    rwa [← Subgroup.map_map]
  have hN : (Subgroup.normalizer (P.toSubgroup : Set G)).map beta.toMonoidHom =
      Subgroup.normalizer (P.toSubgroup : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq,hU]
  refine ⟨c,hU,?_,hN,?_⟩
  · intro g
    have hm := Subgroup.mem_map_iff_mem (f := beta.toMonoidHom)
      (K := P.toSubgroup) (x := g) beta.injective
    rwa [hU] at hm
  · intro g
    have hm := Subgroup.mem_map_iff_mem (f := beta.toMonoidHom)
      (K := Subgroup.normalizer (P.toSubgroup : Set G)) (x := g) beta.injective
    rwa [hN] at hm

variable {F : Type u} [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
include p

/-- Every bare SLn automorphism admits a genuine determinant-one inner
correction, chosen before all targets, preserving the actual full Uplus
and actual Borel, with exact subgroup maps and iff membership. -/
theorem sl_inner_U_Borel_correction (n : ℕ) (alpha : MulAut (SpecialLinearGroup (Fin n) F)) :
    ∃ c : SpecialLinearGroup (Fin n) F,
      let beta : MulAut (SpecialLinearGroup (Fin n) F) := (MulAut.conj c)*alpha
      (Uplus n F).map beta.toMonoidHom = Uplus n F ∧
      (∀ g : SpecialLinearGroup (Fin n) F, beta g ∈ Uplus n F ↔ g ∈ Uplus n F) ∧
      (Borel n F).map beta.toMonoidHom = Borel n F ∧
      (∀ g : SpecialLinearGroup (Fin n) F, beta g ∈ Borel n F ↔ g ∈ Borel n F) := by
  obtain ⟨c,hU,hUi,hB,hBi⟩ := sylow_inner_correction (UplusSylow (F := F) p n) alpha
  simp only [UplusSylow_toSubgroup,normalizer_eq_Borel] at hU hUi hB hBi
  exact ⟨c,hU,hUi,hB,hBi⟩

/-- Every bare PSLn automorphism admits a genuine projective inner correction
preserving the actual quotient Uplus and the quotient image of Borel.
No lift to SLn, classifying law, size bound or rank restriction is required. -/
theorem psl_inner_U_Borel_correction (n : ℕ) (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F,
      let beta : MulAut (ProjectiveSpecialLinearGroup (Fin n) F) := (MulAut.conj c)*alpha
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (∀ g : ProjectiveSpecialLinearGroup (Fin n) F,
        beta g ∈ projectiveUplus n F ↔ g ∈ projectiveUplus n F) ∧
      ((Borel n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))).map
        beta.toMonoidHom =
        (Borel n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))) ∧
      (∀ g : ProjectiveSpecialLinearGroup (Fin n) F,
        beta g ∈ (Borel n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))) ↔
          g ∈ (Borel n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))) := by
  obtain ⟨c,hU,hUi,hB,hBi⟩ := sylow_inner_correction (projectiveUplusSylow (F := F) p n) alpha
  simp only [projectiveUplusSylow_toSubgroup,projective_normalizer_eq_map_Borel] at hU hUi hB hBi
  exact ⟨c,hU,hUi,hB,hBi⟩

end NikolovSegal.InnerUNormalization

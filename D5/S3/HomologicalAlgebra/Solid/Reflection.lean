/- GID: D5/S3/HomologicalAlgebra/Solid/Reflection
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Reflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

/-
Copyright (c) 2024, 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import D5.S3.HomologicalAlgebra.Solid.Filtered

/- Selected proved declarations ported from LightSolid.lean and LightSolidInt.lean,
   dagurtomas/LeanCondensed@339ecc99fdc4bdb68ef248c16da0148dce61a639.
   This module uses the exact protected isSolid; it does not import upstream gaps. -/
noncomputable section
open CategoryTheory LightProfinite OnePoint Limits LightCondensed MonoidalCategory MonoidalClosed
namespace LightCondensed
namespace ReflectionProof
section InternalHomPoints

variable {R : Type} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- On `S`-points of internal Homs, precomposition by `f` is precomposition by
`f ▷ ℤ[S]` after applying `ihomPoints`. -/
lemma ihom_pre_val_app
    {A B X : LightCondMod R} (f : B ⟶ A)
    (S : LightProfinite)
    (x : ((ihom A).obj X).obj.obj ⟨S⟩) :
    (((MonoidalClosed.pre f).app X).hom.app ⟨S⟩) x =
      (ihomPoints R B X S).symm
        ((f ▷ (LightCondensed.free R).obj S.toCondensed) ≫ ihomPoints R A X S x) := by
  apply (ihomPoints R B X S).injective
  simp only [ihomPoints_apply, ← MonoidalClosed.uncurry_pre_app,
    ← Adjunction.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  congr
  apply (coherentTopology LightProfinite).yonedaEquiv.injective
  simp [dsimp% GrothendieckTopology.yonedaEquiv_comp]

lemma ihomPoints_pre_app
    {A B X : LightCondMod R} (f : B ⟶ A)
    (S : LightProfinite)
    (x : ((ihom A).obj X).obj.obj ⟨S⟩) :
    ihomPoints R B X S
      ((((MonoidalClosed.pre f).app X).hom.app ⟨S⟩) x)
      = (f ▷ (LightCondensed.free R).obj S.toCondensed) ≫ ihomPoints R A X S x := by
  rw [ihom_pre_val_app]
  simp

end InternalHomPoints


end ReflectionProof
namespace Solid
instance reflection_locallySmall : LocallySmall.{0} LightCondAb where
instance reflection_hasColimits : HasColimitsOfSize.{0, 0} LightCondAb := by
  dsimp [LightCondAb, LightCondMod, LightCondensed]
  exact hasColimitsOfSizeShrink.{0, 0, 1, 0} _
/-- A small family of maps whose local objects are the solid groups. -/
def solidGeneratingMaps : MorphismProperty LightCondAb :=
  .ofHoms (fun S : SmallModel.{0} LightProfinite ↦
    oneMinusShift ▷ (free ℤ).obj
      ((equivSmallModel LightProfinite).inverse.obj S).toCondensed)

set_option backward.isDefEq.respectTransparency false in
lemma isSolid_iff_isLocal (A : LightCondAb) :
    isSolid A ↔ solidGeneratingMaps.isLocal A := by
  rw [isSolid, ← isIso_iff_of_reflects_iso _ (equivSmall (ModuleCat ℤ)).functor,
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  have h (S : SmallModel.{0} LightProfinite) :
      IsIso ((((MonoidalClosed.pre (oneMinusShift)).app A).hom.app
        ⟨(equivSmallModel LightProfinite).inverse.obj S⟩)) ↔
      Function.Bijective (fun (g : P ⊗ (free ℤ).obj
          ((equivSmallModel LightProfinite).inverse.obj S).toCondensed ⟶ A) ↦
        (oneMinusShift ▷ _) ≫ g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := ihomPoints ℤ (P) A ((equivSmallModel LightProfinite).inverse.obj S)
    rw [← Function.Bijective.of_comp_iff _ e.bijective,
      ← Function.Bijective.of_comp_iff' e.bijective]
    apply Iff.of_eq
    congr 1
    funext x
    exact ReflectionProof.ihomPoints_pre_app (oneMinusShift) _ x
  constructor
  · intro hA X Y f hf
    cases hf with
    | mk S => exact (h S).1 (hA ⟨S⟩)
  · intro hA S
    exact (h S.unop).2 (hA _ (.mk S.unop))

/-- Orthogonal reflection applies because the generating maps have finitely presentable
domains and codomains. -/
instance reflection_rightAdjoint : isSolid.ι.IsRightAdjoint := by
  have := Cardinal.fact_isRegular_aleph0
  have : MorphismProperty.IsSmall.{0} solidGeneratingMaps :=
    inferInstanceAs (MorphismProperty.IsSmall (.ofHoms _))
  have hW : ∀ ⦃X Y : LightCondAb⦄ (f : X ⟶ Y), solidGeneratingMaps f →
      IsCardinalPresentable X Cardinal.aleph0 ∧
        IsCardinalPresentable Y Cardinal.aleph0 := by
    intro X Y f hf
    cases hf with
    | mk S =>
      have := LightSolidFilteredScaffold.preservesFilteredColimits_hom_P_tensor_free
        ((equivSmallModel LightProfinite).inverse.obj S)
      have h : IsCardinalPresentable
          (P ⊗ (free ℤ).obj
            ((equivSmallModel LightProfinite).inverse.obj S).toCondensed)
          Cardinal.aleph0 := {
        preservesColimitOfShape J _ _ := by
          have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
          infer_instance }
      exact ⟨h, h⟩
  have h := solidGeneratingMaps.isRightAdjoint_ι_isLocal Cardinal.aleph0 hW
  have heq : isSolid = solidGeneratingMaps.isLocal := by
    ext A
    exact isSolid_iff_isLocal A
  rw [heq]
  exact h

end Solid
end LightCondensed

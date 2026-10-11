/- GID: D5/S3/HomologicalAlgebra/Solid/ExactMates
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/ExactMates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
Compatibility of an exact adjunction and its mates with the unbounded
derived localization. New proofs, released under the Apache 2.0 license.
The localization constructions used here are Mathlib's proved constructions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits

namespace CWSolid

/-- The degreewise adjunction uses Mathlib's zero-preserving composition comparison. -/
private def exactMatesComplexAdjunction
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι) :
    F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := (Functor.mapHomologicalComplexIdIso C c).inv ≫
    adj.unit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).inv
  counit := (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F)) c).hom ≫
    adj.counit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexIdIso D c).hom
  left_triangle_components K := by
    ext i
    simpa [Functor.mapHomologicalComplexIdIso, Functor.mapHomologicalComplexCompIso,
      NatIso.mapHomologicalComplex, HomologicalComplex.Hom.isoOfComponents,
      Functor.mapHomologicalComplex] using adj.left_triangle_components (K.X i)
  right_triangle_components K := by
    ext i
    simpa [Functor.mapHomologicalComplexIdIso, Functor.mapHomologicalComplexCompIso,
      NatIso.mapHomologicalComplex, HomologicalComplex.Hom.isoOfComponents,
      Functor.mapHomologicalComplex] using adj.right_triangle_components (K.X i)


variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C}
  [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The existing localization-of-adjunction construction, applied directly
to the exact degreewise functors and the unbounded derived localizations. -/
def exactAdjunctionDerived (adj : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (exactMatesComplexAdjunction adj (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
private theorem exactAdjunctionDerived_unit_Q (adj : F ⊣ G)
    (K : CochainComplex C ℤ) :
    (exactAdjunctionDerived adj).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((exactMatesComplexAdjunction adj (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  unfold exactAdjunctionDerived
  apply Adjunction.localization_unit_app

set_option backward.isDefEq.respectTransparency false in
/-- A mate relation for an exact adjunction remains the same relation after
unbounded derived localization. This is proved from the actual localized
unit, rather than assumed as an additional adjunction compatibility. -/
theorem exactAdjunctionDerived_unit_mate (adj : F ⊣ G)
    (a : F ⟶ F) (b : G ⟶ G)
    (h : ∀ X, adj.unit.app X ≫ G.map (a.app X) =
      adj.unit.app X ≫ b.app (F.obj X)) (X : DerivedCategory C) :
    (exactAdjunctionDerived adj).unit.app X ≫ G.mapDerivedCategory.map (a.mapDerivedCategory.app X) =
      (exactAdjunctionDerived adj).unit.app X ≫ b.mapDerivedCategory.app (F.mapDerivedCategory.obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  suffices hK : (exactAdjunctionDerived adj).unit.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (a.mapDerivedCategory.app (DerivedCategory.Q.obj K)) =
        (exactAdjunctionDerived adj).unit.app (DerivedCategory.Q.obj K) ≫
          b.mapDerivedCategory.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) by
    have hn := (exactAdjunctionDerived adj).unit.naturality e.hom
    change e.hom ≫ (exactAdjunctionDerived adj).unit.app X =
      (exactAdjunctionDerived adj).unit.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategory.map e.hom) at hn
    rw [← cancel_epi e.hom]
    simp only [← Category.assoc, hn]
    rw [Category.assoc, ← G.mapDerivedCategory.map_comp,
      a.mapDerivedCategory.naturality, G.mapDerivedCategory.map_comp,
      ← Category.assoc, hK]
    simp only [Category.assoc]
    rw [b.mapDerivedCategory.naturality]
  have hC : (exactMatesComplexAdjunction adj (.up ℤ)).unit.app K ≫
      (G.mapHomologicalComplex (.up ℤ)).map ((a.mapHomologicalComplex (.up ℤ)).app K) =
        (exactMatesComplexAdjunction adj (.up ℤ)).unit.app K ≫
          (b.mapHomologicalComplex (.up ℤ)).app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext n
    simpa [exactMatesComplexAdjunction, Functor.mapHomologicalComplexIdIso,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex, HomologicalComplex.Hom.isoOfComponents,
      Functor.mapHomologicalComplex] using h (K.X n)
  have ha : G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) ≫
      G.mapDerivedCategory.map (a.mapDerivedCategory.app (DerivedCategory.Q.obj K)) =
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          ((a.mapHomologicalComplex (.up ℤ)).app K)) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    rw [← Functor.map_comp, NatTrans.mapDerivedCategory_app_Q_obj]
    simp only [Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have hnG := G.mapDerivedCategoryFactors.inv.naturality
    ((a.mapHomologicalComplex (.up ℤ)).app K)
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).app K)) ≫
      G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      G.mapDerivedCategory.map (DerivedCategory.Q.map
        ((a.mapHomologicalComplex (.up ℤ)).app K)) at hnG
  have hb := b.mapDerivedCategory.naturality (F.mapDerivedCategoryFactors.inv.app K)
  dsimp only [Functor.comp_obj] at hb
  have hbQ : G.mapDerivedCategoryFactors.inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        b.mapDerivedCategory.app (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) =
    DerivedCategory.Q.map ((b.mapHomologicalComplex (.up ℤ)).app
      ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
    rw [NatTrans.mapDerivedCategory_app_Q_obj]
    simp only [Iso.inv_hom_id_app_assoc]
  rw [exactAdjunctionDerived_unit_Q]
  simp only [Category.assoc]
  rw [ha, ← reassoc_of% hnG, hb, reassoc_of% hbQ]
  simp only [← Category.assoc, ← DerivedCategory.Q.map_comp, hC]

set_option backward.isDefEq.respectTransparency false in
/-- Under the localized exact adjunction, precomposition by the left mate
is postcomposition by the right mate. All derived objects are unbounded. -/
theorem exactAdjunctionDerived_homEquiv_mate (adj : F ⊣ G)
    (a : F ⟶ F) (b : G ⟶ G)
    (h : ∀ X, adj.unit.app X ≫ G.map (a.app X) =
      adj.unit.app X ≫ b.app (F.obj X))
    (X : DerivedCategory C) (Y : DerivedCategory D)
    (f : F.mapDerivedCategory.obj X ⟶ Y) :
    (exactAdjunctionDerived adj).homEquiv X Y (a.mapDerivedCategory.app X ≫ f) =
      (exactAdjunctionDerived adj).homEquiv X Y f ≫ b.mapDerivedCategory.app Y := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [exactAdjunctionDerived_unit_mate adj a b h, Category.assoc,
    ← b.mapDerivedCategory.naturality]
  simp only [Category.assoc]

end CWSolid

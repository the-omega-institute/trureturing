/- GID: D5/S3/HomologicalAlgebra/Solid/Supplier/FreeAugmentation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/Supplier/FreeAugmentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in src/licenses/LICENSE.LeanCondensed.
-/
import D5.S3.HomologicalAlgebra.Solid.Early
import D5.S3.HomologicalAlgebra.Solid.DiscreteInt
import Mathlib.Condensed.Discrete.LocallyConstant
import Mathlib.AlgebraicTopology.TopologicalSimplex

noncomputable section
open CategoryTheory Limits LightCondensed
open scoped Simplicial

namespace CWComparison

/-- Free discrete sets and discrete free modules agree by the actual adjunctions. -/
def discreteFreeNatIso :
    LightCondensed.discrete (Type) ⋙ free ℤ ≅
      ModuleCat.free ℤ ⋙ LightCondensed.discrete (ModuleCat ℤ) :=
  ((LightCondensed.discreteUnderlyingAdj (Type)).comp (freeForgetAdjunction ℤ)).leftAdjointUniq
    ((ModuleCat.adj ℤ).comp (LightCondensed.discreteUnderlyingAdj (ModuleCat ℤ)))

/-- The point used for the free-object augmentation. -/
abbrev point : TopCat := TopCat.of PUnit

/-- The protected free condensed group on the point is the discrete integral group. -/
def freePointIsoInt :
    LightCondensed.Solid.freeLightCondAbOfTopFunctor.obj point ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) := by
  let e : LightCondSet.LocallyConstant.functor ≅
      TopCat.discrete ⋙ topCatToLightCondSet :=
    CompHausLike.LocallyConstant.functorIso _ _
  exact (free ℤ).mapIso ((e.app PUnit).symm ≪≫
      LightCondSet.LocallyConstant.iso.app PUnit) ≪≫
    discreteFreeNatIso.app PUnit ≪≫
    (LightCondensed.discrete (ModuleCat ℤ)).mapIso
      (Functor.Monoidal.εIso (ModuleCat.free ℤ)).symm

/-- Collapse to the point, natural in every topological space. -/
def collapse : 𝟭 TopCat ⟶ (Functor.const TopCat).obj point where
  app X := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  naturality _ _ _ := by
    ext
    rfl

/-- The genuine natural augmentation on the exact protected free functor. -/
def freeAugmentation :
    LightCondensed.Solid.freeLightCondAbOfTopFunctor ⟶
      (Functor.const TopCat).obj ((LightCondensed.discrete (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)) where
  app X := LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (collapse.app X) ≫
    freePointIsoInt.hom
  naturality X Y f := by
    change LightCondensed.Solid.freeLightCondAbOfTopFunctor.map f ≫
      (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (collapse.app Y) ≫
        freePointIsoInt.hom) = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← Functor.map_comp]
    have h : f ≫ collapse.app Y = collapse.app X := by
      ext
      rfl
    rw [h]

/-- A chosen point genuinely splits collapse. -/
def collapseSplit (X : TopCat) (x : X) : SplitEpi (collapse.app X) where
  section_ := TopCat.ofHom (X := point) (Y := X) ⟨fun _ => x, continuous_const⟩
  id := by
    ext p
    cases p
    rfl

/-- A chosen point gives an objectwise section; no simplicial naturality is asserted. -/
def freeAugmentationSection (X : TopCat) (x : X) :
    (LightCondensed.discrete (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⟶
      LightCondensed.Solid.freeLightCondAbOfTopFunctor.obj X :=
  freePointIsoInt.inv ≫ LightCondensed.Solid.freeLightCondAbOfTopFunctor.map
    (collapseSplit X x).section_

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem freeAugmentationSection_comp (X : TopCat) (x : X) :
    freeAugmentationSection X x ≫ freeAugmentation.app X = 𝟙 _ := by
  change (freePointIsoInt.inv ≫
    LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (collapseSplit X x).section_) ≫
    (LightCondensed.Solid.freeLightCondAbOfTopFunctor.map (collapse.app X) ≫
      freePointIsoInt.hom) = 𝟙 _
  rw [Category.assoc, ← Functor.map_comp_assoc]
  rw [(collapseSplit X x).id]
  have hid := LightCondensed.Solid.freeLightCondAbOfTopFunctor.map_id
    (((Functor.const TopCat).obj point).obj X)
  rw [hid]
  change freePointIsoInt.inv ≫ (𝟙 _ ≫ freePointIsoInt.hom) = 𝟙 _
  rw [Category.id_comp, Iso.inv_hom_id]

/-- The cosimplicial free topological simplices, without changing their topology. -/
abbrev freeSimplexFunctor : SimplexCategory ⥤ LightCondAb :=
  SimplexCategory.toTop ⋙ LightCondensed.Solid.freeLightCondAbOfTopFunctor

/-- Augmentation of all standard topological simplices, natural under every simplex map. -/
def freeSimplexAugmentation : freeSimplexFunctor ⟶
    (Functor.const SimplexCategory).obj ((LightCondensed.discrete (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)) :=
  Functor.whiskerLeft SimplexCategory.toTop freeAugmentation

/-- Every free-simplex augmentation is genuinely split epimorphic. -/
def freeSimplexAugmentationSplit (n : SimplexCategory) :
    SplitEpi (freeSimplexAugmentation.app n) where
  section_ := freeAugmentationSection _ (Classical.arbitrary _)
  id := freeAugmentationSection_comp _ _

end CWComparison

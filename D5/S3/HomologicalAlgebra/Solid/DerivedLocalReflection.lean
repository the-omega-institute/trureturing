/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedLocalReflection
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedLocalReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.TelescopeEquivalence
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! A genuine reflector on the actual unbounded derived category onto its
full subcategory of protected derived-local objects. This subcategory has
not been identified with DerivedCategory Solid. In particular this file
does not declare the protected total-left-derived functor.
New proofs, released under the Apache 2.0 license. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace LightCondensed.Solid

/-- Locality in the actual derived category, using the protected defining map. -/
def solidDerivedLocal : ObjectProperty DLightCondAb :=
  fun X => IsIso (solidDerivedEndomorphism.app X)

/-- The constructed local replacement of each derived object. -/
def solidDerivedLocalObj (X : DLightCondAb) : solidDerivedLocal.FullSubcategory :=
  ⟨DerivedCategory.Q.obj (solidCellularTelescope (DerivedCategory.Q.objPreimage X)),
    (isIso_solidDerivedEndomorphism_Q_iff _).2
      (solidCellularTelescope_homology_solid _)⟩

/-- Its actual comparison from the original arbitrary derived object. -/
def solidDerivedLocalι (X : DLightCondAb) : X ⟶ (solidDerivedLocalObj X).obj :=
  (DerivedCategory.Q.objObjPreimageIso X).inv ≫
    DerivedCategory.Q.map (solidCellularTelescopeι (DerivedCategory.Q.objPreimage X))

/-- The universal comparison includes every morphism in the actual localization. -/
def solidDerivedLocalHomEquiv (X : DLightCondAb) (Y : solidDerivedLocal.FullSubcategory) :
    (solidDerivedLocalObj X ⟶ Y) ≃ (X ⟶ Y.obj) := by
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  let h := solidCellularTelescope_derivedPrecomp_bijective
    (DerivedCategory.Q.objPreimage X) Y.obj
  apply Equiv.ofBijective (fun g => solidDerivedLocalι X ≫ solidDerivedLocal.ι.map g)
  constructor
  · intro f g hfg
    apply solidDerivedLocal.ι.map_injective
    apply h.injective
    exact (cancel_epi (DerivedCategory.Q.objObjPreimageIso X).inv).1
      (by simpa only [solidDerivedLocalι, Category.assoc] using hfg)
  · intro f
    obtain ⟨g, hg⟩ := h.surjective ((DerivedCategory.Q.objObjPreimageIso X).hom ≫ f)
    refine ⟨ObjectProperty.homMk g, ?_⟩
    change solidDerivedLocalι X ≫ g = f
    have hh := congrArg ((DerivedCategory.Q.objObjPreimageIso X).inv ≫ ·) hg
    simpa only [solidDerivedLocalι, Category.assoc] using
      hh.trans ((DerivedCategory.Q.objObjPreimageIso X).inv_hom_id_assoc f)

theorem solidDerivedLocalHomEquiv_naturality
    (X : DLightCondAb) (Y Y' : solidDerivedLocal.FullSubcategory)
    (g : Y ⟶ Y') (h : solidDerivedLocalObj X ⟶ Y) :
    solidDerivedLocalHomEquiv X Y' (h ≫ g) =
      solidDerivedLocalHomEquiv X Y h ≫ solidDerivedLocal.ι.map g := by
  change solidDerivedLocalι X ≫ solidDerivedLocal.ι.map (h ≫ g) = _
  rw [Functor.map_comp, ← Category.assoc]
  rfl

/-- The telescope universal property constructs a natural functor on all
derived objects and all roofs. This is a reflector into the full local
subcategory; no derivability or projective-replacement assumption is used. -/
def solidDerivedLocalReflection : DLightCondAb ⥤ solidDerivedLocal.FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (G := solidDerivedLocal.ι)
    solidDerivedLocalHomEquiv solidDerivedLocalHomEquiv_naturality

/-- The actual derived-local reflection adjunction. Its right adjoint is
the full local-subcategory inclusion, not the protected derived inclusion. -/
def solidDerivedLocalReflectionAdjunction :
    solidDerivedLocalReflection ⊣ solidDerivedLocal.ι :=
  Adjunction.adjunctionOfEquivLeft (G := solidDerivedLocal.ι)
    solidDerivedLocalHomEquiv solidDerivedLocalHomEquiv_naturality

/-- The adjunction unit is the saved telescope comparison. -/
theorem solidDerivedLocalReflection_unit_app (X : DLightCondAb) :
    solidDerivedLocalReflectionAdjunction.unit.app X = solidDerivedLocalι X := by
  change solidDerivedLocalι X ≫ solidDerivedLocal.ι.map (𝟙 (solidDerivedLocalObj X)) = _
  simp

/-- The protected exact derived inclusion genuinely factors through this
local subcategory. This does not assert its full faithfulness or essential
surjectivity onto that subcategory. -/
def derivedInclusionToLocal : DSolid ⥤ solidDerivedLocal.FullSubcategory :=
  solidDerivedLocal.lift derivedInclusion
    solidDerivedEndomorphism_derivedInclusion_isIso

/-- The factorization preserves the exact original derived inclusion. -/
def derivedInclusionToLocalCompIso :
    derivedInclusionToLocal ⋙ solidDerivedLocal.ι ≅ derivedInclusion := Iso.refl _

local instance ordinaryReflectorAdditive : isSolid.ι.leftAdjoint.Additive :=
  (Adjunction.ofIsRightAdjoint isSolid.ι).left_adjoint_additive

/-- The genuine ordinary degreewise solidification, viewed in the full
local derived subcategory through the exact protected inclusion. -/
def degreewiseSolidificationToLocal :
    CochainComplex LightCondAb ℤ ⥤ solidDerivedLocal.FullSubcategory :=
  isSolid.ι.leftAdjoint.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⋙ derivedInclusionToLocal

/-- The original degreewise adjunction unit followed by the official
derived-category factorization of the exact inclusion. -/
def degreewiseSolidificationDerivedUnit :
    (DerivedCategory.Q (C := LightCondAb)) ⟶
      degreewiseSolidificationToLocal ⋙ solidDerivedLocal.ι where
  app K :=
    DerivedCategory.Q.map
      ((CWSolid.mapHomologicalComplexAdjunction
        (Adjunction.ofIsRightAdjoint isSolid.ι) (.up ℤ)).unit.app K) ≫
      (isSolid.ι.mapDerivedCategoryFactors.app
        ((isSolid.ι.leftAdjoint.mapHomologicalComplex (.up ℤ)).obj K)).inv
  naturality K L f := by
    let F := isSolid.ι.leftAdjoint.mapHomologicalComplex (.up ℤ)
    let adj := CWSolid.mapHomologicalComplexAdjunction
      (Adjunction.ofIsRightAdjoint isSolid.ι) (.up ℤ)
    change DerivedCategory.Q.map f ≫ (DerivedCategory.Q.map (adj.unit.app L) ≫
      (isSolid.ι.mapDerivedCategoryFactors.app (F.obj L)).inv) =
        (DerivedCategory.Q.map (adj.unit.app K) ≫
          (isSolid.ι.mapDerivedCategoryFactors.app (F.obj K)).inv) ≫
            derivedInclusion.map (DerivedCategory.Q.map (F.map f))
    have hunit : f ≫ adj.unit.app L = adj.unit.app K ≫
        (isSolid.ι.mapHomologicalComplex (.up ℤ)).map (F.map f) := by
      simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality f
    rw [← DerivedCategory.Q.map_comp_assoc, hunit,
      DerivedCategory.Q.map_comp, Category.assoc, Category.assoc]
    exact congrArg (DerivedCategory.Q.map (adj.unit.app K) ≫ ·)
      (isSolid.ι.mapDerivedCategoryFactors.inv.naturality (F.map f))

/-- The actual natural comparison from the constructed derived-local
reflector into the image of ordinary degreewise solidification. This
lives in the full local derived category; lifting it to D(Solid) is the
remaining realization boundary, not an assumed property of this map. -/
def solidDerivedLocalDegreewiseComparison :
    DerivedCategory.Q ⋙ solidDerivedLocalReflection ⟶ degreewiseSolidificationToLocal :=
  ((solidDerivedLocalReflectionAdjunction.whiskerRight
      (CochainComplex LightCondAb ℤ)).homEquiv _ _).symm
    degreewiseSolidificationDerivedUnit

/-- The natural comparison factors the exact original degreewise unit. -/
theorem solidDerivedLocalDegreewiseComparison_unit
    (K : CochainComplex LightCondAb ℤ) :
    solidDerivedLocalReflectionAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
      solidDerivedLocal.ι.map (solidDerivedLocalDegreewiseComparison.app K) =
        degreewiseSolidificationDerivedUnit.app K := by
  let adj := solidDerivedLocalReflectionAdjunction.whiskerRight
    (CochainComplex LightCondAb ℤ)
  have h := (adj.homEquiv (DerivedCategory.Q (C := LightCondAb))
    degreewiseSolidificationToLocal).apply_symm_apply degreewiseSolidificationDerivedUnit
  rw [Adjunction.homEquiv_unit] at h
  simpa [adj, solidDerivedLocalDegreewiseComparison] using congrArg (fun t => t.app K) h

/-- The actual cellular colimit, not only the telescope, has the full
derived universal comparison against all protected derived-local targets. -/
theorem solidCellularColimit_derivedPrecomp_bijective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (solidCellularColimit K) ⟶ Y) =>
      DerivedCategory.Q.map (colimit.ι (solidCellularDiagram K) 0) ≫ g) := by
  haveI := solidCellularTelescopeToColimit_quasiIso K
  let c := DerivedCategory.Q.map (solidCellularTelescopeToColimit K)
  haveI : IsIso c := inferInstance
  have hc : Function.Bijective (fun g : DerivedCategory.Q.obj (solidCellularColimit K) ⟶ Y =>
      c ≫ g) := by simpa [Iso.homCongr] using
        (Iso.homCongr (asIso c).symm (Iso.refl Y)).bijective
  have h := (solidCellularTelescope_derivedPrecomp_bijective K Y).comp hc
  have heq : DerivedCategory.Q.map (solidCellularTelescopeι K) ≫ c =
      DerivedCategory.Q.map (colimit.ι (solidCellularDiagram K) 0) := by
    rw [← DerivedCategory.Q.map_comp, solidCellularTelescopeToColimit_input]
  simpa only [Function.comp_def, ← Category.assoc, heq] using h

end LightCondensed.Solid

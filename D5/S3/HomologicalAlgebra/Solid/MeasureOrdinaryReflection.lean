/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureOrdinaryReflection
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureOrdinaryReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.MeasureComparisonConstruction
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
Compatibility of the actual canonical P-measure computation with the
protected ordinary reflection unit. This does not assert DSolid realization,
derived full faithfulness or the existence of an unbounded derived adjunction.
New proofs, Apache-2.0; the generator route follows Rodriguez Camargo,
Notes on Solid Geometry, Theorem 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits

namespace LightCondensed.Solid

-- The canonical unit identity is already proved in MeasureFactorization.

def solidMeasureTargetLocal (B : Solid) : solidDerivedLocal.FullSubcategory :=
  ⟨(DerivedCategory.singleFunctor LightCondAb 0).obj (isSolid.ι.obj B), by
    apply (isIso_solidDerivedEndomorphism_Q_iff _).2
    intro n
    by_cases hn : n = 0
    · subst n
      exact isSolid.prop_of_iso
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (isSolid.ι.obj B)).symm
        B.property
    · exact isSolid.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 (isSolid.ι.obj B) n hn)⟩

/-- The canonical measure arrow, rather than an abstract isomorphic arrow,
is universal against every solid stalk in the actual localization. -/
theorem PToIntegerMeasures_derivedPrecomp_bijective (B : Solid) :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures ⟶
        (DerivedCategory.singleFunctor LightCondAb 0).obj (isSolid.ι.obj B) =>
      (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g) := by
  haveI := localPToIntegerMeasures_isIso
  let X := (DerivedCategory.singleFunctor LightCondAb 0).obj P
  let Y := solidMeasureTargetLocal B
  let j := solidDerivedLocal.ι
  let e : (integerMeasuresDerivedLocal.obj ⟶ Y.obj) ≃ (X ⟶ Y.obj) :=
    (Functor.FullyFaithful.ofFullyFaithful j).homEquiv.symm.trans
    (((asIso localPToIntegerMeasures).symm.homCongr (Iso.refl Y)).trans
      (solidDerivedLocalReflectionAdjunction.homEquiv X Y))
  have heq : (fun g : integerMeasuresDerivedLocal.obj ⟶ Y.obj =>
      (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g) =
      (fun g => e g) := by
    funext g
    change _ = solidDerivedLocalReflectionAdjunction.unit.app X ≫
      j.map (localPToIntegerMeasures ≫ j.preimage
        (X := integerMeasuresDerivedLocal) (Y := Y) g ≫ 𝟙 Y)
    simp only [Functor.map_comp, Category.comp_id, ← Category.assoc]
    rw [localPToIntegerMeasures_unit, Functor.map_preimage]
  change Function.Bijective (fun g : integerMeasuresDerivedLocal.obj ⟶ Y.obj =>
    (DerivedCategory.singleFunctor LightCondAb 0).map PToIntegerMeasures ≫ g)
  rw [heq]
  exact e.bijective

/-- The degree-zero comparison is genuinely the ordinary universal arrow. -/
theorem PToIntegerMeasures_precomp_bijective (B : Solid) :
    Function.Bijective (fun g : integerMeasures ⟶ isSolid.ι.obj B =>
      PToIntegerMeasures ≫ g) := by
  let F := DerivedCategory.singleFunctor LightCondAb 0
  have h := PToIntegerMeasures_derivedPrecomp_bijective B
  constructor
  · intro f g hfg
    apply F.map_injective
    apply h.injective
    change F.map PToIntegerMeasures ≫ F.map f = F.map PToIntegerMeasures ≫ F.map g
    simpa only [Functor.map_comp] using congrArg F.map hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective (F.map f)
    refine ⟨F.preimage g, F.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage]
    exact hg

def integerMeasuresSolid : Solid := ⟨integerMeasures, integerMeasures_solid⟩

/-- The actual map obtained from the original protected adjunction unit. -/
def solidPToIntegerMeasures : solidification.obj P ⟶ integerMeasuresSolid :=
  (solidificationAdjunction.homEquiv P integerMeasuresSolid).symm PToIntegerMeasures

theorem solidPToIntegerMeasures_unit :
    solidificationAdjunction.unit.app P ≫ isSolid.ι.map solidPToIntegerMeasures =
      PToIntegerMeasures :=
  (solidificationAdjunction.homEquiv P integerMeasuresSolid).apply_symm_apply _

theorem solidPToIntegerMeasures_isIso : IsIso solidPToIntegerMeasures := by
  apply isIso_of_coyoneda_map_bijective
  intro B
  let e := solidificationAdjunction.homEquiv P B
  let eM := (Functor.FullyFaithful.ofFullyFaithful isSolid.ι).homEquiv
    (X := integerMeasuresSolid) (Y := B)
  have heq : (fun g : integerMeasuresSolid ⟶ B => solidPToIntegerMeasures ≫ g) =
      (fun g => e.symm (PToIntegerMeasures ≫ eM g)) := by
    funext g
    apply e.injective
    rw [Equiv.apply_symm_apply]
    have h := solidificationAdjunction.homEquiv_naturality_right solidPToIntegerMeasures g
    exact h.trans (congrArg (· ≫ isSolid.ι.map g)
      ((solidificationAdjunction.homEquiv P integerMeasuresSolid).apply_symm_apply
        PToIntegerMeasures))
  change Function.Bijective (fun g : integerMeasuresSolid ⟶ B =>
    solidPToIntegerMeasures ≫ g)
  rw [heq]
  exact e.symm.bijective.comp ((PToIntegerMeasures_precomp_bijective B).comp eM.bijective)

def solidPIntegerMeasuresIso : solidification.obj P ≅ integerMeasuresSolid := by
  haveI := solidPToIntegerMeasures_isIso
  exact asIso solidPToIntegerMeasures

end LightCondensed.Solid

/- Fresh complete public-root audit of the actual ordinary comparison. -/
#print axioms LightCondensed.Solid.solidMeasureTargetLocal
#print axioms LightCondensed.Solid.PToIntegerMeasures_derivedPrecomp_bijective
#print axioms LightCondensed.Solid.PToIntegerMeasures_precomp_bijective
#print axioms LightCondensed.Solid.integerMeasuresSolid
#print axioms LightCondensed.Solid.solidPToIntegerMeasures
#print axioms LightCondensed.Solid.solidPToIntegerMeasures_unit
#print axioms LightCondensed.Solid.solidPToIntegerMeasures_isIso
#print axioms LightCondensed.Solid.solidPIntegerMeasuresIso

/- GID: D5/S3/HomologicalAlgebra/Solid/AdjunctionKanExtension
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/AdjunctionKanExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Reflection
import D5.S3.HomologicalAlgebra.Solid.ComplexAdjunction

/-!
# The total left derived universal property from the actual derived adjunction

The only additional premise is an actual adjunction to the protected exact
derived inclusion. The geometric construction of that adjunction is separate.
All complexes here are unbounded cochain complexes, and the localization is
at every quasi-isomorphism.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory

namespace LightCondensed.Solid

/-- The genuine ordinary reflector supplied by the frozen reflection proof. -/
abbrev kanSolidification : LightCondAb ⥤ Solid := isSolid.ι.leftAdjoint

instance kanSolidification_additive : kanSolidification.Additive :=
  (Adjunction.ofIsRightAdjoint isSolid.ι).left_adjoint_additive

/-- The ordinary adjunction applied in every integer degree. -/
def kanComplexAdjunction :
    kanSolidification.mapHomologicalComplex (.up ℤ) ⊣
      isSolid.ι.mapHomologicalComplex (.up ℤ) :=
  CWSolid.mapHomologicalComplexAdjunction
    (Adjunction.ofIsRightAdjoint isSolid.ι) (.up ℤ)

variable {L : DLightCondAb ⥤ DSolid} (derivedAdj : L ⊣ derivedInclusion)

/-- The explicit comparison: ordinary unit, actual inclusion factorization,
then the counit of the given derived adjunction. -/
def adjunctionDerivedCounit :
    DerivedCategory.Q ⋙ L ⟶
      kanSolidification.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight kanComplexAdjunction.unit (DerivedCategory.Q ⋙ L) ≫
    Functor.whiskerLeft (kanSolidification.mapHomologicalComplex (.up ℤ))
      (Functor.whiskerRight isSolid.ι.mapDerivedCategoryFactors.inv L) ≫
    Functor.whiskerLeft
      (kanSolidification.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      derivedAdj.counit

@[simp]
lemma adjunctionDerivedCounit_app (K : CochainComplex LightCondAb ℤ) :
    (adjunctionDerivedCounit derivedAdj).app K =
      L.map (DerivedCategory.Q.map (kanComplexAdjunction.unit.app K)) ≫
      L.map (isSolid.ι.mapDerivedCategoryFactors.inv.app
        ((kanSolidification.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      derivedAdj.counit.app
        (DerivedCategory.Q.obj
          ((kanSolidification.mapHomologicalComplex (.up ℤ)).obj K)) := rfl

/-- The three concrete Hom bijections: derived mate, fully faithful
precomposition by `Q` on the solid side, and ordinary degreewise mate. -/
def adjunctionKanHomEquiv (H : DLightCondAb ⥤ DSolid) :
    (H ⟶ L) ≃
      (DerivedCategory.Q ⋙ H ⟶
        kanSolidification.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :=
  (((derivedAdj.whiskerLeft DSolid).homEquiv H (𝟭 DSolid)).symm.trans
    (Localization.fullyFaithfulWhiskeringLeft
      (DerivedCategory.Q : CochainComplex Solid ℤ ⥤ DSolid)
      (HomologicalComplex.quasiIso Solid (.up ℤ)) DSolid).homEquiv).trans
    ((Iso.homCongr
      (Functor.isoWhiskerRight isSolid.ι.mapDerivedCategoryFactors H)
      (Iso.refl DerivedCategory.Q)).trans
      ((kanComplexAdjunction.whiskerLeft DSolid).homEquiv
        (DerivedCategory.Q ⋙ H) DerivedCategory.Q))

set_option backward.isDefEq.respectTransparency false in
/-- The Hom bijection is literally composition with the explicit comparison. -/
lemma adjunctionKanHomEquiv_apply (H : DLightCondAb ⥤ DSolid) (γ : H ⟶ L) :
    adjunctionKanHomEquiv derivedAdj H γ =
      Functor.whiskerLeft DerivedCategory.Q γ ≫ adjunctionDerivedCounit derivedAdj := by
  ext K
  dsimp [adjunctionKanHomEquiv, Adjunction.homEquiv, Adjunction.whiskerLeft,
    Functor.FullyFaithful.homEquiv, Iso.homCongr, adjunctionDerivedCounit]
  simp only [Category.id_comp, Category.comp_id]
  rw [γ.naturality_assoc, γ.naturality_assoc]

/-- The exact unbounded right Kan extension, with no assumed derivability. -/
theorem adjunction_isRightKanExtension :
    L.IsRightKanExtension (adjunctionDerivedCounit derivedAdj) := by
  refine ⟨⟨CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun E => CostructuredArrow.homMk
      ((adjunctionKanHomEquiv derivedAdj E.left).symm E.hom) ?_) ?_⟩⟩
  · change Functor.whiskerLeft DerivedCategory.Q
        ((adjunctionKanHomEquiv derivedAdj E.left).symm E.hom) ≫
        adjunctionDerivedCounit derivedAdj = E.hom
    rw [← adjunctionKanHomEquiv_apply]
    exact (adjunctionKanHomEquiv derivedAdj E.left).apply_symm_apply E.hom
  · intro E m
    apply CostructuredArrow.hom_ext
    apply (adjunctionKanHomEquiv derivedAdj E.left).injective
    change adjunctionKanHomEquiv derivedAdj E.left m.left =
      adjunctionKanHomEquiv derivedAdj E.left
        ((adjunctionKanHomEquiv derivedAdj E.left).symm E.hom)
    erw [Equiv.apply_symm_apply, adjunctionKanHomEquiv_apply]
    exact CostructuredArrow.w m

/-- The literal Mathlib property for all quasi-isomorphisms of unbounded complexes. -/
theorem adjunction_isLeftDerivedFunctor :
    L.IsLeftDerivedFunctor (adjunctionDerivedCounit derivedAdj)
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ)) :=
  ⟨adjunction_isRightKanExtension derivedAdj⟩

include derivedAdj in
/-- Existence obtained from the constructed witness using Mathlib's `mk'`. -/
theorem adjunction_hasLeftDerivedFunctor :
    (kanSolidification.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso LightCondAb (.up ℤ)) := by
  have := adjunction_isLeftDerivedFunctor derivedAdj
  exact Functor.HasLeftDerivedFunctor.mk' (LF := L)
    (α := adjunctionDerivedCounit derivedAdj)

end LightCondensed.Solid

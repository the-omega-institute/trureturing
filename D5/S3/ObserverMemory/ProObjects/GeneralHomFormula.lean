/- GID: D5/S3/ObserverMemory/ProObjects/GeneralHomFormula
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ProObjects/GeneralHomFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Morphisms between presented pro-objects form a limit of stage-map colimits. -/

import D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/- Library-search audit trail (2026-09-01):
   * The target atom has no formalization receipt and remains in `residual-open`.
     Repository searches found the adjacent `FiniteStageReadout` and
     `ConceptAnchorHomAsymmetry`; the former proves stage representability for
     a constant target, while the latter computes Hom when either endpoint is
     constant. Neither states the general two-diagram formula below.
   * Pinned Mathlib has no declared `CategoryTheory.Pro` or `ProCategory`.
     The existing local module therefore supplies the canonical definition
     `Pro(C) = (Ind(Cᵒᵖ))ᵒᵖ`, rather than introducing a second pro-category.
   * Exact Mathlib hits `Ind.limCompInclusion`,
     `Ind.inclusion.fullyFaithful`, and `colimitYonedaHomEquiv` compute the
     general Hom type. `preservesColimitIso` identifies each value with the
     corresponding stage-map colimit; `Types.jointly_surjective'` and
     `limit.w_apply` give stage representatives and their compatibility.
   * Searches across the remaining pinned Lean packages found no packaged
     pro-category Hom equivalence to import. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.ProObjects.GeneralHomFormula

open CategoryTheory CategoryTheory.Limits Opposite Functor
open D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry

universe u v

/-- The functor whose value at `target` is canonically the filtered colimit
of the types `X_i ⟶ target`. Using the Ind inclusion makes functoriality in
the target part of the construction rather than an additional assertion. -/
noncomputable def stageColimitFunctor
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (X : Iᵒᵖ ⥤ C) : Cᵒᵖᵒᵖ ⥤ Type v :=
  (Ind.inclusion Cᵒᵖ).obj ((Ind.lim I).obj X.rightOp)

/-- Pointwise, `stageColimitFunctor X` is the stated colimit of ordinary Hom
types. -/
noncomputable def stageColimitEquiv
    {C : Type u} [Category.{v} C]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (X : Iᵒᵖ ⥤ C) (target : C) :
    (stageColimitFunctor X).obj (op (op target)) ≃
      colimit (stageMapsTo X target) := by
  refine ((Ind.limCompInclusion.app X.rightOp).app (op (op target))).toEquiv.trans ?_
  exact (preservesColimitIso ((evaluation _ _).obj (op (op target)))
    (X.rightOp ⋙ yoneda)).toEquiv

/-- The outer, contravariant target-stage diagram. Its value at `j` is
canonically `colim_i (X_i ⟶ Y_j)`. -/
noncomputable def proHomDiagram
    {C : Type u} [Category.{v} C]
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    (X : Iᵒᵖ ⥤ C) (Y : Jᵒᵖ ⥤ C) : Jᵒᵖ ⥤ Type v :=
  Y.rightOp.op ⋙ stageColimitFunctor X

/-- The limit-colimit formula for the morphism type of two presented
pro-objects. -/
noncomputable def ProHom
    {C : Type u} [Category.{v} C]
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    (X : Iᵒᵖ ⥤ C) (Y : Jᵒᵖ ⥤ C) : Type v :=
  limit (proHomDiagram X Y)

/-- For presented pro-objects, categorical morphisms are exactly
`lim_j colim_i Hom(X_i, Y_j)`. -/
noncomputable def pro_category_hom_formula
    {C : Type u} [Category.{v} C]
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    (X : Iᵒᵖ ⥤ C) (Y : Jᵒᵖ ⥤ C) :
    (presentedObject X ⟶ presentedObject Y) ≃ ProHom X Y := by
  refine Quiver.Hom.opEquiv.symm.trans ?_
  refine Ind.inclusion.fullyFaithful.homEquiv.trans ?_
  refine (Iso.homCongr (Ind.limCompInclusion.app Y.rightOp) (Iso.refl _)).trans ?_
  exact colimitYonedaHomEquiv Y.rightOp (stageColimitFunctor X)

/-- Every target-stage component of a pro-morphism is represented after
refining the source to one sufficiently fine stage. -/
theorem pro_hom_has_stage_representatives
    {C : Type u} [Category.{v} C]
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    (X : Iᵒᵖ ⥤ C) (Y : Jᵒᵖ ⥤ C) (f : ProHom X Y) (j : Jᵒᵖ) :
    ∃ (i : I) (stageMap : X.obj (op i) ⟶ Y.obj j),
      colimit.ι (stageMapsTo X (Y.obj j)) i
          ((stageMapsToObjEquiv X (Y.obj j) i).symm stageMap) =
        stageColimitEquiv X (Y.obj j) (limit.π (proHomDiagram X Y) j f) := by
  obtain ⟨i, stageMap, hstageMap⟩ := Types.jointly_surjective'
    (stageColimitEquiv X (Y.obj j) (limit.π (proHomDiagram X Y) j f))
  refine ⟨i, stageMapsToObjEquiv X (Y.obj j) i stageMap, ?_⟩
  simpa using hstageMap

/-- The target-stage classes extracted from one pro-morphism are compatible
with every refinement arrow in the target diagram. -/
theorem pro_hom_stage_classes_compatible
    {C : Type u} [Category.{v} C]
    {I J : Type v} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J]
    (X : Iᵒᵖ ⥤ C) (Y : Jᵒᵖ ⥤ C) (f : ProHom X Y)
    {j j' : Jᵒᵖ} (g : j ⟶ j') :
    (proHomDiagram X Y).map g (limit.π (proHomDiagram X Y) j f) =
      limit.π (proHomDiagram X Y) j' f := by
  exact limit.w_apply (proHomDiagram X Y) g f

/-- A one-object inverse system presenting `A`. -/
def singleStageDiagram
    {C : Type u} [Category.{v} C] (A : C) :
    (Discrete PUnit.{v + 1})ᵒᵖ ⥤ C :=
  (Functor.const _).obj A

/-- When both index categories have one object, the pro-morphism formula
reduces to the ordinary Hom type. -/
noncomputable def proHomSingleStageEquiv
    {C : Type u} [Category.{v} C] (A B : C) :
    ProHom (singleStageDiagram A) (singleStageDiagram B) ≃ (A ⟶ B) := by
  let X := singleStageDiagram A
  let Y := singleStageDiagram B
  let j : (Discrete PUnit.{v + 1})ᵒᵖ := ⊥_ _
  let i : Discrete PUnit.{v + 1} := ⊤_ _
  refine (asIso (limit.π (proHomDiagram X Y) j)).toEquiv.trans ?_
  refine (stageColimitEquiv X (Y.obj j)).trans ?_
  refine (asIso (colimit.ι (stageMapsTo X (Y.obj j)) i)).symm.toEquiv.trans ?_
  exact stageMapsToObjEquiv X (Y.obj j) i

/-- The explicit nonempty witness in `Type`: the identity function is the
ordinary map represented by a unique element of the single-stage Pro-Hom. -/
theorem type_single_stage_identity_witness (A : Type u) :
    ∃ f : ProHom (singleStageDiagram A) (singleStageDiagram A),
      proHomSingleStageEquiv A A f = (𝟙 A : A ⟶ A) := by
  exact ⟨(proHomSingleStageEquiv A A).symm (𝟙 A),
    (proHomSingleStageEquiv A A).apply_symm_apply (𝟙 A)⟩

#print axioms pro_category_hom_formula
#print axioms pro_hom_has_stage_representatives
#print axioms pro_hom_stage_classes_compatible
#print axioms proHomSingleStageEquiv
#print axioms type_single_stage_identity_witness

end D5.S3.ObserverMemory.ProObjects.GeneralHomFormula

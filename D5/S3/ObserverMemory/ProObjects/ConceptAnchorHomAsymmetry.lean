/- GID: D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Constant-object morphisms compute as the stage colimit and stage limit. -/

import Mathlib.CategoryTheory.Limits.Indization.Category

/- Library-search audit trail (2026-08-22):
   * Repository search found `FiniteStageReadout`, which constructs only the
     first stage-colimit quotient and its representative corollary; it has no
     pro-category or Hom equivalence to reuse.
   * Pinned Mathlib has no declared `CategoryTheory.Pro` alias. The canonical
     construction is the opposite of `Ind` on the opposite category.
   * Exact hits `Ind.yoneda`, `Ind.inclusion.fullyFaithful`, `Ind.lim`,
     `Ind.yonedaCompInclusion`, and `Ind.limCompInclusion` occur in
     `Mathlib.CategoryTheory.Limits.Indization.Category` and are applied below.
   * Exact hit `colimitYonedaHomEquiv` in the imported Ind locally-small API
     supplies the second Hom-limit calculation. `Quiver.Hom.opEquiv`,
     `yonedaEquiv`, and `preservesColimitIso` supply the remaining canonical
     opposite, representable, and pointwise-colimit equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry

open CategoryTheory CategoryTheory.Limits Opposite Functor

universe u v

/-- The canonical pro-object category, defined as the opposite of Ind-objects
in the opposite category. -/
abbrev ProObjectCategory (C : Type u) [Category.{v} C] := (Ind Cᵒᵖ)ᵒᵖ

/-- The constant pro-object induced by the fully faithful Ind Yoneda
embedding. -/
noncomputable def constantObject
    {C : Type u} [Category.{v} C] (A : C) : ProObjectCategory C :=
  op ((Ind.yoneda (C := Cᵒᵖ)).obj (op A))

/-- A cofiltered stage diagram, indexed as `Jᵒᵖ`, presents a pro-object by the
filtered Ind-colimit of its opposite diagram. -/
noncomputable def presentedObject
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (stages : Jᵒᵖ ⥤ C) : ProObjectCategory C :=
  op ((Ind.lim J).obj stages.rightOp)

/-- The filtered diagram whose stage `j` consists of maps from the stage
object into an ordinary target. -/
def stageMapsTo
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J]
    (stages : Jᵒᵖ ⥤ C) (target : C) : J ⥤ Type v :=
  stages.rightOp ⋙ coyoneda.obj (op (op target))

/-- The cofiltered diagram whose stage consists of maps from an ordinary
source into the corresponding stage object. -/
def stageMapsFrom
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J]
    (source : C) (stages : Jᵒᵖ ⥤ C) : Jᵒᵖ ⥤ Type v :=
  stages.rightOp.op ⋙ yoneda.obj (op source)

def stageMapsToObjEquiv
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J]
    (stages : Jᵒᵖ ⥤ C) (target : C) (j : J) :
    (stageMapsTo stages target).obj j ≃
      (stages.obj (op j) ⟶ target) := by
  change (op target ⟶ op (stages.obj (op j))) ≃
    (stages.obj (op j) ⟶ target)
  exact Quiver.Hom.opEquiv.symm

def stageMapsFromObjEquiv
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J]
    (source : C) (stages : Jᵒᵖ ⥤ C) (j : Jᵒᵖ) :
    (stageMapsFrom source stages).obj j ≃
      (source ⟶ stages.obj j) := by
  change (op (stages.obj j) ⟶ op source) ≃
    (source ⟶ stages.obj j)
  exact Quiver.Hom.opEquiv.symm

/-- The canonical equivalence from maps out of a presented pro-object into a
constant object to the filtered colimit of the stage maps. -/
noncomputable def presentedToConstantEquiv
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (stages : Jᵒᵖ ⥤ C) (target : C) :
    (presentedObject stages ⟶ constantObject target) ≃
      colimit (stageMapsTo stages target) := by
  refine Quiver.Hom.opEquiv.symm.trans ?_
  refine Ind.inclusion.fullyFaithful.homEquiv.trans ?_
  refine (Iso.homCongr
    (Ind.yonedaCompInclusion.app (op target))
    (Ind.limCompInclusion.app stages.rightOp)).trans ?_
  refine yonedaEquiv.trans ?_
  exact (preservesColimitIso ((evaluation _ _).obj (op (op target)))
    (stages.rightOp ⋙ yoneda)).toEquiv

/-- The canonical equivalence from maps out of a constant object into a
presented pro-object to the cofiltered limit of the stage maps. -/
noncomputable def constantToPresentedEquiv
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (source : C) (stages : Jᵒᵖ ⥤ C) :
    (constantObject source ⟶ presentedObject stages) ≃
      limit (stageMapsFrom source stages) := by
  refine Quiver.Hom.opEquiv.symm.trans ?_
  refine Ind.inclusion.fullyFaithful.homEquiv.trans ?_
  refine (Iso.homCongr
    (Ind.limCompInclusion.app stages.rightOp)
    (Ind.yonedaCompInclusion.app (op source))).trans ?_
  exact colimitYonedaHomEquiv stages.rightOp (yoneda.obj (op source))

/-- Maps from a presented pro-object to a constant object form the filtered
colimit of stage maps, while maps in the reverse constant-to-presented
direction form their cofiltered limit. -/
theorem concept_anchor_hom_asymmetry
    {C : Type u} [Category.{v} C]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (stages : Jᵒᵖ ⥤ C) (source target : C) :
    Function.Bijective
      (fun f : presentedObject stages ⟶ constantObject target =>
        (presentedToConstantEquiv stages target f :
          colimit (stageMapsTo stages target))) ∧
    Function.Bijective
      (fun f : constantObject source ⟶ presentedObject stages =>
        (constantToPresentedEquiv source stages f :
          limit (stageMapsFrom source stages))) := by
  exact ⟨(presentedToConstantEquiv stages target).bijective,
    (constantToPresentedEquiv source stages).bijective⟩

#print axioms presentedToConstantEquiv
#print axioms constantToPresentedEquiv
#print axioms concept_anchor_hom_asymmetry

end D5.S3.ObserverMemory.ProObjects.ConceptAnchorHomAsymmetry

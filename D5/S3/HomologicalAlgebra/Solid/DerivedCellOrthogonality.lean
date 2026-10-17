/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedCellOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import D5.S3.HomologicalAlgebra.Solid.ExactMates
import D5.S3.HomologicalAlgebra.Solid.FreeFlat
import D5.S3.HomologicalAlgebra.Solid.CellLocality

/-!
The protected defining cells tested in the actual unbounded derived category.
These proofs use only the exact tensor/internal-Hom adjunction for P, not a
derived solidification adjunction. New proofs, Apache 2.0.
-/

noncomputable section
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open Pretriangulated

namespace LightCondensed.Solid

private theorem precomp_bijective_conjugate
    {C : Type*} [Category* C] {X X' Y : C} (e : X ≅ X')
    (f : X ⟶ X) (f' : X' ⟶ X') (he : f ≫ e.hom = e.hom ≫ f')
    (hf : Function.Bijective (fun (g : X ⟶ Y) => f ≫ g)) :
    Function.Bijective (fun (g : X' ⟶ Y) => f' ≫ g) := by
  constructor
  · intro u v huv
    apply (cancel_epi e.hom).1
    apply hf.injective
    change f ≫ (e.hom ≫ u) = f ≫ (e.hom ≫ v)
    calc
      f ≫ e.hom ≫ u = e.hom ≫ f' ≫ u := by rw [← Category.assoc, he, Category.assoc]
      _ = e.hom ≫ f' ≫ v := congrArg (e.hom ≫ ·) huv
      _ = f ≫ e.hom ≫ v := by rw [← Category.assoc, ← he, Category.assoc]
  · intro u
    obtain ⟨v, hv⟩ := hf.surjective (e.hom ≫ u)
    refine ⟨e.inv ≫ v, ?_⟩
    apply (cancel_epi e.hom).1
    rw [← Category.assoc, ← he, Category.assoc, e.hom_inv_id_assoc]
    exact hv

/-- The defining action on tensoring with the protected P, in all degrees. -/
def solidTensorEndomorphism : tensorLeft P ⟶ tensorLeft P :=
  (tensoringLeft LightCondAb).map oneMinusShift

/-- Its genuine derived natural transformation; tensoring with P is exact. -/
def solidDerivedTensorEndomorphism :
    (tensorLeft P).mapDerivedCategory ⟶ (tensorLeft P).mapDerivedCategory :=
  solidTensorEndomorphism.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- The exact inclusion has derived-local image in every degree, without
any derived solidification existence or full-faithfulness hypothesis. -/
theorem solidDerivedEndomorphism_derivedInclusion_isIso (Y : DSolid) :
    IsIso (solidDerivedEndomorphism.app (derivedInclusion.obj Y)) := by
  let K := DerivedCategory.Q.objPreimage Y
  let I := isSolid.ι.mapHomologicalComplex (.up ℤ) |>.obj K
  have hI (n : ℤ) : isSolid (I.homology n) :=
    isSolid.prop_of_iso ((K.sc n).mapHomologyIso isSolid.ι).symm (K.homology n).property
  have : IsIso (solidDerivedEndomorphism.app (DerivedCategory.Q.obj I)) :=
    (isIso_solidDerivedEndomorphism_Q_iff I).2 hI
  let e : DerivedCategory.Q.obj I ≅ derivedInclusion.obj Y :=
    (isSolid.ι.mapDerivedCategoryFactors.app K).symm ≪≫
      derivedInclusion.mapIso (DerivedCategory.Q.objObjPreimageIso Y)
  have h := solidDerivedEndomorphism.naturality e.hom
  have heq : solidDerivedEndomorphism.app (derivedInclusion.obj Y) =
      (ihom P).mapDerivedCategory.map e.inv ≫
        solidDerivedEndomorphism.app (DerivedCategory.Q.obj I) ≫
          (ihom P).mapDerivedCategory.map e.hom := by
    rw [← h, ← Functor.map_comp_assoc, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [heq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The defining map with an arbitrary derived tensor parameter induces
a bijection on derived maps into any object with vanishing locality defect.
Both the source and target may be unbounded. -/
theorem solidDerivedTensor_precomp_bijective
    (X Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : (tensorLeft P).mapDerivedCategory.obj X ⟶ Y) =>
      solidDerivedTensorEndomorphism.app X ≫ g) := by
  let adj := CWSolid.exactAdjunctionDerived (ihom.adjunction P)
  let e := adj.homEquiv X Y
  have mate (g : (tensorLeft P).mapDerivedCategory.obj X ⟶ Y) :
      e (solidDerivedTensorEndomorphism.app X ≫ g) =
        e g ≫ solidDerivedEndomorphism.app Y := by
    exact CWSolid.exactAdjunctionDerived_homEquiv_mate (ihom.adjunction P)
      solidTensorEndomorphism (MonoidalClosed.pre oneMinusShift)
      (fun B => (MonoidalClosed.coev_app_comp_pre_app B oneMinusShift).symm) X Y g
  constructor
  · intro f g h
    apply e.injective
    apply (cancel_mono (solidDerivedEndomorphism.app Y)).1
    rw [← mate, ← mate]
    exact congrArg e h
  · intro g
    let f := e.symm (e g ≫ inv (solidDerivedEndomorphism.app Y))
    refine ⟨f, e.injective ?_⟩
    rw [mate]
    simp [f]

set_option backward.isDefEq.respectTransparency false in
/-- The same bijection for the actual degreewise map on any unbounded
complex, not just for a single free generator. -/
theorem solidTensorComplex_precomp_bijective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj
      ((tensorLeft P).mapHomologicalComplex (.up ℤ) |>.obj K) ⟶ Y) =>
        DerivedCategory.Q.map ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K) ≫ g) := by
  let e := (tensorLeft P).mapDerivedCategoryFactors.app K
  let f := DerivedCategory.Q.map
    ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K)
  have he : solidDerivedTensorEndomorphism.app (DerivedCategory.Q.obj K) ≫ e.hom =
      e.hom ≫ f := by
    rw [solidDerivedTensorEndomorphism, NatTrans.mapDerivedCategory_app_Q_obj]
    simp [e, f, Category.assoc]
  have hb := solidDerivedTensor_precomp_bijective (DerivedCategory.Q.obj K) Y
  exact precomp_bijective_conjugate e _ f he hb

set_option backward.isDefEq.respectTransparency false in
/-- The actual defining map placed in any integer degree is invisible to
maps into derived-local targets. No projectivity of the tensor parameter
and no derived solidification adjunction is used. -/
theorem solidTensorSingle_precomp_bijective
    (B : LightCondAb) (n : ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj
      ((single LightCondAb (.up ℤ) n).obj (P ⊗ B)) ⟶ Y) =>
        DerivedCategory.Q.map ((single LightCondAb (.up ℤ) n).map (oneMinusShift ▷ B)) ≫ g) := by
  let K := (single LightCondAb (.up ℤ) n).obj B
  let ec := (singleMapHomologicalComplex (tensorLeft P) (.up ℤ) n).app B
  let f := (solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K
  let f' := (single LightCondAb (.up ℤ) n).map (oneMinusShift ▷ B)
  have h : f ≫ ec.hom = ec.hom ≫ f' := by
    apply (cancel_epi ec.inv).1
    apply from_single_hom_ext
    simp [f, f', ec, K, solidTensorEndomorphism]
    rw [single_map_f_self]
    have hn := solidTensorEndomorphism.naturality (singleObjXSelf (.up ℤ) n B).inv
    dsimp [solidTensorEndomorphism] at hn
    rw [reassoc_of% hn]
    simp [← MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact precomp_bijective_conjugate (DerivedCategory.Q.mapIso ec)
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map f')
    (by simpa only [Functor.mapIso_hom, ← Functor.map_comp] using congrArg DerivedCategory.Q.map h)
    (solidTensorComplex_precomp_bijective K Y)

set_option backward.isDefEq.respectTransparency false in
private theorem shifted_precomp_bijective
    {C : Type*} [Category* C] [HasShift C ℤ]
    {X Y : C} (f : X ⟶ X)
    (hf : Function.Bijective (fun (g : X ⟶ Y⟦(-1 : ℤ)⟧) => f ≫ g)) :
    Function.Bijective (fun (g : X⟦(1 : ℤ)⟧ ⟶ Y) => f⟦(1 : ℤ)⟧' ≫ g) := by
  let e := (shiftEquiv C (1 : ℤ)).toAdjunction.homEquiv X Y
  have he (g : X⟦(1 : ℤ)⟧ ⟶ Y) : e (f⟦(1 : ℤ)⟧' ≫ g) = f ≫ e g :=
    (shiftEquiv C (1 : ℤ)).toAdjunction.homEquiv_naturality_left f g
  constructor
  · intro u v huv
    change f⟦(1 : ℤ)⟧' ≫ u = f⟦(1 : ℤ)⟧' ≫ v at huv
    apply e.injective
    apply hf.injective
    change f ≫ e u = f ≫ e v
    rw [← he, ← he]
    exact congrArg e huv
  · intro u
    obtain ⟨v, hv⟩ := hf.surjective (e u)
    change f ≫ v = e u at hv
    refine ⟨e.symm v, e.injective ?_⟩
    change e (f⟦(1 : ℤ)⟧' ≫ e.symm v) = e u
    exact (he (e.symm v)).trans (by rw [e.apply_symm_apply]; exact hv)

private theorem solidDerivedEndomorphism_shift_isIso (Y : DLightCondAb) (n : ℤ)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    IsIso (solidDerivedEndomorphism.app (Y⟦n⟧)) := by
  haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app Y) :=
    (inferInstance : IsIso (solidDerivedEndomorphism.app Y))
  unfold solidDerivedEndomorphism
  rw [NatTrans.app_shift _ n Y]
  infer_instance

private theorem triangle_hom_zero_of_precomp_bijective
    {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) (Y : C)
    (hf : Function.Bijective (fun (g : T.obj₂ ⟶ Y) => T.mor₁ ≫ g))
    (hf' : Function.Surjective
      (fun (g : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y) => T.mor₁⟦(1 : ℤ)⟧' ≫ g))
    (u : T.obj₃ ⟶ Y) : u = 0 := by
  have hu : T.mor₂ ≫ u = 0 := hf.injective (by
    simp only [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp, comp_zero])
  obtain ⟨v, hv⟩ := T.yoneda_exact₃ hT u hu
  obtain ⟨w, hw⟩ := hf' v
  rw [hv, ← hw, ← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The derived invisibility statement also holds with an arbitrary
unbounded complex as tensor parameter. This permits assembly of all the
cells at once, rather than assuming preservation of coproducts by Q. -/
theorem solidTensorCone_derivedHom_zero
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)]
    (g : DerivedCategory.Q.obj (CochainComplex.mappingCone
      ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K)) ⟶ Y) : g = 0 := by
  let f := (solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K
  have : IsIso (solidDerivedEndomorphism.app (Y⟦(-1 : ℤ)⟧)) := by
    exact solidDerivedEndomorphism_shift_isIso Y (-1)
  exact triangle_hom_zero_of_precomp_bijective
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
    (DerivedCategory.mappingCone_triangle_distinguished f) Y
    (solidTensorComplex_precomp_bijective K Y)
    (shifted_precomp_bijective (DerivedCategory.Q.map f)
      (solidTensorComplex_precomp_bijective K (Y⟦(-1 : ℤ)⟧))).surjective g

set_option backward.isDefEq.respectTransparency false in
/-- Every actual defining cell has zero outgoing morphisms to a derived
object with solid homology. The statement is in the genuine unbounded
derived category, including all roofs, rather than only chain maps. -/
theorem solidLocalizationCell_derivedHom_zero
    (i : SmallModel.{0} LightProfinite × ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)]
    (g : DerivedCategory.Q.obj (solidLocalizationCell i) ⟶ Y) : g = 0 := by
  let B := (LightCondensed.free ℤ).obj
    ((equivSmallModel LightProfinite).inverse.obj i.1).toCondensed
  let f := (single LightCondAb (.up ℤ) i.2).map (oneMinusShift ▷ B)
  have : IsIso (solidDerivedEndomorphism.app (Y⟦(-1 : ℤ)⟧)) := by
    exact solidDerivedEndomorphism_shift_isIso Y (-1)
  exact triangle_hom_zero_of_precomp_bijective
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f))
    (DerivedCategory.mappingCone_triangle_distinguished f) Y
    (solidTensorSingle_precomp_bijective B i.2 Y)
    (shifted_precomp_bijective (DerivedCategory.Q.map f)
      (solidTensorSingle_precomp_bijective B i.2 (Y⟦(-1 : ℤ)⟧))).surjective g

/-- In particular, the actual defining cells have zero derived maps into
the image of every unbounded solid complex. -/
theorem solidLocalizationCell_derivedInclusionHom_zero
    (i : SmallModel.{0} LightProfinite × ℤ) (Y : DSolid)
    (g : DerivedCategory.Q.obj (solidLocalizationCell i) ⟶ derivedInclusion.obj Y) : g = 0 := by
  have := solidDerivedEndomorphism_derivedInclusion_isIso Y
  exact solidLocalizationCell_derivedHom_zero i _ g

set_option backward.isDefEq.respectTransparency false in
/-- An actual attachment along one defining cell has a universal derived
comparison against every derived-local target. This supplies both existence
and uniqueness for derived maps (not only chain-map homotopies). -/
theorem solidCellAttachment_derivedPrecomp_bijective
    (i : SmallModel.{0} LightProfinite × ℤ) (K : CochainComplex LightCondAb ℤ)
    (f : solidLocalizationCell i ⟶ K) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (CochainComplex.mappingCone f) ⟶ Y) =>
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr f) ≫ g) := by
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  have hcell (g : T.obj₁ ⟶ Y) : g = 0 := solidLocalizationCell_derivedHom_zero i Y g
  have : IsIso (solidDerivedEndomorphism.app (Y⟦(-1 : ℤ)⟧)) := by
    exact solidDerivedEndomorphism_shift_isIso Y (-1)
  have hshift (g : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) : g = 0 := by
    let e := (shiftEquiv DLightCondAb (1 : ℤ)).toAdjunction.homEquiv T.obj₁ Y
    letI : (shiftEquiv DLightCondAb (1 : ℤ)).functor.Additive := by
      change (shiftFunctor DLightCondAb (1 : ℤ)).Additive
      infer_instance
    apply e.injective
    exact (solidLocalizationCell_derivedHom_zero i (Y⟦(-1 : ℤ)⟧) (e g)).trans
      ((shiftEquiv DLightCondAb (1 : ℤ)).toAdjunction.homAddEquiv_zero _ _).symm
  constructor
  · intro g h hgh
    have hzero : T.mor₂ ≫ (g - h) = 0 := by
      change DerivedCategory.Q.map (CochainComplex.mappingCone.inr f) ≫ (g - h) = 0
      simp only [Preadditive.comp_sub, hgh, sub_self]
    obtain ⟨u, hu⟩ := T.yoneda_exact₃ hT (g - h) hzero
    exact sub_eq_zero.mp (by rw [hu, hshift u, comp_zero])
  · intro g
    obtain ⟨u, hu⟩ := T.yoneda_exact₂ hT g (hcell (T.mor₁ ≫ g))
    exact ⟨u, hu.symm⟩

end LightCondensed.Solid

/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedCellAttachment
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedCellAttachment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedCellOrthogonality
import D5.S3.HomologicalAlgebra.Solid.ConeColimit

/-! The simultaneous, arbitrary-size actual cell attachments tested in the
unbounded derived category. New proofs, released under Apache 2.0. -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomologicalComplex
open Pretriangulated

namespace LightCondensed.Solid

local instance complexCoproducts (I : Type) :
    HasColimitsOfShape (Discrete I) (CochainComplex LightCondAb ℤ) where
  has_colimit F := by
    haveI : HasColimitsOfShape (Discrete I) LightCondAb :=
      HasColimitsOfSize.has_colimits_of_shape (C := LightCondAb) (J := Discrete I)
    haveI (n : ℤ) : HasColimit (F ⋙ eval LightCondAb (.up ℤ) n) := inferInstance
    exact ⟨⟨⟨HomologicalComplex.coconeOfHasColimitEval F,
      HomologicalComplex.isColimitCoconeOfHasColimitEval F⟩⟩⟩

local instance tensorPComplex_leftAdjoint :
    ((tensorLeft P).mapHomologicalComplex (.up ℤ)).IsLeftAdjoint :=
  (CWSolid.mapHomologicalComplexAdjunction (ihom.adjunction P) (.up ℤ)).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The coproduct of tensor-action cones is the tensor-action cone on
the coproduct of the original unbounded complexes. -/
def solidTensorConeCoproductIso {I : Type}
    (K : I → CochainComplex LightCondAb ℤ) :
    (∐ fun i => CochainComplex.mappingCone
      ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app (K i))) ≅
      CochainComplex.mappingCone
        ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app (∐ K)) := by
  let F := (tensorLeft P).mapHomologicalComplex (.up ℤ)
  let a := solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)
  let e := PreservesCoproduct.iso F K
  have h : Limits.Sigma.map (fun i => a.app (K i)) ≫ e.inv = e.inv ≫ a.app (∐ K) := by
    dsimp only [e]
    rw [PreservesCoproduct.inv_hom]
    apply colimit.hom_ext
    intro ⟨i⟩
    simp only [Sigma.ι_map_assoc]
    change a.app (K i) ≫ Sigma.ι (fun j => F.obj (K j)) i ≫ sigmaComparison F K =
      Sigma.ι (fun j => F.obj (K j)) i ≫ sigmaComparison F K ≫ a.app (∐ K)
    simp only [ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc]
    exact (a.naturality (Sigma.ι K i)).symm
  exact CWSolid.mappingConeCoproductIso (fun i => F.obj (K i)) (fun i => a.app (K i)) ≪≫
    homotopyCofiber.mapArrowIso _ _
      (fun n => ⟨n - 1, by change n - 1 + 1 = n; omega⟩)
      (Arrow.isoMk e.symm e.symm h.symm)

set_option backward.isDefEq.respectTransparency false in
/-- A coproduct of arbitrary tensor-action cones has no derived maps
into any derived-local target. This uses an actual cone comparison and
does not presume coproduct preservation by the derived localization. -/
theorem solidTensorConeCoproduct_derivedHom_zero {I : Type}
    (K : I → CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)]
    (g : DerivedCategory.Q.obj (∐ fun i => CochainComplex.mappingCone
      ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app (K i))) ⟶ Y) : g = 0 := by
  let e := DerivedCategory.Q.mapIso (solidTensorConeCoproductIso K)
  have h : e.inv ≫ g = 0 := solidTensorCone_derivedHom_zero (∐ K) Y (e.inv ≫ g)
  rw [← cancel_epi e.inv, h, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The saved defining cell is the tensor-action cone on the original
single free generator; the comparison preserves the protected map. -/
def solidLocalizationCellTensorConeIso (i : SmallModel.{0} LightProfinite × ℤ) :
    solidLocalizationCell i ≅ CochainComplex.mappingCone
      ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app
        ((single LightCondAb (.up ℤ) i.2).obj ((LightCondensed.free ℤ).obj
          ((equivSmallModel LightProfinite).inverse.obj i.1).toCondensed))) := by
  let B := (LightCondensed.free ℤ).obj
    ((equivSmallModel LightProfinite).inverse.obj i.1).toCondensed
  let K := (single LightCondAb (.up ℤ) i.2).obj B
  let ec := (singleMapHomologicalComplex (tensorLeft P) (.up ℤ) i.2).app B
  let f := (solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app K
  let f' := (single LightCondAb (.up ℤ) i.2).map (oneMinusShift ▷ B)
  have h : f ≫ ec.hom = ec.hom ≫ f' := by
    apply (cancel_epi ec.inv).1
    apply from_single_hom_ext
    simp [f, f', ec, K, solidTensorEndomorphism]
    rw [single_map_f_self]
    have hn := solidTensorEndomorphism.naturality (singleObjXSelf (.up ℤ) i.2 B).inv
    dsimp [solidTensorEndomorphism] at hn
    rw [reassoc_of% hn]
    simp [← MonoidalCategory.whiskerLeft_comp, Category.assoc]
  exact (homotopyCofiber.mapArrowIso _ _
    (fun n => ⟨n - 1, by change n - 1 + 1 = n; omega⟩) (Arrow.isoMk ec ec h.symm)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Every small coproduct of actual defining cells has zero maps in the
derived category to derived-local targets. -/
theorem solidCellCoproduct_derivedHom_zero {I : Type}
    (i : I → SmallModel.{0} LightProfinite × ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)]
    (g : DerivedCategory.Q.obj (∐ fun j => solidLocalizationCell (i j)) ⟶ Y) : g = 0 := by
  let K j := (single LightCondAb (.up ℤ) (i j).2).obj ((LightCondensed.free ℤ).obj
    ((equivSmallModel LightProfinite).inverse.obj (i j).1).toCondensed)
  let e₀ : (∐ fun j => solidLocalizationCell (i j)) ≅
      (∐ fun j => CochainComplex.mappingCone
        ((solidTensorEndomorphism.mapHomologicalComplex (.up ℤ)).app (K j))) :=
    HasColimit.isoOfNatIso
    (Discrete.natIso (fun j => solidLocalizationCellTensorConeIso (i j.as)))
  let e := DerivedCategory.Q.mapIso (e₀ ≪≫ solidTensorConeCoproductIso K)
  have h : e.inv ≫ g = 0 := solidTensorCone_derivedHom_zero (∐ K) Y (e.inv ≫ g)
  rw [← cancel_epi e.inv, h, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Simultaneous attachment of an arbitrary family of the protected cells
has a universal derived comparison to each derived-local target. -/
theorem solidCellsAttachment_derivedPrecomp_bijective {I : Type}
    (i : I → SmallModel.{0} LightProfinite × ℤ) (K : CochainComplex LightCondAb ℤ)
    (f : (∐ fun j => solidLocalizationCell (i j)) ⟶ K) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (CochainComplex.mappingCone f) ⟶ Y) =>
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr f) ≫ g) := by
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hT := DerivedCategory.mappingCone_triangle_distinguished f
  have hcell (g : T.obj₁ ⟶ Y) : g = 0 := solidCellCoproduct_derivedHom_zero i Y g
  have : IsIso (solidDerivedEndomorphism.app (Y⟦(-1 : ℤ)⟧)) := by
    haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app Y) :=
      (inferInstance : IsIso (solidDerivedEndomorphism.app Y))
    unfold solidDerivedEndomorphism
    rw [NatTrans.app_shift _ (-1 : ℤ) Y]
    infer_instance
  have hshift (g : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y) : g = 0 := by
    let e := (shiftEquiv DLightCondAb (1 : ℤ)).toAdjunction.homEquiv T.obj₁ Y
    letI : (shiftEquiv DLightCondAb (1 : ℤ)).functor.Additive := by
      change (shiftFunctor DLightCondAb (1 : ℤ)).Additive
      infer_instance
    apply e.injective
    exact (solidCellCoproduct_derivedHom_zero i (Y⟦(-1 : ℤ)⟧) (e g)).trans
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

set_option backward.isDefEq.respectTransparency false in
/-- The actual saved attachment step, along all maps from all defining
cells, has the proved universal derived comparison. -/
theorem solidCellularStep_derivedPrecomp_bijective
    (K : CochainComplex LightCondAb ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun (g : DerivedCategory.Q.obj (solidCellularStep K) ⟶ Y) =>
      DerivedCategory.Q.map (solidCellularStepι K) ≫ g) := by
  unfold solidCellularStepι
  apply solidCellsAttachment_derivedPrecomp_bijective

end LightCondensed.Solid

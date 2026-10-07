/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedHomFiltration
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedHomFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.DerivedHomTriangle
import D5.S3.HomologicalAlgebra.Solid.DerivedGeneratorSums
import D5.S3.HomologicalAlgebra.Solid.SolidGeneratorAugmentation
import D5.S3.HomologicalAlgebra.Solid.LowerTruncationLayers

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
Extension of the literal generator comparison to every unbounded DSolid
source. The inputs are the actual kernel resolution, finite lower layers,
and the two actual truncation telescopes. No generation, replacement,
derived full faithfulness, or derived adjunction is assumed.
Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
This file is a proof attempt until a matching compiler/audit receipt exists.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits HomologicalComplex Pretriangulated LightCondensed
open scoped ZeroObject

namespace LightCondensed.Solid
open CWSolid

private theorem homGood_of_source_iso {X X' : DSolid} (e : X ≅ X') (Y : DSolid)
    (h : Function.Bijective (fun f : X ⟶ Y => derivedInclusion.map f)) :
    Function.Bijective (fun f : X' ⟶ Y => derivedInclusion.map f) := by
  constructor
  · intro f g hfg
    change derivedInclusion.map f = derivedInclusion.map g at hfg
    apply (cancel_epi e.hom).1
    apply h.injective
    change derivedInclusion.map (e.hom ≫ f) = derivedInclusion.map (e.hom ≫ g)
    simpa only [Functor.map_comp] using congrArg (derivedInclusion.map e.hom ≫ ·) hfg
  · intro f
    obtain ⟨g, hg⟩ := h.surjective (derivedInclusion.map e.hom ≫ f)
    change derivedInclusion.map g = derivedInclusion.map e.hom ≫ f at hg
    refine ⟨e.inv ≫ g, ?_⟩
    change derivedInclusion.map (e.inv ≫ g) = f
    rw [Functor.map_comp, hg, ← Functor.map_comp_assoc, e.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]

private def homGood : ObjectProperty DSolid := fun X =>
  ∀ (n : ℤ) (Y : DSolid),
    Function.Bijective (fun f : X⟦n⟧ ⟶ Y => derivedInclusion.map f)

private theorem homGood_iso {X X' : DSolid} (e : X ≅ X') (hX : homGood X) :
    homGood X' := fun n Y =>
  homGood_of_source_iso ((shiftFunctor DSolid n).mapIso e) Y (hX n Y)

private theorem homGood_shift (X : DSolid) (a : ℤ) (hX : homGood X) :
    homGood (X⟦a⟧) := fun n Y =>
  homGood_of_source_iso ((shiftFunctorAdd DSolid a n).app X) Y (hX (a + n) Y)

private theorem homGood_isZero {X : DSolid} (hX : IsZero X) : homGood X := by
  intro n Y
  have hz := (shiftFunctor DSolid n).map_isZero hX
  have hGz := derivedInclusion.map_isZero hz
  exact ⟨fun _ _ _ => hz.eq_of_src _ _, fun f => ⟨0, by
    change derivedInclusion.map 0 = f
    rw [Functor.map_zero]
    exact hGz.eq_of_src _ _⟩⟩

private instance homGood_closedUnderIsomorphisms : homGood.IsClosedUnderIsomorphisms where
  of_iso e h := homGood_iso e h

private instance homGood_containsZero : homGood.ContainsZero where
  exists_zero := ⟨0, isZero_zero _, homGood_isZero (isZero_zero _)⟩

private instance homGood_stableUnderShift : homGood.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun X h => homGood_shift X a h⟩

private instance homGood_closedUnderExtensions : homGood.IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h₁ h₃ n Y
    let Tn := (Triangle.shiftFunctor DSolid n).obj T
    exact mapHom_bijective_triangle_middle derivedInclusion Tn
      (T.shift_distinguished hT n) Y (h₁ n Y) (h₃ n Y)
      ((homGood_shift T.obj₁ n h₁) 1 Y).surjective
      ((homGood_shift T.obj₃ n h₃) (-1) Y).injective)

private instance homGood_isTriangulated : homGood.IsTriangulated where

private theorem map_bijective_from_colimit
    {J : Type*} [Category* J] {F : J ⥤ DSolid} (c : Cocone F)
    (hc : IsColimit c) (hGc : IsColimit (derivedInclusion.mapCocone c)) (Y : DSolid)
    (h : ∀ j, Function.Bijective (fun f : F.obj j ⟶ Y => derivedInclusion.map f)) :
    Function.Bijective (fun f : c.pt ⟶ Y => derivedInclusion.map f) := by
  constructor
  · intro f g hfg
    change derivedInclusion.map f = derivedInclusion.map g at hfg
    apply hc.hom_ext
    intro j
    apply (h j).injective
    change derivedInclusion.map (c.ι.app j ≫ f) = derivedInclusion.map (c.ι.app j ≫ g)
    simpa only [Functor.map_comp] using congrArg (derivedInclusion.map (c.ι.app j) ≫ ·) hfg
  · intro f
    let a j := ((h j).surjective (derivedInclusion.map (c.ι.app j) ≫ f)).choose
    have ha j : derivedInclusion.map (a j) = derivedInclusion.map (c.ι.app j) ≫ f :=
      ((h j).surjective (derivedInclusion.map (c.ι.app j) ≫ f)).choose_spec
    let d : Cocone F :=
      { pt := Y
        ι :=
          { app := a
            naturality j k u := by
              dsimp
              rw [Category.comp_id]
              apply (h j).injective
              change derivedInclusion.map (F.map u ≫ a k) = derivedInclusion.map (a j)
              rw [Functor.map_comp, ha, ha, ← Functor.map_comp_assoc, c.w u] } }
    refine ⟨hc.desc d, hGc.hom_ext (fun j => ?_)⟩
    change derivedInclusion.map (c.ι.app j) ≫ derivedInclusion.map (hc.desc d) =
      derivedInclusion.map (c.ι.app j) ≫ f
    rw [← Functor.map_comp, hc.fac d j]
    exact ha j

private theorem homGood_complex_coproduct {I : Type}
    (K : I → CochainComplex Solid ℤ)
    (hK : ∀ i, homGood (DerivedCategory.Q.obj (K i))) :
    homGood (DerivedCategory.Q.obj (∐ K)) := by
  intro n Y
  let D := Discrete.functor (fun i => DerivedCategory.Q.obj (K i))
  let c : Cocone D := Cofan.mk (DerivedCategory.Q.obj (∐ K))
    (fun i => DerivedCategory.Q.map (Sigma.ι K i))
  let hc := derivedCoproductIsColimit K
  haveI : PreservesColimit D derivedInclusion := derivedInclusion_preservesComplexCoproduct K
  haveI : PreservesColimit D (derivedInclusion ⋙ shiftFunctor DLightCondAb n) := inferInstance
  haveI : PreservesColimit D (shiftFunctor DSolid n ⋙ derivedInclusion) :=
    preservesColimit_of_natIso D (derivedInclusion.commShiftIso n).symm
  exact map_bijective_from_colimit ((shiftFunctor DSolid n).mapCocone c)
    (isColimitOfPreserves (shiftFunctor DSolid n) hc)
    (isColimitOfPreserves (shiftFunctor DSolid n ⋙ derivedInclusion) hc) Y
    (fun i => hK i.as n Y)

private theorem homGood_mappingCone {K L : CochainComplex Solid ℤ} (f : K ⟶ L)
    (hK : homGood (DerivedCategory.Q.obj K)) (hL : homGood (DerivedCategory.Q.obj L)) :
    homGood (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) :=
  homGood.ext_of_isTriangulatedClosed₃ _ (DerivedCategory.mappingCone_triangle_distinguished f)
    hK hL

private theorem homGood_sequence_colimit (F : ℕ ⥤ CochainComplex Solid ℤ)
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ n, homGood (DerivedCategory.Q.obj (F.obj n))) :
    homGood (DerivedCategory.Q.obj c.pt) := by
  have hsum := homGood_complex_coproduct (fun n => F.obj n) hF
  have htel := homGood_mappingCone (complexSequenceDifferential F) hsum hsum
  haveI := complexSequenceTelescopeToCocone_quasiIso F c hc
  exact homGood_iso (asIso (DerivedCategory.Q.map (complexSequenceTelescopeToCocone F c))) htel

private theorem homGood_copower_stalk (I : Type) (i : ℤ) :
    homGood ((DerivedCategory.singleFunctor Solid i).obj
      (∐ fun _ : I => solidification.obj P)) := by
  intro n Y
  let e := (DerivedCategory.singleFunctors Solid).shiftIso n (i - n) i (by omega)
  exact homGood_of_source_iso (e.app _).symm Y
    (derivedInclusion_generatorCopower_map_bijective I (i - n) Y)

private theorem homGood_lower_finite (K : CochainComplex Solid ℤ)
    [K.IsStrictlyLE 0]
    (hK : ∀ i, homGood ((DerivedCategory.singleFunctor Solid i).obj (K.X i))) (m : ℕ) :
    homGood (DerivedCategory.Q.obj (lowerTruncation K m)) := by
  induction m with
  | zero =>
    haveI : (lowerTruncation K 0).IsStrictlyGE 0 := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      simp only [lowerTruncation, Nat.cast_zero, neg_zero,
        if_neg (show ¬ (0 : ℤ) ≤ i by omega)]
      exact Limits.isZero_zero Solid
    haveI : (lowerTruncation K 0).IsStrictlyLE 0 := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      simpa [lowerTruncation, show (0 : ℤ) ≤ i by omega] using
        K.isZero_of_isStrictlyLE 0 i hi
    obtain ⟨M, ⟨e⟩⟩ := CochainComplex.exists_iso_single (lowerTruncation K 0) 0
    let e₀ : (lowerTruncation K 0).X 0 ≅ M :=
      (HomologicalComplex.eval Solid (.up ℤ) 0).mapIso (X := lowerTruncation K 0) e ≪≫
        singleObjXSelf (.up ℤ) 0 M
    have h₀ : homGood ((DerivedCategory.singleFunctor Solid 0).obj
        ((lowerTruncation K 0).X 0)) := by simpa [lowerTruncation] using hK 0
    have hM := homGood_iso ((DerivedCategory.singleFunctor Solid 0).mapIso e₀) h₀
    exact homGood_iso (DerivedCategory.Q.mapIso e).symm hM
  | succ m ih =>
    let hS := lowerTruncationLayerSequence_shortExact K m
    exact homGood.ext_of_isTriangulatedClosed₂ _ (DerivedCategory.triangleOfSES_distinguished hS)
      ih (hK (-((m + 1 : ℕ) : ℤ)))

private theorem homGood_nonpositive (K : CochainComplex Solid ℤ)
    [K.IsStrictlyLE 0]
    (hK : ∀ i, homGood ((DerivedCategory.singleFunctor Solid i).obj (K.X i))) :
    homGood (DerivedCategory.Q.obj K) :=
  homGood_sequence_colimit (lowerTruncationDiagram K) (lowerTruncationCocone K)
    (lowerTruncationCocone_isColimit K) (homGood_lower_finite K hK)

private theorem homGood_solid_stalk_zero (X : Solid) :
    homGood ((DerivedCategory.singleFunctor Solid 0).obj X) := by
  let K := solidGeneratorCochainResolution X
  haveI : K.IsStrictlyLE 0 := by
    change (solidGeneratorProjectiveResolution X).cochainComplex.IsStrictlyLE 0
    infer_instance
  have hK (i : ℤ) : homGood ((DerivedCategory.singleFunctor Solid i).obj (K.X i)) := by
    by_cases hi : i ≤ 0
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hi
      obtain ⟨Y, ⟨e⟩⟩ := solidGeneratorCochainResolution_negative_term X n
      exact homGood_iso ((DerivedCategory.singleFunctor Solid (- (n : ℤ))).mapIso e).symm
        (homGood_copower_stalk (SolidGeneratorIndex Y) (- (n : ℤ)))
    · have hz := K.isZero_of_isStrictlyLE 0 i (by omega)
      exact homGood_isZero ((DerivedCategory.singleFunctor Solid i).map_isZero hz)
  have h := homGood_nonpositive K hK
  haveI := solidGeneratorCochainResolutionπ_quasiIso X
  exact homGood_iso (asIso (DerivedCategory.Q.map (solidGeneratorCochainResolutionπ X))) h

private theorem homGood_solid_stalk (X : Solid) (i : ℤ) :
    homGood ((DerivedCategory.singleFunctor Solid i).obj X) :=
  homGood_iso (((DerivedCategory.singleFunctors Solid).shiftIso (-i) i 0 (by simp)).app X)
    (homGood_shift _ (-i) (homGood_solid_stalk_zero X))

private theorem homGood_boundedAbove (K : CochainComplex Solid ℤ) (b : ℤ)
    [K.IsStrictlyLE b] : homGood (DerivedCategory.Q.obj K) := by
  haveI : (K⟦b⟧).IsStrictlyLE 0 := CochainComplex.isStrictlyLE_shift K b b 0 (by simp)
  have h := homGood_nonpositive (K⟦b⟧) (fun i => homGood_solid_stalk _ i)
  have hs := homGood_iso ((DerivedCategory.Q.commShiftIso b).app K) h
  exact homGood_iso ((shiftEquiv DSolid b).unitIso.app (DerivedCategory.Q.obj K)).symm
    (homGood_shift _ (-b) hs)

private theorem homGood_unbounded (K : CochainComplex Solid ℤ) :
    homGood (DerivedCategory.Q.obj K) :=
  homGood_sequence_colimit (upperTruncationDiagram K) (upperTruncationCocone K)
    (upperTruncationCocone_isColimit K)
    (fun m => homGood_boundedAbove (K.truncLE (m : ℤ)) (m : ℤ))

/-- The literal protected derived inclusion is bijective on morphisms
from EVERY unbounded source to EVERY unbounded target. The proof uses
the constructed generator resolution and both actual telescopes. -/
theorem derivedInclusion_map_bijective (X Y : DSolid) :
    Function.Bijective (fun f : X ⟶ Y => derivedInclusion.map f) := by
  have h := homGood_iso (DerivedCategory.Q.objObjPreimageIso X)
    (homGood_unbounded (DerivedCategory.Q.objPreimage X))
  exact homGood_of_source_iso ((shiftFunctorZero DSolid ℤ).app X) Y (h 0 Y)

/-- Actual full-faithfulness data, with inverse induced by the proved
literal-map bijection. No full-faithfulness premise is introduced. -/
def derivedInclusionFullyFaithful : derivedInclusion.FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective derivedInclusion).mpr
    derivedInclusion_map_bijective).some

end LightCondensed.Solid

#print axioms LightCondensed.Solid.derivedInclusion_map_bijective
#print axioms LightCondensed.Solid.derivedInclusionFullyFaithful

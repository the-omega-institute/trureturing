/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationDescent
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationDifferenceRelation
import D5.S3.HomologicalAlgebra.Solid.BoundedMeasures
import Mathlib.Condensed.Light.EffectiveEpi

/-!
Actual free descent of representative differences along the full compact
kernel pair, then through the protected infinity cokernel. Constructs
P -> free(S), without any derived-adjunction/realization premise.
New proofs, Apache-2.0; Juan Esteban Rodríguez Camargo, Notes on Solid
Geometry, Lemma 3.3.2. Effective-epi proof pattern: immutable Apache-2.0
CWComparison.FreeCoverPresentation (2026); no supplier source is modified.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint LightCondensed

namespace CWSolid

def finiteApproximationDifferencePullbackCone (S : LightProfinite) (s₀ : S) :
    PullbackCone (finiteApproximationDifferenceProjection S s₀)
      (finiteApproximationDifferenceProjection S s₀) :=
  PullbackCone.mk (finiteApproximationDifferenceRelationFst S s₀)
    (finiteApproximationDifferenceRelationSnd S s₀) (by ext r; exact r.property)

/-- The genuine full kernel-pair subtype is a categorical pullback. -/
def finiteApproximationDifferencePullbackIsLimit (S : LightProfinite) (s₀ : S) :
    IsLimit (finiteApproximationDifferencePullbackCone S s₀) :=
  PullbackCone.isLimitAux' _ (by
    intro T
    let m : T.pt ⟶ finiteApproximationDifferenceRelationSpace S s₀ :=
      ConcreteCategory.ofHom {
      toFun := fun x => ⟨(T.fst x, T.snd x), by
        simpa using! ConcreteCategory.congr_hom T.condition x⟩
      continuous_toFun := (T.fst.hom.hom.continuous.prodMk
        T.snd.hom.hom.continuous).subtype_mk (fun x => by
          simpa using! ConcreteCategory.congr_hom T.condition x) }
    refine ⟨m, ?_, ?_, ?_⟩
    · ext x
      rfl
    · ext x
      rfl
    · intro m' h₁ h₂
      ext x
      apply Subtype.ext
      apply Prod.ext
      · simpa using! ConcreteCategory.congr_hom h₁ x
      · simpa using! ConcreteCategory.congr_hom h₂ x)

end CWSolid

namespace LightCondensed.Solid

local notation "F" => (lightProfiniteToLightCondSet ⋙ free ℤ)

def finiteApproximationFreeDifference (S : LightProfinite) (s₀ : S) :
    freeOn (CWSolid.finiteApproximationDifferenceSpace S s₀) ⟶ freeOn S :=
  (free ℤ).map (lightProfiniteToLightCondSet.map
      (CWSolid.finiteApproximationDifferenceFirst S s₀)) -
    (free ℤ).map (lightProfiniteToLightCondSet.map
      (CWSolid.finiteApproximationDifferenceSecond S s₀))

private theorem finiteApproximationFreeDifference_relation_piece
    (S : LightProfinite) (s₀ : S) (b : Bool) :
    (F).map (CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ b) ≫
      (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
        finiteApproximationFreeDifference S s₀ =
    (F).map (CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ b) ≫
      (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
        finiteApproximationFreeDifference S s₀ := by
  cases b
  · rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      CWSolid.finiteApproximationDifferenceRelation_diagonal]
  · change
      (F).map (CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ true) ≫
        (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
          ((F).map (CWSolid.finiteApproximationDifferenceFirst S s₀) -
            (F).map (CWSolid.finiteApproximationDifferenceSecond S s₀)) =
      (F).map (CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ true) ≫
        (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
          ((F).map (CWSolid.finiteApproximationDifferenceFirst S s₀) -
            (F).map (CWSolid.finiteApproximationDifferenceSecond S s₀))
    simp only [Preadditive.comp_sub, ← Functor.map_comp_assoc, ← Functor.map_comp,
      Category.assoc]
    rw [CWSolid.finiteApproximationDifferenceRelation_infty_first,
      CWSolid.finiteApproximationDifferenceRelation_infty_second]
    simp only [sub_self]

/-- Equality on the entire relation follows from a genuine finite cover. -/
theorem finiteApproximationFreeDifference_relation (S : LightProfinite) (s₀ : S) :
    (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
      finiteApproximationFreeDifference S s₀ =
    (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
      finiteApproximationFreeDifference S s₀ := by
  let c := CWSolid.finiteApproximationDifferenceRelationCover S s₀
  haveI : Epi c := (LightProfinite.epi_iff_surjective c).mpr
    (CWSolid.finiteApproximationDifferenceRelationCover_surjective S s₀)
  haveI : Epi ((F).map c) := (F).map_epi c
  apply (cancel_epi ((F).map c)).1
  apply (isColimitOfPreserves F
    (CompHausLike.finiteCoproduct.isColimit
      (CWSolid.finiteApproximationDifferenceRelationPieceSpace S s₀))).hom_ext
  intro ⟨b⟩
  change (F).map (CompHausLike.finiteCoproduct.ι
      (CWSolid.finiteApproximationDifferenceRelationPieceSpace S s₀) b) ≫
      (F).map c ≫ (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
        finiteApproximationFreeDifference S s₀ =
    (F).map (CompHausLike.finiteCoproduct.ι
      (CWSolid.finiteApproximationDifferenceRelationPieceSpace S s₀) b) ≫
      (F).map c ≫ (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
        finiteApproximationFreeDifference S s₀
  have h : CompHausLike.finiteCoproduct.ι
      (CWSolid.finiteApproximationDifferenceRelationPieceSpace S s₀) b ≫ c =
      CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ b := by ext x; rfl
  have hmap : (F).map (CompHausLike.finiteCoproduct.ι
      (CWSolid.finiteApproximationDifferenceRelationPieceSpace S s₀) b) ≫
        (F).map c =
      (F).map (CWSolid.finiteApproximationDifferenceRelationPieceInclusion S s₀ b) :=
    ((F).map_comp _ _).symm.trans (congrArg (F).map h)
  have h₁ := congrArg (fun k => k ≫
    (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
      finiteApproximationFreeDifference S s₀) hmap
  have h₂ := congrArg (fun k => k ≫
    (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
      finiteApproximationFreeDifference S s₀) hmap
  simpa only [Category.assoc] using
    h₁.trans ((finiteApproximationFreeDifference_relation_piece S s₀ b).trans h₂.symm)

/-- The actual cover is the effective-epi coequalizer after taking free. -/
def finiteApproximationFreeCoforkIsColimit (S : LightProfinite) (s₀ : S) :
    IsColimit (Cofork.ofπ
      ((F).map (CWSolid.finiteApproximationDifferenceProjection S s₀))
      (show (F).map (CWSolid.finiteApproximationDifferenceRelationFst S s₀) ≫
          (F).map (CWSolid.finiteApproximationDifferenceProjection S s₀) =
        (F).map (CWSolid.finiteApproximationDifferenceRelationSnd S s₀) ≫
          (F).map (CWSolid.finiteApproximationDifferenceProjection S s₀) by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (F).map
          (CWSolid.finiteApproximationDifferencePullbackCone S s₀).condition)) := by
  let q := CWSolid.finiteApproximationDifferenceProjection S s₀
  haveI : Epi q := (LightProfinite.epi_iff_surjective q).mpr
    (CWSolid.finiteApproximationDifferenceProjection_surjective S s₀)
  haveI : Epi (lightProfiniteToLightCondSet.map q) :=
    lightProfiniteToLightCondSet.map_epi q
  haveI : EffectiveEpi (lightProfiniteToLightCondSet.map q) :=
    (regularEpiOfEpi _).effectiveEpi
  let c := CWSolid.finiteApproximationDifferencePullbackCone S s₀
  let c' := PullbackCone.mk (lightProfiniteToLightCondSet.map c.fst)
    (lightProfiniteToLightCondSet.map c.snd)
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ c.condition)
  have hc' : IsLimit c' := isLimitPullbackConeMapOfIsLimit
    lightProfiniteToLightCondSet c.condition
      (CWSolid.finiteApproximationDifferencePullbackIsLimit S s₀)
  exact isColimitCoforkMapOfIsColimit (free ℤ) c'.condition
    (isColimitCoforkOfEffectiveEpi (lightProfiniteToLightCondSet.map q) c' hc')

def finiteApproximationFreeSequence (S : LightProfinite) (s₀ : S) :
    freeOn (ℕ∪{∞}) ⟶ freeOn S :=
  (finiteApproximationFreeCoforkIsColimit S s₀).desc
    (Cofork.ofπ (finiteApproximationFreeDifference S s₀)
      (finiteApproximationFreeDifference_relation S s₀))

@[reassoc (attr := simp)] theorem finiteApproximationFreeSequence_fac
    (S : LightProfinite) (s₀ : S) :
    (F).map (CWSolid.finiteApproximationDifferenceProjection S s₀) ≫
      finiteApproximationFreeSequence S s₀ = finiteApproximationFreeDifference S s₀ :=
  (finiteApproximationFreeCoforkIsColimit S s₀).fac _ WalkingParallelPair.one

/-- An actual infinity lift kills the infinity value of the descended sequence. -/
theorem finiteApproximationFreeSequence_infty (S : LightProfinite) (s₀ : S) :
    P_map ≫ finiteApproximationFreeSequence S s₀ = 0 := by
  obtain ⟨p, hp⟩ := CWSolid.finiteApproximationDifferenceProjection_surjective S s₀ ∞
  let j : LightProfinite.of PUnit.{1} ⟶
      CWSolid.finiteApproximationDifferenceSpace S s₀ :=
    ConcreteCategory.ofHom ⟨fun _ => p, continuous_const⟩
  have hq : j ≫ CWSolid.finiteApproximationDifferenceProjection S s₀ = ι := by
    ext x
    exact hp
  change (F).map ι ≫ _ = _
  rw [← hq, Functor.map_comp, Category.assoc, finiteApproximationFreeSequence_fac]
  change (F).map j ≫ ((F).map (CWSolid.finiteApproximationDifferenceFirst S s₀) -
    (F).map (CWSolid.finiteApproximationDifferenceSecond S s₀)) = 0
  rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp]
  have h : j ≫ CWSolid.finiteApproximationDifferenceFirst S s₀ =
      j ≫ CWSolid.finiteApproximationDifferenceSecond S s₀ := by
    ext x
    exact CWSolid.finiteApproximationDifference_infty_fiber S s₀ p hp
  rw [h, sub_self]

/-- The actual P-to-free map needed for the generator retract. -/
def finiteApproximationPMap (S : LightProfinite) (s₀ : S) : P ⟶ freeOn S :=
  P_homMk _ (finiteApproximationFreeSequence S s₀)
    (finiteApproximationFreeSequence_infty S s₀)

@[reassoc (attr := simp)] theorem finiteApproximationPMap_fac
    (S : LightProfinite) (s₀ : S) :
    P_proj ≫ finiteApproximationPMap S s₀ = finiteApproximationFreeSequence S s₀ := by
  simp [finiteApproximationPMap, P_homMk, P_proj]

end LightCondensed.Solid

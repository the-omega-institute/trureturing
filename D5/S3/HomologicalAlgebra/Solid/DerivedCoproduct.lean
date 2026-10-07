/- GID: D5/S3/HomologicalAlgebra/Solid/DerivedCoproduct
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/DerivedCoproduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.ComplexColimit
import D5.S3.HomologicalAlgebra.Solid.LocalizationCoproduct
import D5.S3.HomologicalAlgebra.Solid.KProjectiveCoproduct
import D5.S3.HomologicalAlgebra.Solid.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Actual coproducts in the unbounded derived category of an abelian
category with exact sums. This supplies the sum comparison needed by the
cellular telescope; no derived solidification is assumed. New proofs,
released under the Apache 2.0 license. -/

noncomputable section
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]
  {I : Type} [HasColimitsOfShape (Discrete I) C]

set_option backward.isDefEq.respectTransparency false in
/-- The actual coproduct of unbounded complexes remains a coproduct in
the homotopy category, by assembling the saved component homotopies. -/
def homotopyCoproductIsColimit (K : I → CochainComplex C ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ K))
      (fun i => (HomotopyCategory.quotient C (.up ℤ)).map (Sigma.ι K i))) := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  refine Cofan.IsColimit.mk _
    (fun s => H.map (Sigma.desc (fun i => (s.inj i).out))) ?_ ?_
  · intro s i
    change H.map (Sigma.ι K i) ≫ H.map (Sigma.desc (fun i => (s.inj i).out)) = s.inj i
    rw [← H.map_comp, Sigma.ι_desc]
    exact HomotopyCategory.quotient_map_out (s.inj i)
  · intro s m hm
    change ∀ i, H.map (Sigma.ι K i) ≫ m = s.inj i at hm
    have hh : Homotopy m.out (Sigma.desc (fun i => (s.inj i).out)) :=
      homotopyFromCoproduct K (fun i => HomotopyCategory.homotopyOfEq _ _ (by
        rw [H.map_comp, HomotopyCategory.quotient_map_out, hm, Sigma.ι_desc]
        exact (HomotopyCategory.quotient_map_out (s.inj i)).symm))
    exact (HomotopyCategory.quotient_map_out m).symm.trans
      (HomotopyCategory.eq_of_homotopy _ _ hh)

local instance homotopyCoproducts :
    HasColimitsOfShape (Discrete I) (HomotopyCategory C (.up ℤ)) where
  has_colimit F := by
    let K (i : I) := (F.obj ⟨i⟩).as
    haveI : HasCoproduct (fun i => (HomotopyCategory.quotient C (.up ℤ)).obj (K i)) :=
      ⟨⟨⟨_, homotopyCoproductIsColimit K⟩⟩⟩
    let e : F ≅ Discrete.functor (fun i => (HomotopyCategory.quotient C (.up ℤ)).obj (K i)) :=
      Discrete.natIso (fun j => Iso.refl (F.obj j))
    exact hasColimit_of_iso e

local instance homotopyQuotient_preservesCoproduct (K : I → CochainComplex C ℤ) :
    PreservesColimit (Discrete.functor K) (HomotopyCategory.quotient C (.up ℤ)) :=
  preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (homotopyCoproductIsColimit K))

section Exact

variable [HasExactColimitsOfShape (Discrete I) C]

set_option backward.isDefEq.respectTransparency false in
private theorem homotopyQuasiIso_coproduct
    (X Y : I → HomotopyCategory C (.up ℤ)) (f : ∀ i, X i ⟶ Y i)
    (hf : ∀ i, HomotopyCategory.quasiIso C (.up ℤ) (f i)) :
    HomotopyCategory.quasiIso C (.up ℤ) (Limits.Sigma.map f) := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  let K i := (X i).as
  let M i := (Y i).as
  let g i : K i ⟶ M i := (f i).out
  haveI hg (i : I) : QuasiIso (g i) := by
    rw [← HomologicalComplex.mem_quasiIso_iff,
      ← HomotopyCategory.quotient_map_mem_quasiIso_iff]
    simpa only [g, HomotopyCategory.quotient_map_out] using hf i
  let τ : Discrete.functor K ⟶ Discrete.functor M := Discrete.natTrans (fun j => g j.as)
  haveI : ∀ j, QuasiIso (τ.app j) := fun j => hg j.as
  have hsum : QuasiIso (Limits.Sigma.map g) := quasiIso_colimitMap τ
  let eK := PreservesCoproduct.iso H K
  let eM := PreservesCoproduct.iso H M
  have he : eK.inv ≫ H.map (Limits.Sigma.map g) = Limits.Sigma.map f ≫ eM.inv := by
    apply Sigma.hom_ext
    intro i
    simp only [eK, eM, PreservesCoproduct.inv_hom, Sigma.ι_map_assoc]
    change Sigma.ι (fun j => H.obj (K j)) i ≫ sigmaComparison H K ≫
        H.map (Limits.Sigma.map g) =
      f i ≫ Sigma.ι (fun j => H.obj (M j)) i ≫ sigmaComparison H M
    rw [ι_comp_sigmaComparison_assoc, ← H.map_comp, Sigma.ι_map, H.map_comp]
    simp only [g, H, HomotopyCategory.quotient_map_out, ι_comp_sigmaComparison]
  have hQ : HomotopyCategory.quasiIso C (.up ℤ) (H.map (Limits.Sigma.map g)) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hsum
  exact ((HomotopyCategory.quasiIso C (.up ℤ)).arrow_mk_iso_iff
    (Arrow.isoMk eK.symm eM.symm he)).2 hQ

local instance homotopyQuasiIso_stableCoproducts :
    (HomotopyCategory.quasiIso C (.up ℤ)).IsStableUnderCoproductsOfShape I :=
  MorphismProperty.IsStableUnderCoproductsOfShape.mk
    (HomotopyCategory.quasiIso C (.up ℤ)) I
    (fun X Y _ _ f hf => homotopyQuasiIso_coproduct X Y f hf)

variable [HasDerivedCategory C]

local instance derivedQuotient_preservesCoproducts :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Qh (C := C)) where
  preservesColimit {F} := by
    let X (i : I) := F.obj ⟨i⟩
    haveI : (HomotopyCategory.quasiIso C (.up ℤ)).HasRightCalculusOfFractions := by
      rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
      infer_instance
    haveI : PreservesColimit (Discrete.functor X) (DerivedCategory.Qh (C := C)) :=
      preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
        ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
          (localizationCoproductIsColimit DerivedCategory.Qh
            (HomotopyCategory.quasiIso C (.up ℤ)) X))
    let e : Discrete.functor X ≅ F := Discrete.natIso (fun j => Iso.refl (F.obj j))
    exact preservesColimit_of_iso_diagram _ e

/-- The official unbounded derived localization preserves the actual
coproduct of complexes whenever sums in the original category are exact.
This follows from the proved roof argument, not an assumed property of Q. -/
theorem derivedQ_preservesCoproduct (K : I → CochainComplex C ℤ) :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := C)) := by
  exact preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso C)

/-- An explicit colimit witness for the derived images of an arbitrary
family of unbounded complexes. -/
def derivedCoproductIsColimit (K : I → CochainComplex C ℤ) :
    IsColimit (Cofan.mk (DerivedCategory.Q.obj (∐ K))
      (fun i => DerivedCategory.Q.map (Sigma.ι K i))) := by
  have := derivedQ_preservesCoproduct K
  exact isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K

end Exact
end CWSolid

namespace LightCondensed.Solid

set_option synthInstance.maxHeartbeats 200000 in
/-- The sum theorem applies to the actual protected light condensed
category and every small family of unbounded complexes. -/
theorem lightCondensedDerivedQ_preservesCoproduct {I : Type}
    (K : I → CochainComplex LightCondAb ℤ) :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := LightCondAb)) := by
  haveI : HasColimitsOfShape (Discrete I) LightCondAb :=
    solidification_hasSmallCoproducts I
  haveI : IsGrothendieckAbelian.{0} LightCondAb := inferInstance
  haveI : AB4OfSize.{0} LightCondAb := IsGrothendieckAbelian.ab4OfSize LightCondAb
  exact CWSolid.derivedQ_preservesCoproduct K

end LightCondensed.Solid

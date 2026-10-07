/- GID: D5/S3/HomologicalAlgebra/Solid/BoundedCoefficientDescent
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BoundedCoefficientDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedUnitMap
import D5.S3.HomologicalAlgebra.Solid.CoefficientLinearity
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
Descent of the bounded coefficient maps to the actual condensed object B_Z.
This constructs D : P tensor B_Z -> P as an honest condensed morphism.
New proofs, Apache-2.0; the construction is the coefficient map in
Rodríguez Camargo's Notes on Solid Geometry, Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory MonoidalClosed

namespace LightCondensed.Solid
open IntProof

def freeSectionIntAddEquiv (S : LightProfinite) (A : LightCondAb) :
    (freeOn S ⟶ A) ≃+ A.obj.obj (op S) where
  __ := freeSectionEquiv S A
  map_add' f g := by
    let x := freeSectionEquiv S (freeOn S) (𝟙 (freeOn S))
    have hev (h : freeOn S ⟶ A) : freeSectionEquiv S A h = h.hom.app (op S) x := by
      simpa only [Category.id_comp] using
        (freeSectionEquiv_comp S (𝟙 (freeOn S)) h)
    change freeSectionEquiv S A (f + g) = freeSectionEquiv S A f + freeSectionEquiv S A g
    rw [hev (f + g), hev f, hev g]
    rfl

def ihomPointsIntAddEquiv (A B : LightCondAb) (S : LightProfinite)
    [(tensorLeft A).Additive] :
    ((ihom A).obj B).obj.obj (op S) ≃+ (A ⊗ freeOn S ⟶ B) :=
  (freeSectionIntAddEquiv S ((ihom A).obj B)).symm.trans
    ((ihom.adjunction A).homAddEquiv (freeOn S) B).symm

theorem ihomPointsIntAddEquiv_eq (A B : LightCondAb) (S : LightProfinite)
    [(tensorLeft A).Additive] :
    (ihomPointsIntAddEquiv A B S).toEquiv = ihomPoints ℤ A B S := rfl

def boundedIntegerCoordinates (S : LightProfinite) (x : boundedIntegerSections S) :
    ℕ → LocallyConstant S ℤ := fun j => integerSectionCoordinate S j x.val

def boundedIntegerRange (S : LightProfinite) (x : boundedIntegerSections S) : Finset ℤ :=
  Finset.Icc (-(x.property.choose : ℤ)) (x.property.choose : ℤ)

theorem boundedIntegerRange_spec (S : LightProfinite) (x : boundedIntegerSections S) :
    ∀ j s, boundedIntegerCoordinates S x j s ∈ boundedIntegerRange S x := by
  intro j s
  exact Finset.mem_Icc.mpr (abs_le.mp (x.property.choose_spec j s))

def boundedIntegerCoefficient (S : LightProfinite) (x : boundedIntegerSections S) :
    P ⊗ freeOn S ⟶ P :=
  boundedCoefficientMap S (boundedIntegerCoordinates S x) (boundedIntegerRange S x)

theorem boundedIntegerCoefficient_add (S : LightProfinite)
    (x y : boundedIntegerSections S) :
    boundedIntegerCoefficient S (x + y) =
      boundedIntegerCoefficient S x + boundedIntegerCoefficient S y := by
  let N := x.property.choose + y.property.choose
  let H : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hsum : ∀ k ∈ boundedIntegerRange S x,
      ∀ l ∈ boundedIntegerRange S y, k + l ∈ H := by
    intro k hk l hl
    rw [boundedIntegerRange, Finset.mem_Icc] at hk hl
    apply Finset.mem_Icc.mpr
    dsimp [N]
    push_cast
    constructor <;> omega
  have hcoords : boundedIntegerCoordinates S (x + y) =
      boundedIntegerCoordinates S x + boundedIntegerCoordinates S y := by
    funext j
    exact map_add (integerSectionCoordinate S j) x.val y.val
  have hH : ∀ j s, boundedIntegerCoordinates S (x + y) j s ∈ H := by
    intro j s
    rw [hcoords]
    exact hsum _ (boundedIntegerRange_spec S x j s) _ (boundedIntegerRange_spec S y j s)
  dsimp only [boundedIntegerCoefficient]
  rw [boundedCoefficientMap_range_independent S _ _ H
    (boundedIntegerRange_spec S (x + y)) hH, hcoords]
  exact boundedCoefficientMap_add S _ _ _ _ H
    (boundedIntegerRange_spec S x) (boundedIntegerRange_spec S y) hsum

theorem boundedIntegerCoefficient_naturality {S' S : LightProfinite} (f : S' ⟶ S)
    (x : boundedIntegerSections S) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f) ≫
        boundedIntegerCoefficient S x =
      boundedIntegerCoefficient S' (boundedIntegerPresheaf.map f.op x) := by
  have hc : boundedIntegerCoordinates S' (boundedIntegerPresheaf.map f.op x) =
      pullIntegerFamily f (boundedIntegerCoordinates S x) := by
    funext j
    exact integerSectionCoordinate_restrict f x.val j
  dsimp only [boundedIntegerCoefficient]
  rw [boundedCoefficientMap_naturality, ← hc]
  apply boundedCoefficientMap_range_independent
  · intro j s
    rw [hc]
    exact boundedIntegerRange_spec S x j (f s)
  · exact boundedIntegerRange_spec S' _

/-- The coefficient construction is an actual natural transformation of
module-valued presheaves, not just a family of set maps. -/
def boundedCoefficientPresheafMap : boundedIntegerPresheaf ⟶
    ((ihom P).obj P).obj where
  app S := by
    letI : Module ℤ (((ihom P).obj P).obj.obj S) :=
      (((ihom P).obj P).obj.obj S).isModule
    let f : boundedIntegerSections S.unop →+ ((ihom P).obj P).obj.obj S :=
      AddMonoidHom.mk' (fun x => (ihomPointsIntAddEquiv P P S.unop).symm
        (boundedIntegerCoefficient S.unop x)) (by
          intro x y
          rw [boundedIntegerCoefficient_add, map_add])
    exact ModuleCat.ofHom
      { toFun := f
        map_add' := f.map_add
        map_smul' k x := map_intCast_smul f ℤ ℤ k x }
  naturality := by
    intro S T f
    ext x
    change (ihomPoints ℤ P P T.unop).symm
        (boundedIntegerCoefficient T.unop (boundedIntegerPresheaf.map f x)) =
      ((ihom P).obj P).obj.map f
        ((ihomPoints ℤ P P S.unop).symm (boundedIntegerCoefficient S.unop x))
    have h := ihomPoints_symm_comp ℤ P P T.unop S.unop f.unop
      (boundedIntegerCoefficient S.unop x)
    have h' := boundedIntegerCoefficient_naturality f.unop x
    exact (congrArg (ihomPoints ℤ P P T.unop).symm h').symm.trans h

/-- D, descended through real sheafification of the actual bounded object. -/
def boundedMeasureCoefficient : P ⊗ boundedIntegerMeasures ⟶ P :=
  MonoidalClosed.uncurry
    (((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
      boundedIntegerPresheaf ((ihom P).obj P)).symm boundedCoefficientPresheafMap)

theorem boundedMeasureCoefficient_curry_spec :
    toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf ≫
      (MonoidalClosed.curry boundedMeasureCoefficient).hom = boundedCoefficientPresheafMap := by
  rw [boundedMeasureCoefficient, MonoidalClosed.curry_uncurry]
  exact (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
    boundedIntegerPresheaf ((ihom P).obj P) |>.apply_symm_apply _

/-- D agrees with the concrete coefficient selector map on every actual
bounded test section. This is the required descent comparison. -/
theorem boundedMeasureCoefficient_on_section (S : LightProfinite)
    (x : boundedIntegerSections S) :
    (P ◁ boundedFreeSection S x) ≫ boundedMeasureCoefficient =
      boundedIntegerCoefficient S x := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_left]
  apply (freeSectionEquiv S ((ihom P).obj P)).injective
  rw [freeSectionEquiv_comp, boundedFreeSection, Equiv.apply_symm_apply]
  change (MonoidalClosed.curry boundedMeasureCoefficient).hom.app (op S)
      ((toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf).app (op S) x) =
    boundedCoefficientPresheafMap.app (op S) x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app boundedMeasureCoefficient_curry_spec (op S)) x

theorem boundedMeasureCoefficient_on_family (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    (P ◁ boundedFamilyMap S c F hF) ≫ boundedMeasureCoefficient =
      boundedCoefficientMap S c F := by
  rw [boundedFamilyMap, boundedMeasureCoefficient_on_section]
  have hc : boundedIntegerCoordinates S (boundedFamilySection S c F hF) = c := by
    funext j
    dsimp only [boundedIntegerCoordinates, boundedFamilySection]
    rw [freeSectionEquiv_coordinate]
    simp only [familyToIntegerMeasures, Pi.lift_π, AddEquiv.apply_symm_apply]
  dsimp only [boundedIntegerCoefficient]
  rw [hc]
  apply boundedCoefficientMap_range_independent
  · intro j s
    have hh := boundedIntegerRange_spec S (boundedFamilySection S c F hF) j s
    simpa only [hc] using hh
  · exact hF

end LightCondensed.Solid

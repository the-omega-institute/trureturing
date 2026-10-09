/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureComparisonBounded
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureComparisonBounded
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedCoefficientDescent
import D5.S3.HomologicalAlgebra.Solid.MeasureDiagonal
import D5.S3.HomologicalAlgebra.Solid.IntegerNullSequence
import D5.S3.HomologicalAlgebra.Solid.BinaryShiftSupplier
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
Concrete bounded inverse, dyadic integer-quotient cancellation and canonical
P-measure comparison. This is the bounded-inverse compilation unit; the
integer-quotient continuation imports it at the existing component boundary.
All new proofs are Apache-2.0. Research construction: Juan Esteban Rodriguez
Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4. Immutable formal suppliers
retain their source/commit/license identities. No DSolid realization or original
HasLeftDerivedFunctor/derived adjunction is assumed.
-/

/- Owned source component: BoundedTails.lean. -/

/-!
Actual bounded tail maps into B_Z, including the tensor square and the zeroth
section. New proofs, Apache-2.0. This is the bounded-tail construction in
Rodríguez Camargo's Notes on Solid Geometry, Lemma 3.3.3. Neither DSolid
realization nor the invertibility of the measure comparison is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

def boundedTailFamily (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ) :
    ℕ → LocallyConstant (NinfTensor S) ℤ := fun j =>
  (measureInitialCharacteristic j).comap
      (⟨Prod.fst, continuous_fst⟩ : C(NinfTensor S, ℕ∪{∞})) *
    (c j).comap (⟨Prod.snd, continuous_snd⟩ : C(NinfTensor S, S))

theorem boundedTailFamily_range (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    ∀ j x, boundedTailFamily S c j x ∈ insert 0 F := by
  rintro j ⟨a, s⟩
  cases a using OnePoint.rec
  · change measureInitialCharacteristic j ∞ * c j s ∈ insert 0 F
    rw [measureInitialCharacteristic_infty, zero_mul]
    exact Finset.mem_insert_self _ _
  · rename_i n
    change measureInitialCharacteristic j (n : ℕ∪{∞}) * c j s ∈ insert 0 F
    rw [measureInitialCharacteristic_nat]
    split_ifs <;> simp [hF j s]

def boundedTailNumerator (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    freeOn (ℕ∪{∞}) ⊗ freeOn S ⟶ boundedIntegerMeasures :=
  (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
    boundedFamilyMap (NinfTensor S) (boundedTailFamily S c) (insert 0 F)
      (boundedTailFamily_range S c F hF)

theorem boundedTailNumerator_comparison (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    boundedTailNumerator S c F hF ≫ boundedIntegerMeasuresInclusion =
      (P_proj ▷ freeOn S) ≫ measureTailMap S c := by
  apply Pi.hom_ext
  intro j
  simp only [boundedTailNumerator, Category.assoc, boundedFamilyMap_comparison,
    familyToIntegerMeasures, measureTailMap, Pi.lift_comp_π]
  apply (freeProductHomEquiv (ℕ∪{∞}) S).injective
  have hleft : freeProductHomEquiv (ℕ∪{∞}) S
      ((freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
        (freeHomIntAddEquiv (NinfTensor S)).symm (boundedTailFamily S c j)) =
      boundedTailFamily S c j := by
    dsimp only [freeProductHomEquiv]
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id, Iso.inv_hom_id_assoc]
    exact (freeHomIntAddEquiv (NinfTensor S)).apply_symm_apply _
  rw [hleft]
  ext ⟨a, s⟩
  change boundedTailFamily S c j (a, s) =
    numeratorHomEquiv S ((P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j) (a, s)
  cases a using OnePoint.rec
  · have h := (pTensorHomVanishEquiv S (measureTailCoordinate S c j)).property s
    change numeratorHomEquiv S ((pTensorHomSubtypeEquiv S
      (measureTailCoordinate S c j)).val) (∞, s) = 0 at h
    rw [pTensorHomSubtypeEquiv_apply_coe] at h
    change measureInitialCharacteristic j ∞ * c j s = _
    rw [measureInitialCharacteristic_infty, zero_mul]
    exact h.symm
  · rename_i n
    rw [← pTensorHomSubtypeEquiv_apply_coe, ← nullSeqPointsEquiv_apply,
      show nullSeqPointsEquiv S (measureTailCoordinate S c j) =
        (c j).map (measureTailSeq j) from (nullSeqPointsEquiv S).apply_symm_apply _]
    change measureInitialCharacteristic j (n : ℕ∪{∞}) * c j s =
      measureTailSeq j (c j s) n
    rw [measureInitialCharacteristic_nat, measureTailSeq_apply]
    split_ifs <;> simp

theorem boundedTailNumerator_relation (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    (P_map ▷ freeOn S) ≫ boundedTailNumerator S c F hF = 0 := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [Category.assoc, boundedTailNumerator_comparison, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight]
  simp only [P_proj, cokernel.condition]
  rw [zero_comp]
  change (tensorRight (freeOn S)).map
      (0 : freeOn (LightProfinite.of PUnit.{1}) ⟶ P) ≫ measureTailMap S c = 0
  rw [Functor.map_zero, zero_comp]

def boundedTailMap (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    P ⊗ freeOn S ⟶ boundedIntegerMeasures :=
  (tensorCokerIsoInt P_map).hom ≫
    cokernel.desc (P_map ▷ freeOn S) (boundedTailNumerator S c F hF)
      (boundedTailNumerator_relation S c F hF)

theorem P_proj_boundedTailMap (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    (P_proj ▷ freeOn S) ≫ boundedTailMap S c F hF = boundedTailNumerator S c F hF := by
  have h : (P_proj ▷ freeOn S) ≫ (tensorCokerIsoInt P_map).hom =
      cokernel.π (P_map ▷ freeOn S) := by
    have h' := congrArg (· ≫ (tensorCokerIsoInt P_map :
      P ⊗ freeOn S ≅ cokernel (P_map ▷ freeOn S)).hom)
      (tensorCokerIsoInt_π_inv (C := freeOn S))
    simpa using h'.symm
  rw [boundedTailMap, ← Category.assoc, h, cokernel.π_desc]

theorem boundedTailMap_comparison (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    boundedTailMap S c F hF ≫ boundedIntegerMeasuresInclusion = measureTailMap S c := by
  haveI : Epi (P_proj ▷ freeOn S) := by
    rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
    infer_instance
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  rw [← Category.assoc, P_proj_boundedTailMap, boundedTailNumerator_comparison]

theorem boundedTailMap_tensorSquare (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    (oneMinusShift ▷ freeOn S) ≫ boundedTailMap S c F hF =
      boundedCoefficientMap S c F ≫ PToBoundedIntegerMeasures := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [Category.assoc, boundedTailMap_comparison, Category.assoc,
    PToBoundedIntegerMeasures_comparison]
  exact boundedMeasureTensorSquare S c F hF

theorem measureTailSection_boundedTailMap (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    measureTailSection S ≫ boundedTailMap S c F hF = boundedFamilyMap S c F hF := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [Category.assoc, boundedTailMap_comparison, boundedFamilyMap_comparison]
  exact measureTailSection_tailMap S c

end LightCondensed.Solid

/- Owned source component: BoundedTailDescent.lean. -/

/-!
The genuine global bounded tail morphism F : P tensor B_Z -> B_Z.
The construction descends an additive natural module-valued presheaf map
through the actual sheafification defining B_Z. No derived realization or
measure-comparison invertibility is assumed.
New proofs, Apache-2.0; research construction: Juan Esteban Rodríguez Camargo,
Notes on Solid Geometry, Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory MonoidalClosed

namespace LightCondensed.Solid
open IntProof

local instance boundedTailDescent_proj_epi (S : LightProfinite) :
    Epi (P_proj ▷ freeOn S) := by
  rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
  infer_instance

/-- The saved null-sequence coordinates respect actual morphism addition. -/
theorem nullSeqPointsEquiv_add (S : LightProfinite)
    (f g : P ⊗ freeOn S ⟶ Zdisc) :
    nullSeqPointsEquiv S (f + g) = nullSeqPointsEquiv S f + nullSeqPointsEquiv S g := by
  ext s n
  simp only [LocallyConstant.coe_add, Pi.add_apply, Finsupp.coe_add]
  rw [nullSeqPointsEquiv_apply, nullSeqPointsEquiv_apply, nullSeqPointsEquiv_apply,
    pTensorHomSubtypeEquiv_apply_coe, pTensorHomSubtypeEquiv_apply_coe,
    pTensorHomSubtypeEquiv_apply_coe, Preadditive.comp_add]
  exact congrArg (fun a : LocallyConstant (NinfTensor S) ℤ => a ((n : ℕ∪{∞}), s))
    ((freeProductHomIntAddEquiv (ℕ∪{∞}) S).map_add _ _)

theorem measureTailCoordinate_add (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) (j : ℕ) :
    measureTailCoordinate S (c + d) j =
      measureTailCoordinate S c j + measureTailCoordinate S d j := by
  apply (nullSeqPointsEquiv S).injective
  rw [nullSeqPointsEquiv_add]
  simp only [measureTailCoordinate, Equiv.apply_symm_apply]
  ext s n
  change (if n ≤ j then c j s + d j s else 0) =
    (if n ≤ j then c j s else 0) + (if n ≤ j then d j s else 0)
  split_ifs <;> simp

theorem measureTailMap_add (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) :
    measureTailMap S (c + d) = measureTailMap S c + measureTailMap S d := by
  apply Pi.hom_ext
  intro j
  simp only [measureTailMap, Pi.lift_comp_π, Preadditive.add_comp]
  exact measureTailCoordinate_add S c d j

/-- Explicit numerator coordinates of the tail, including the infinity row. -/
theorem measureTailCoordinate_numerator (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (j : ℕ) :
    freeProductHomEquiv (ℕ∪{∞}) S
      ((P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j) = boundedTailFamily S c j := by
  ext ⟨a, s⟩
  cases a using OnePoint.rec
  · have h := (pTensorHomVanishEquiv S (measureTailCoordinate S c j)).property s
    change numeratorHomEquiv S ((pTensorHomSubtypeEquiv S
      (measureTailCoordinate S c j)).val) (∞, s) = 0 at h
    rw [pTensorHomSubtypeEquiv_apply_coe] at h
    change _ = measureInitialCharacteristic j ∞ * c j s
    rw [measureInitialCharacteristic_infty, zero_mul]
    exact h
  · rename_i n
    change numeratorHomEquiv S ((P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j)
      ((n : ℕ∪{∞}), s) = boundedTailFamily S c j ((n : ℕ∪{∞}), s)
    rw [← pTensorHomSubtypeEquiv_apply_coe, ← nullSeqPointsEquiv_apply,
      show nullSeqPointsEquiv S (measureTailCoordinate S c j) =
        (c j).map (measureTailSeq j) from (nullSeqPointsEquiv S).apply_symm_apply _]
    change measureTailSeq j (c j s) n =
      measureInitialCharacteristic j (n : ℕ∪{∞}) * c j s
    rw [measureInitialCharacteristic_nat, measureTailSeq_apply]
    split_ifs <;> simp

theorem freeProductHomEquiv_precomp_right {A S' S : LightProfinite} (f : S' ⟶ S)
    (g : freeOn A ⊗ freeOn S ⟶ Zdisc) :
    freeProductHomEquiv A S' ((freeOn A ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f) ≫ g) =
      (freeProductHomEquiv A S g).comap (𝟙 A ⊗ₘ f).hom.hom := by
  dsimp [freeProductHomEquiv]
  simp only [Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Category.assoc, freeTensorIsoInt_inv_naturality_right, Category.assoc]
  rw [freeHomDiscreteEquiv_map]

theorem measureTailMap_naturality {S' S : LightProfinite} (f : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f) ≫ measureTailMap S c =
      measureTailMap S' (pullIntegerFamily f c) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, measureTailMap, Pi.lift_comp_π]
  apply (cancel_epi (P_proj ▷ freeOn S')).1
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  apply (freeProductHomEquiv (ℕ∪{∞}) S').injective
  rw [freeProductHomEquiv_precomp_right]
  change (freeProductHomEquiv (ℕ∪{∞}) S
    ((P_proj ▷ freeOn S) ≫ measureTailCoordinate S c j)).comap
      (𝟙 (ℕ∪{∞}) ⊗ₘ f).hom.hom =
    freeProductHomEquiv (ℕ∪{∞}) S'
      ((P_proj ▷ freeOn S') ≫ measureTailCoordinate S' (pullIntegerFamily f c) j)
  rw [measureTailCoordinate_numerator, measureTailCoordinate_numerator]
  rfl

/-- The actual tail map for one bounded measure section. -/
def boundedIntegerTail (S : LightProfinite) (x : boundedIntegerSections S) :
    P ⊗ freeOn S ⟶ boundedIntegerMeasures :=
  boundedTailMap S (boundedIntegerCoordinates S x) (boundedIntegerRange S x)
    (boundedIntegerRange_spec S x)

theorem boundedIntegerTail_add (S : LightProfinite) (x y : boundedIntegerSections S) :
    boundedIntegerTail S (x + y) = boundedIntegerTail S x + boundedIntegerTail S y := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  simp only [boundedIntegerTail, boundedTailMap_comparison, Preadditive.add_comp]
  have hc : boundedIntegerCoordinates S (x + y) =
      boundedIntegerCoordinates S x + boundedIntegerCoordinates S y := by
    funext j
    exact map_add (integerSectionCoordinate S j) x.val y.val
  rw [hc, measureTailMap_add]

theorem boundedIntegerTail_naturality {S' S : LightProfinite} (f : S' ⟶ S)
    (x : boundedIntegerSections S) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f) ≫ boundedIntegerTail S x =
      boundedIntegerTail S' (boundedIntegerPresheaf.map f.op x) := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  simp only [Category.assoc, boundedIntegerTail, boundedTailMap_comparison]
  rw [measureTailMap_naturality]
  congr 1
  funext j
  exact (integerSectionCoordinate_restrict f x.val j).symm

/-- The actual additive natural presheaf map defining global F. -/
def boundedTailPresheafMap : boundedIntegerPresheaf ⟶
    ((ihom P).obj boundedIntegerMeasures).obj where
  app S := by
    letI : Module ℤ (((ihom P).obj boundedIntegerMeasures).obj.obj S) :=
      (((ihom P).obj boundedIntegerMeasures).obj.obj S).isModule
    let f : boundedIntegerSections S.unop →+
        ((ihom P).obj boundedIntegerMeasures).obj.obj S :=
      AddMonoidHom.mk' (fun x => (ihomPointsIntAddEquiv P boundedIntegerMeasures S.unop).symm
        (boundedIntegerTail S.unop x)) (by
          intro x y
          rw [boundedIntegerTail_add, map_add])
    exact ModuleCat.ofHom
      { toFun := f
        map_add' := f.map_add
        map_smul' k x := map_intCast_smul f ℤ ℤ k x }
  naturality := by
    intro S T f
    ext x
    change (ihomPoints ℤ P boundedIntegerMeasures T.unop).symm
        (boundedIntegerTail T.unop (boundedIntegerPresheaf.map f x)) =
      ((ihom P).obj boundedIntegerMeasures).obj.map f
        ((ihomPoints ℤ P boundedIntegerMeasures S.unop).symm (boundedIntegerTail S.unop x))
    have h := ihomPoints_symm_comp ℤ boundedIntegerMeasures P T.unop S.unop f.unop
      (boundedIntegerTail S.unop x)
    have h' := boundedIntegerTail_naturality f.unop x
    exact (congrArg (ihomPoints ℤ P boundedIntegerMeasures T.unop).symm h').symm.trans h

/-- The genuine condensed tail morphism on the sheafified bounded object. -/
def boundedMeasureTail : P ⊗ boundedIntegerMeasures ⟶ boundedIntegerMeasures :=
  MonoidalClosed.uncurry
    (((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
      boundedIntegerPresheaf ((ihom P).obj boundedIntegerMeasures)).symm boundedTailPresheafMap)

theorem boundedMeasureTail_curry_spec :
    toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf ≫
      (MonoidalClosed.curry boundedMeasureTail).hom = boundedTailPresheafMap := by
  rw [boundedMeasureTail, MonoidalClosed.curry_uncurry]
  exact (sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
    boundedIntegerPresheaf ((ihom P).obj boundedIntegerMeasures) |>.apply_symm_apply _

/-- F specializes to the actual tail construction on every bounded section. -/
theorem boundedMeasureTail_on_section (S : LightProfinite) (x : boundedIntegerSections S) :
    (P ◁ boundedFreeSection S x) ≫ boundedMeasureTail = boundedIntegerTail S x := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_left]
  apply (freeSectionEquiv S ((ihom P).obj boundedIntegerMeasures)).injective
  rw [freeSectionEquiv_comp, boundedFreeSection, Equiv.apply_symm_apply]
  change (MonoidalClosed.curry boundedMeasureTail).hom.app (op S)
      ((toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf).app (op S) x) =
    boundedTailPresheafMap.app (op S) x
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app boundedMeasureTail_curry_spec (op S)) x

/-- The sheafification defining B_Z permits testing actual tensor morphisms
on all bounded sections. This is used for the global tensor square below. -/
theorem boundedTensor_hom_ext {X : LightCondAb}
    {f g : P ⊗ boundedIntegerMeasures ⟶ X}
    (h : ∀ (S : LightProfinite) (x : boundedIntegerSections S),
      (P ◁ boundedFreeSection S x) ≫ f = (P ◁ boundedFreeSection S x) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply ((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
    boundedIntegerPresheaf ((ihom P).obj X)).injective
  ext S x
  have hh := congrArg (freeSectionEquiv S.unop ((ihom P).obj X))
    (congrArg MonoidalClosed.curry (h S.unop x))
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_left,
    freeSectionEquiv_comp, freeSectionEquiv_comp] at hh
  simp only [boundedFreeSection, Equiv.apply_symm_apply] at hh
  exact hh

/-- The actual global finite-difference square, now on the condensed B_Z,
not merely on individually chosen bounded families. -/
theorem boundedMeasureTail_tensorSquare :
    (oneMinusShift ▷ boundedIntegerMeasures) ≫ boundedMeasureTail =
      boundedMeasureCoefficient ≫ PToBoundedIntegerMeasures := by
  apply boundedTensor_hom_ext
  intro S x
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    boundedMeasureTail_on_section, ← Category.assoc,
    boundedMeasureCoefficient_on_section]
  exact boundedTailMap_tensorSquare S (boundedIntegerCoordinates S x)
    (boundedIntegerRange S x) (boundedIntegerRange_spec S x)

theorem boundedMeasureTail_on_family (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    (P ◁ boundedFamilyMap S c F hF) ≫ boundedMeasureTail = boundedTailMap S c F hF := by
  rw [boundedFamilyMap, boundedMeasureTail_on_section]
  have hc : boundedIntegerCoordinates S (boundedFamilySection S c F hF) = c := by
    funext j
    dsimp only [boundedIntegerCoordinates, boundedFamilySection]
    rw [freeSectionEquiv_coordinate]
    simp only [familyToIntegerMeasures, Pi.lift_comp_π, AddEquiv.apply_symm_apply]
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  simp only [boundedIntegerTail, boundedTailMap_comparison]
  rw [hc]

/-- The global tail specializes to the identity in its zeroth row on every
bounded family. This is an equality of actual condensed morphisms. -/
theorem measureTailSection_boundedMeasureTail (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    measureTailSection S ≫ (P ◁ boundedFamilyMap S c F hF) ≫ boundedMeasureTail =
      boundedFamilyMap S c F hF := by
  rw [boundedMeasureTail_on_family, measureTailSection_boundedTailMap]

end LightCondensed.Solid

/- Owned source component: BoundedInverseIdentity.lean. -/

/-!
The actual second bounded-inverse identity D(1 tensor q)=F_P(t tensor P).
The closed-cover supplier proves the comparison in protected P itself.
No injectivity of its integer-measure map is assumed.
New proofs, Apache-2.0; research construction: Juan Esteban Rodríguez Camargo,
Notes on Solid Geometry, Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

@[reassoc] theorem P_proj_PToBoundedIntegerMeasures :
    P_proj ≫ PToBoundedIntegerMeasures = boundedMeasureNumerator := by
  simp [PToBoundedIntegerMeasures, P_homMk, P_proj]

theorem measurePTail_difference_numerator :
    (freeTensorIsoInt (ℕ∪{∞}) (ℕ∪{∞})).inv ≫
      (oneMinusShift' ▷ freeOn (ℕ∪{∞})) ≫ measurePTailNumerator =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measureDiagonalSelector ≫ P_proj := by
  dsimp only [oneMinusShift']
  change (freeTensorIsoInt (ℕ∪{∞}) (ℕ∪{∞})).inv ≫
    ((𝟙 (freeOn (ℕ∪{∞})) - (free ℤ).map
      (lightProfiniteToLightCondSet.map LightProfinite.shift)) ▷ freeOn (ℕ∪{∞})) ≫
        measurePTailNumerator = _
  rw [sub_whiskerRight, Preadditive.sub_comp, Preadditive.comp_sub]
  simp only [id_whiskerRight, Category.id_comp, measurePTailNumerator,
    Iso.inv_hom_id_assoc]
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc]
  change
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj -
      (lightProfiniteToLightCondSet ⋙ free ℤ).map (shift ⊗ₘ 𝟙 (ℕ∪{∞})) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map measureDiagonalSelector ≫ P_proj
  rw [← Functor.map_comp_assoc]
  exact measurePointedTail_difference

/-- The actual restriction identity D(1 tensor q) = F_P(t tensor P),
proved in the protected P without any unproved measure-map injectivity. -/
theorem boundedMeasureCoefficient_unit :
    (P ◁ PToBoundedIntegerMeasures) ≫ boundedMeasureCoefficient =
      (oneMinusShift ▷ P) ≫ measurePTail := by
  haveI : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))
  haveI : Epi (P ◁ P_proj) := by
    change Epi ((tensorLeft P).map P_proj)
    infer_instance
  haveI : Epi (P_proj ▷ freeOn (ℕ∪{∞})) := by
    rw [← tensorCokerIsoInt_π_inv (C := freeOn (ℕ∪{∞}))]
    infer_instance
  apply (cancel_epi (P ◁ P_proj)).1
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    P_proj_PToBoundedIntegerMeasures]
  change (P ◁ boundedFamilyMap (ℕ∪{∞}) measureCharacteristic {0, 1} _) ≫
      boundedMeasureCoefficient = _
  rw [boundedMeasureCoefficient_on_family, boundedCoefficientMap_unitVectors]
  apply (cancel_epi (P_proj ▷ freeOn (ℕ∪{∞}))).1
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) (ℕ∪{∞})).inv).1
  rw [P_proj_coefficientSelectorMap, coefficientSelectorNumerator, Iso.inv_hom_id_assoc]
  have ht : (P_proj ▷ freeOn (ℕ∪{∞})) ≫ (P ◁ P_proj) ≫
      (oneMinusShift ▷ P) ≫ measurePTail =
    (oneMinusShift' ▷ freeOn (ℕ∪{∞})) ≫ measurePTailNumerator := by
    rw [← Category.assoc (P ◁ P_proj) (oneMinusShift ▷ P) measurePTail,
      whisker_exchange, Category.assoc]
    rw [← Category.assoc, P_proj_tensor_oneMinusShift, Category.assoc]
    rw [← Category.assoc (P_proj ▷ freeOn (ℕ∪{∞})) (P ◁ P_proj) measurePTail,
      ← MonoidalCategory.tensorHom_def, measurePTail_both_quotients]
  rw [ht, measurePTail_difference_numerator]

end LightCondensed.Solid

/- Owned source component: MeasureZeroSection.lean. -/

/-!
The natural zeroth-row section for actual condensed tensor products, and the
zeroth-row identities of the bounded and protected-P tails. This uses the
monoidal unit of the genuine protected free functor. New proofs, Apache-2.0.
CWComparison.BinaryShift is reused from the immutable independently audited
339ecc99-compatible official-pin checkpoint, with its copyright/license intact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

def measureFreePointUnitIso : (𝟙_ LightCondAb) ≅ freeOn (LightProfinite.of PUnit.{1}) :=
  Functor.Monoidal.εIso (lightProfiniteToLightCondSet ⋙ free ℤ)

/-- The genuine natural morphism e_0 tensor identity on an arbitrary object. -/
def measureTensorZeroSection (B : LightCondAb) : B ⟶ P ⊗ B :=
  (λ_ B).inv ≫ (measureFreePointUnitIso.hom ▷ B) ≫ (CWComparison.Pfinite 0 ▷ B)

theorem measureTensorZeroSection_naturality {A B : LightCondAb} (f : A ⟶ B) :
    f ≫ measureTensorZeroSection B = measureTensorZeroSection A ≫ (P ◁ f) := by
  dsimp only [measureTensorZeroSection]
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc]
  rw [← Category.assoc (𝟙_ LightCondAb ◁ f) (measureFreePointUnitIso.hom ▷ B)
    (CWComparison.Pfinite 0 ▷ B), whisker_exchange, Category.assoc]
  rw [whisker_exchange]
  simp only [Category.assoc]

/-- The free-object formula agrees with the previously proved concrete
zero slice, rather than an unrelated tensor-unit choice. -/
theorem measureTensorZeroSection_free (S : LightProfinite) :
    measureTensorZeroSection (freeOn S) = measureTailSection S := by
  let F := lightProfiniteToLightCondSet ⋙ free ℤ
  let p : (𝟙_ LightProfinite) ⟶ ℕ∪{∞} :=
    ConcreteCategory.ofHom ⟨fun _ => ((0 : ℕ) : ℕ∪{∞}), continuous_const⟩
  have hs : measureZeroSlice S = (λ_ S).inv ≫ (p ▷ S) := by ext s <;> rfl
  have hu : (λ_ (F.obj S)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj S =
      F.map (λ_ S).inv ≫ Functor.OplaxMonoidal.δ F (𝟙_ LightProfinite) S := by
    apply (cancel_mono (Functor.LaxMonoidal.μ F (𝟙_ LightProfinite) S)).1
    simpa only [Category.assoc, Functor.Monoidal.δ_μ, Category.comp_id] using
      (Functor.LaxMonoidal.left_unitality_inv F S)
  change (λ_ (F.obj S)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj S ≫
      ((F.map p ≫ P_proj) ▷ F.obj S) = _
  rw [MonoidalCategory.comp_whiskerRight, ← Category.assoc, hu, Category.assoc,
    Functor.OplaxMonoidal.δ_natural_left_assoc, ← Functor.map_comp_assoc, ← hs]
  rfl

theorem measureTensorZeroSection_P : measureTensorZeroSection P = measurePTailSection := by
  haveI : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))
  apply (cancel_epi P_proj).1
  rw [measureTensorZeroSection_naturality, measureTensorZeroSection_free]
  simp only [measurePTailSection, P_homMk, P_proj, cokernel.π_desc]
  rfl

/-- The actual protected tail has the natural zeroth-row section. -/
theorem measureTensorZeroSection_P_tail :
    measureTensorZeroSection P ≫ measurePTail = 𝟙 P := by
  rw [measureTensorZeroSection_P, measurePTailSection_tail]

theorem boundedIntegerCoordinates_section (S : LightProfinite)
    (x : boundedIntegerSections S) :
    familyToIntegerMeasures S (boundedIntegerCoordinates S x) =
      (freeSectionEquiv S integerMeasures).symm x.val := by
  apply Pi.hom_ext
  intro j
  simp only [familyToIntegerMeasures, Pi.lift_comp_π]
  apply (freeHomIntAddEquiv S).injective
  rw [AddEquiv.apply_symm_apply, ← freeSectionEquiv_coordinate, Equiv.apply_symm_apply]
  rfl

theorem boundedFreeSection_eq_family (S : LightProfinite) (x : boundedIntegerSections S) :
    boundedFreeSection S x = boundedFamilyMap S (boundedIntegerCoordinates S x)
      (boundedIntegerRange S x) (boundedIntegerRange_spec S x) := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [boundedFreeSection_comparison, boundedFamilyMap_comparison,
    boundedIntegerCoordinates_section]

/-- The global bounded tail really has zeroth row identity on sheafification. -/
theorem measureTensorZeroSection_bounded_tail :
    measureTensorZeroSection boundedIntegerMeasures ≫ boundedMeasureTail =
      𝟙 boundedIntegerMeasures := by
  apply ((sheafificationAdjunction (coherentTopology LightProfinite) (ModuleCat ℤ)).homEquiv
    boundedIntegerPresheaf boundedIntegerMeasures).injective
  ext S x
  have h : boundedFreeSection S.unop x ≫
      measureTensorZeroSection boundedIntegerMeasures ≫ boundedMeasureTail =
      boundedFreeSection S.unop x := by
    rw [← Category.assoc, measureTensorZeroSection_naturality,
      measureTensorZeroSection_free]
    rw [boundedFreeSection_eq_family]
    exact measureTailSection_boundedMeasureTail S.unop _ _ _
  have hh := congrArg (freeSectionEquiv S.unop boundedIntegerMeasures) h
  rw [freeSectionEquiv_comp] at hh
  simp only [boundedFreeSection, Equiv.apply_symm_apply] at hh
  exact hh

end LightCondensed.Solid

/- Owned source component: BoundedDerivedInverse.lean. -/

/-!
The explicit two-sided inverse of the actual bounded measure unit after the
constructed derived-local reflection. This is an unconditional computation
in Dlocal. No identification with DSolid, projective replacement, or total
left-derived existence is assumed. New proofs, Apache-2.0; research
construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits MonoidalCategory

namespace LightCondensed.Solid

local instance : solidDerivedLocalReflection.Additive :=
  solidDerivedLocalReflectionAdjunction.left_adjoint_additive

abbrev localMeasureStalk : LightCondAb ⥤ solidDerivedLocal.FullSubcategory :=
  DerivedCategory.singleFunctor LightCondAb 0 ⋙ solidDerivedLocalReflection

/-- The defining tensor map really becomes invertible in the already
constructed local reflector, by its all-roof universal property. -/
theorem localMeasureDifference_isIso (B : LightCondAb) :
    IsIso (localMeasureStalk.map (oneMinusShift ▷ B)) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  let X := (DerivedCategory.singleFunctor LightCondAb 0).obj (P ⊗ B)
  let t := (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ B)
  let e := solidDerivedLocalReflectionAdjunction.homEquiv X Y
  have h := solidTensorSingle_precomp_bijective B 0 Y.obj
  have heq : (fun g : solidDerivedLocalReflection.obj X ⟶ Y =>
      solidDerivedLocalReflection.map t ≫ g) =
    (fun g => e.symm (t ≫ e g)) := by
    funext g
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact solidDerivedLocalReflectionAdjunction.homEquiv_naturality_left t g
  change Function.Bijective (fun g : solidDerivedLocalReflection.obj X ⟶ Y =>
    solidDerivedLocalReflection.map t ≫ g)
  rw [heq]
  exact e.symm.bijective.comp (h.comp e.bijective)

local instance (B : LightCondAb) :
    IsIso (localMeasureStalk.map (oneMinusShift ▷ B)) := localMeasureDifference_isIso B

def localPToBoundedIntegerMeasures :
    localMeasureStalk.obj P ⟶ localMeasureStalk.obj boundedIntegerMeasures :=
  localMeasureStalk.map PToBoundedIntegerMeasures

/-- The concrete inverse: zeroth row, inverse finite difference, coefficient. -/
def localBoundedMeasureInverse :
    localMeasureStalk.obj boundedIntegerMeasures ⟶ localMeasureStalk.obj P :=
  localMeasureStalk.map (measureTensorZeroSection boundedIntegerMeasures) ≫
    inv (localMeasureStalk.map (oneMinusShift ▷ boundedIntegerMeasures)) ≫
      localMeasureStalk.map boundedMeasureCoefficient

theorem localBoundedMeasureInverse_unit :
    localBoundedMeasureInverse ≫ localPToBoundedIntegerMeasures =
      𝟙 (localMeasureStalk.obj boundedIntegerMeasures) := by
  dsimp only [localBoundedMeasureInverse, localPToBoundedIntegerMeasures]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← boundedMeasureTail_tensorSquare, Functor.map_comp,
    IsIso.inv_hom_id_assoc, ← Functor.map_comp,
    measureTensorZeroSection_bounded_tail, CategoryTheory.Functor.map_id]

theorem localBoundedMeasureUnit_inverse :
    localPToBoundedIntegerMeasures ≫ localBoundedMeasureInverse =
      𝟙 (localMeasureStalk.obj P) := by
  have ht : localMeasureStalk.map (oneMinusShift ▷ P) ≫
      localMeasureStalk.map (P ◁ PToBoundedIntegerMeasures) =
    localMeasureStalk.map (P ◁ PToBoundedIntegerMeasures) ≫
      localMeasureStalk.map (oneMinusShift ▷ boundedIntegerMeasures) := by
    simpa only [Functor.map_comp] using
      congrArg localMeasureStalk.map
        (whisker_exchange oneMinusShift PToBoundedIntegerMeasures).symm
  have hi : localMeasureStalk.map (P ◁ PToBoundedIntegerMeasures) ≫
      inv (localMeasureStalk.map (oneMinusShift ▷ boundedIntegerMeasures)) =
    inv (localMeasureStalk.map (oneMinusShift ▷ P)) ≫
      localMeasureStalk.map (P ◁ PToBoundedIntegerMeasures) := by
    apply (cancel_mono (localMeasureStalk.map (oneMinusShift ▷ boundedIntegerMeasures))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← ht]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  dsimp only [localBoundedMeasureInverse, localPToBoundedIntegerMeasures]
  rw [← Functor.map_comp_assoc, measureTensorZeroSection_naturality, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (localMeasureStalk.map (P ◁ PToBoundedIntegerMeasures))
    (inv (localMeasureStalk.map (oneMinusShift ▷ boundedIntegerMeasures)))
    (localMeasureStalk.map boundedMeasureCoefficient), hi, Category.assoc]
  rw [← Functor.map_comp, boundedMeasureCoefficient_unit, Functor.map_comp,
    IsIso.inv_hom_id_assoc, ← Functor.map_comp,
    measureTensorZeroSection_P_tail, CategoryTheory.Functor.map_id]

/-- A genuine derived-local bounded-measure equivalence, with the exact
protected unit q. This still does not identify Dlocal with DSolid. -/
def localBoundedMeasureIso : localMeasureStalk.obj P ≅
    localMeasureStalk.obj boundedIntegerMeasures where
  hom := localPToBoundedIntegerMeasures
  inv := localBoundedMeasureInverse
  hom_inv_id := localBoundedMeasureUnit_inverse
  inv_hom_id := localBoundedMeasureInverse_unit

instance localPToBoundedIntegerMeasures_isIso : IsIso localPToBoundedIntegerMeasures :=
  localBoundedMeasureIso.isIso_hom

end LightCondensed.Solid

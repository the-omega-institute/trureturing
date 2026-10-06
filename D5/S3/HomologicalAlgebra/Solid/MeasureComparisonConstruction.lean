/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureComparisonConstruction
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureComparisonConstruction
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
P-measure comparison. This is a single compilation unit for the substantive
construction, assembled from the saved owned drafts to share one import pass.
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
    familyToIntegerMeasures, measureTailMap, Pi.lift_π]
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
  simp only [measureTailMap, Pi.lift_π, Preadditive.add_comp]
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
  simp only [Category.assoc, measureTailMap, Pi.lift_π]
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
    simp only [familyToIntegerMeasures, Pi.lift_π, AddEquiv.apply_symm_apply]
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
  simp only [familyToIntegerMeasures, Pi.lift_π]
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

/- Owned source component: IntegerQuotientAction.lean. -/

/-!
Actual integer null-matrix maps into the quotient M_Z/B_Z. Uniform rounding
errors vanish through the proved bounded inclusion, giving an additive natural
condensed morphism on P tensor M_Z. No quotient vanishing or derived
realization is assumed. New proofs, Apache-2.0.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory MonoidalClosed

namespace LightCondensed.Solid
open IntProof

local instance integerQuotient_proj_epi (S : LightProfinite) : Epi (P_proj ▷ freeOn S) := by
  rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
  infer_instance

def integerMeasureQuotient : LightCondAb := cokernel boundedIntegerMeasuresInclusion

def integerMeasureQuotientπ : integerMeasures ⟶ integerMeasureQuotient :=
  cokernel.π boundedIntegerMeasuresInclusion

def integerRoundFamily (S : LightProfinite) (x : integerMeasures.obj.obj (op S)) :
    ℕ → LocallyConstant (NinfTensor S) ℤ := fun j =>
  integerBinaryRoundMatrix S (integerSectionCoordinate S j x)

/-- Each coordinate is an actual null matrix, so descends through protected P. -/
def integerRoundCoordinate (S : LightProfinite) (x : integerMeasures.obj.obj (op S))
    (j : ℕ) : P ⊗ freeOn S ⟶ Zdisc :=
  (pTensorHomVanishEquiv S).symm ⟨integerRoundFamily S x j, by
    intro s
    exact integerBinaryRoundMatrix_infty S _ s⟩

def integerRoundTensor (S : LightProfinite) (x : integerMeasures.obj.obj (op S)) :
    P ⊗ freeOn S ⟶ integerMeasures := Pi.lift (integerRoundCoordinate S x)

theorem integerRoundCoordinate_numerator (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) (j : ℕ) :
    freeProductHomEquiv (ℕ∪{∞}) S
      ((P_proj ▷ freeOn S) ≫ integerRoundCoordinate S x j) = integerRoundFamily S x j := by
  have h := congrArg Subtype.val ((pTensorHomVanishEquiv S).apply_symm_apply
    (⟨integerRoundFamily S x j, by intro s; exact integerBinaryRoundMatrix_infty S _ s⟩ :
      VanishAtInfinity S))
  change numeratorHomEquiv S ((pTensorHomSubtypeEquiv S
    (integerRoundCoordinate S x j)).val) = _ at h
  rwa [pTensorHomSubtypeEquiv_apply_coe] at h

/-- Exact computation before imposing the first infinity relation. -/
@[reassoc] theorem integerRoundTensor_prequotient (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) :
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S) ≫ integerRoundTensor S x =
      familyToIntegerMeasures (NinfTensor S) (integerRoundFamily S x) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, integerRoundTensor, familyToIntegerMeasures, Pi.lift_π]
  apply (freeHomIntAddEquiv (NinfTensor S)).injective
  change freeProductHomEquiv (ℕ∪{∞}) S
      ((P_proj ▷ freeOn S) ≫ integerRoundCoordinate S x j) = _
  rw [integerRoundCoordinate_numerator]
  exact (freeHomIntAddEquiv (NinfTensor S)).apply_symm_apply _ |>.symm

theorem familyToIntegerMeasures_add (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) :
    familyToIntegerMeasures S (c + d) =
      familyToIntegerMeasures S c + familyToIntegerMeasures S d := by
  apply Pi.hom_ext
  intro j
  simp only [familyToIntegerMeasures, Pi.lift_π, Preadditive.add_comp, Pi.add_apply]
  exact (freeHomIntAddEquiv S).symm.map_add _ _

theorem familyToIntegerMeasures_sub (S : LightProfinite)
    (c d : ℕ → LocallyConstant S ℤ) :
    familyToIntegerMeasures S (c - d) =
      familyToIntegerMeasures S c - familyToIntegerMeasures S d := by
  apply Pi.hom_ext
  intro j
  simp only [familyToIntegerMeasures, Pi.lift_π, Preadditive.sub_comp, Pi.sub_apply]
  exact (freeHomIntAddEquiv S).symm.map_sub _ _

/-- Every genuinely bounded family is killed by the actual quotient map. -/
theorem boundedFamily_quotient_zero (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    familyToIntegerMeasures S c ≫ integerMeasureQuotientπ = 0 := by
  rw [← boundedFamilyMap_comparison S c F hF, Category.assoc]
  rw [show boundedIntegerMeasuresInclusion ≫ integerMeasureQuotientπ = 0 from
    cokernel.condition boundedIntegerMeasuresInclusion, comp_zero]

def integerRoundQuotientTensor (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) : P ⊗ freeOn S ⟶ integerMeasureQuotient :=
  integerRoundTensor S x ≫ integerMeasureQuotientπ

/-- Uniform defects really factor through B_Z and vanish in its cokernel. -/
theorem integerRoundQuotientTensor_add (S : LightProfinite)
    (x y : integerMeasures.obj.obj (op S)) :
    integerRoundQuotientTensor S (x + y) =
      integerRoundQuotientTensor S x + integerRoundQuotientTensor S y := by
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S).inv).1
  simp only [integerRoundQuotientTensor, Preadditive.comp_add, Category.assoc,
    integerRoundTensor_prequotient_assoc]
  apply sub_eq_zero.mp
  let c := integerRoundFamily S (x + y) - integerRoundFamily S x - integerRoundFamily S y
  have hc : ∀ j s, c j s ∈ Finset.Icc (-2 : ℤ) 2 := by
    intro j a
    rcases a with ⟨n, s⟩
    apply Finset.mem_Icc.mpr
    change -2 ≤ _ ∧ _ ≤ 2
    rw [← abs_le]
    change |integerBinaryRoundMatrix S (integerSectionCoordinate S j (x + y)) (n, s) -
      integerBinaryRoundMatrix S (integerSectionCoordinate S j x) (n, s) -
      integerBinaryRoundMatrix S (integerSectionCoordinate S j y) (n, s)| ≤ 2
    rw [map_add]
    exact integerBinaryRoundMatrix_add_defect S _ _ n s
  have h := boundedFamily_quotient_zero (NinfTensor S) c _ hc
  simpa only [c, familyToIntegerMeasures_sub, Preadditive.sub_comp, sub_sub,
    familyToIntegerMeasures_add, Preadditive.add_comp] using h

theorem integerRoundTensor_naturality {S' S : LightProfinite} (f : S' ⟶ S)
    (x : integerMeasures.obj.obj (op S)) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f) ≫ integerRoundTensor S x =
      integerRoundTensor S' (integerMeasures.obj.map f.op x) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, integerRoundTensor, Pi.lift_π]
  apply (cancel_epi (P_proj ▷ freeOn S')).1
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  apply (freeProductHomEquiv (ℕ∪{∞}) S').injective
  rw [freeProductHomEquiv_precomp_right]
  change (freeProductHomEquiv (ℕ∪{∞}) S
    ((P_proj ▷ freeOn S) ≫ integerRoundCoordinate S x j)).comap
      (𝟙 (ℕ∪{∞}) ⊗ₘ f).hom.hom =
    freeProductHomEquiv (ℕ∪{∞}) S'
      ((P_proj ▷ freeOn S') ≫ integerRoundCoordinate S'
        (integerMeasures.obj.map f.op x) j)
  rw [integerRoundCoordinate_numerator, integerRoundCoordinate_numerator]
  ext ⟨n, s⟩
  change integerBinaryRoundSequence (integerSectionCoordinate S j x (f s)) n =
    integerBinaryRoundSequence
      (integerSectionCoordinate S' j (integerMeasures.obj.map f.op x) s) n
  rw [integerSectionCoordinate_restrict]
  rfl

/-- The projected rounding construction is genuinely additive and natural. -/
def integerRoundQuotientPresheafMap : integerMeasures.obj ⟶
    ((ihom P).obj integerMeasureQuotient).obj where
  app S := by
    letI : Module ℤ (((ihom P).obj integerMeasureQuotient).obj.obj S) :=
      (((ihom P).obj integerMeasureQuotient).obj.obj S).isModule
    let f : integerMeasures.obj.obj S →+
        ((ihom P).obj integerMeasureQuotient).obj.obj S :=
      AddMonoidHom.mk' (fun x => (ihomPointsIntAddEquiv P integerMeasureQuotient S.unop).symm
        (integerRoundQuotientTensor S.unop x)) (by
          intro x y
          rw [integerRoundQuotientTensor_add, map_add])
    exact ModuleCat.ofHom
      { toFun := f
        map_add' := f.map_add
        map_smul' k x := map_intCast_smul f ℤ ℤ k x }
  naturality := by
    intro S T f
    ext x
    change (ihomPoints ℤ P integerMeasureQuotient T.unop).symm
        (integerRoundQuotientTensor T.unop (integerMeasures.obj.map f x)) =
      ((ihom P).obj integerMeasureQuotient).obj.map f
        ((ihomPoints ℤ P integerMeasureQuotient S.unop).symm
          (integerRoundQuotientTensor S.unop x))
    have h := ihomPoints_symm_comp ℤ integerMeasureQuotient P T.unop S.unop f.unop
      (integerRoundQuotientTensor S.unop x)
    have h' : (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map f.unop) ≫
        integerRoundQuotientTensor S.unop x =
      integerRoundQuotientTensor T.unop (integerMeasures.obj.map f x) := by
      simp only [integerRoundQuotientTensor, ← Category.assoc, integerRoundTensor_naturality,
        Quiver.Hom.op_unop]
    exact (congrArg (ihomPoints ℤ P integerMeasureQuotient T.unop).symm h').symm.trans h

/-- An actual condensed morphism, after quotienting uniform rounding errors. -/
def integerMeasureRounding : P ⊗ integerMeasures ⟶ integerMeasureQuotient :=
  MonoidalClosed.uncurry ⟨integerRoundQuotientPresheafMap⟩

theorem integerMeasureRounding_on_section (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) :
    (P ◁ (freeSectionEquiv S integerMeasures).symm x) ≫ integerMeasureRounding =
      integerRoundQuotientTensor S x := by
  apply MonoidalClosed.curry_injective
  rw [MonoidalClosed.curry_natural_left, integerMeasureRounding,
    MonoidalClosed.curry_uncurry]
  apply (freeSectionEquiv S ((ihom P).obj integerMeasureQuotient)).injective
  rw [freeSectionEquiv_comp, Equiv.apply_symm_apply]
  change integerRoundQuotientPresheafMap.app (op S) x = _
  rfl

/-- Every bounded input is genuinely killed, before any derived reflection. -/
theorem integerRoundQuotientTensor_bounded (S : LightProfinite)
    (x : boundedIntegerSections S) : integerRoundQuotientTensor S x.val = 0 := by
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S).inv).1
  simp only [integerRoundQuotientTensor, Category.assoc,
    integerRoundTensor_prequotient_assoc, comp_zero]
  apply boundedFamily_quotient_zero (NinfTensor S) _
    (Finset.Icc (-(x.property.choose : ℤ)) (x.property.choose : ℤ))
  intro j a
  rcases a with ⟨n, s⟩
  apply Finset.mem_Icc.mpr
  rw [← abs_le]
  exact integerBinaryRoundMatrix_preserves_bound S _ _
    (fun s => x.property.choose_spec j s) n s

/-- The global condensed rounding morphism kills the actual sheafified
bounded object, rather than only a class of test-section representatives. -/
theorem integerMeasureRounding_bounded :
    (P ◁ boundedIntegerMeasuresInclusion) ≫ integerMeasureRounding = 0 := by
  apply boundedTensor_hom_ext
  intro S x
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
    boundedFreeSection_comparison, integerMeasureRounding_on_section,
    integerRoundQuotientTensor_bounded, comp_zero]

def integerQuotientTensorIso : P ⊗ integerMeasureQuotient ≅
    cokernel (P ◁ boundedIntegerMeasuresInclusion) :=
  preservesColimitIso (tensorLeft P) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl
      (by exact Functor.map_zero (tensorLeft P) _ _))

/-- The actual descended action P tensor (M_Z/B_Z) -> M_Z/B_Z. -/
def integerQuotientAction : P ⊗ integerMeasureQuotient ⟶ integerMeasureQuotient :=
  integerQuotientTensorIso.hom ≫
    cokernel.desc (P ◁ boundedIntegerMeasuresInclusion)
      integerMeasureRounding integerMeasureRounding_bounded

/-- Exact factorization through the quotient, with no derived premise. -/
@[reassoc] theorem integerQuotientπ_action :
    (P ◁ integerMeasureQuotientπ) ≫ integerQuotientAction = integerMeasureRounding := by
  have h : (P ◁ integerMeasureQuotientπ) ≫ integerQuotientTensorIso.hom =
      cokernel.π (P ◁ boundedIntegerMeasuresInclusion) := by
    have hi : cokernel.π (P ◁ boundedIntegerMeasuresInclusion) ≫
        integerQuotientTensorIso.inv = P ◁ integerMeasureQuotientπ := by
      simp [integerQuotientTensorIso, integerMeasureQuotientπ]
    have hh := congrArg (· ≫ integerQuotientTensorIso.hom) hi
    simpa using hh.symm
  rw [integerQuotientAction, ← Category.assoc, h, cokernel.π_desc]

end LightCondensed.Solid

/- Owned source component: IntegerQuotientIdentities.lean. -/

/-!
The binary and zeroth-row identities of the actual integer quotient action.
Uniform dyadic rounding defects are killed by the genuine bounded inclusion.
These concrete identities use no derived adjunction or realization premise.
New proofs, Apache-2.0. Binary indexing is reused from the immutable audited
CWComparison.BinaryShift source, with its original attribution preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory MonoidalClosed

namespace LightCondensed.Solid
open IntProof

local instance (S : LightProfinite) : Epi (P_proj ▷ freeOn S) := by
  rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
  infer_instance

local instance : Epi (P ◁ integerMeasureQuotientπ) := by
  change Epi ((tensorLeft P).map (cokernel.π boundedIntegerMeasuresInclusion))
  infer_instance

theorem familyToIntegerMeasures_precomp {T S : LightProfinite} (f : T ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) :
    (lightProfiniteToLightCondSet ⋙ free ℤ).map f ≫ familyToIntegerMeasures S c =
      familyToIntegerMeasures T (fun j => (c j).comap f.hom.hom) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, familyToIntegerMeasures, Pi.lift_π]
  apply (freeHomDiscreteEquiv ℤ T (ModuleCat.of ℤ ℤ)).injective
  change freeHomDiscreteEquiv ℤ T (ModuleCat.of ℤ ℤ)
    ((free ℤ).map (lightProfiniteToLightCondSet.map f) ≫
      (freeHomIntAddEquiv S).symm (c j)) = _
  rw [freeHomDiscreteEquiv_map]
  exact congrArg (fun a : LocallyConstant S ℤ => a.comap f.hom.hom)
    ((freeHomIntAddEquiv S).apply_symm_apply (c j)) |>.trans
      ((freeHomIntAddEquiv T).apply_symm_apply _).symm

@[reassoc] theorem integerRoundTensor_sequence_prequotient (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) (f : ℕ∪{∞} ⟶ ℕ∪{∞}) (hf : f ∞ = ∞) :
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S) ≫
      (CWComparison.sequencePMap f hf ▷ freeOn S) ≫ integerRoundTensor S x =
    familyToIntegerMeasures (NinfTensor S)
      (fun j => (integerRoundFamily S x j).comap (f ⊗ₘ 𝟙 S).hom.hom) := by
  rw [← Category.assoc (P_proj ▷ freeOn S)
    (CWComparison.sequencePMap f hf ▷ freeOn S) (integerRoundTensor S x),
    ← MonoidalCategory.comp_whiskerRight, CWComparison.P_proj_sequencePMap,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  change (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫
    ((free ℤ).map (lightProfiniteToLightCondSet.map f) ▷ freeOn S) ≫
      (P_proj ▷ freeOn S) ≫ integerRoundTensor S x = _
  rw [freeTensorIsoInt_inv_naturality_left_assoc, integerRoundTensor_prequotient]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (f ⊗ₘ 𝟙 S) ≫
    familyToIntegerMeasures (NinfTensor S) (integerRoundFamily S x) = _
  exact familyToIntegerMeasures_precomp (f ⊗ₘ 𝟙 S) (integerRoundFamily S x)

/-- The binary sum acts as identity on each projected test-section map. -/
theorem integerRoundQuotientTensor_binary (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) :
    ((CWComparison.PbinaryLeft + CWComparison.PbinaryRight) ▷ freeOn S) ≫
      integerRoundQuotientTensor S x = integerRoundQuotientTensor S x := by
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S).inv).1
  have hadd : ((CWComparison.PbinaryLeft + CWComparison.PbinaryRight) ▷ freeOn S) =
      (CWComparison.PbinaryLeft ▷ freeOn S) + (CWComparison.PbinaryRight ▷ freeOn S) := by
    change (tensorRight (freeOn S)).map _ =
      (tensorRight (freeOn S)).map _ + (tensorRight (freeOn S)).map _
    exact CategoryTheory.Functor.map_add (tensorRight (freeOn S))
  simp only [hadd, Preadditive.add_comp, Preadditive.comp_add,
    integerRoundQuotientTensor, Category.assoc]
  rw [integerRoundTensor_sequence_prequotient_assoc,
    integerRoundTensor_sequence_prequotient_assoc, integerRoundTensor_prequotient_assoc]
  let c := integerRoundFamily S x
  let l : ℕ → LocallyConstant (NinfTensor S) ℤ := fun j =>
    (c j).comap (CWComparison.binaryLeft ⊗ₘ 𝟙 S).hom.hom
  let r : ℕ → LocallyConstant (NinfTensor S) ℤ := fun j =>
    (c j).comap (CWComparison.binaryRight ⊗ₘ 𝟙 S).hom.hom
  have hc : ∀ j a, (l + r - c) j a ∈ Finset.Icc (-2 : ℤ) 2 := by
    rintro j ⟨n, s⟩
    apply Finset.mem_Icc.mpr
    rw [← abs_le]
    cases n using OnePoint.rec
    · change |(0 : ℤ) + 0 - 0| ≤ 2
      norm_num
    · rename_i n
      change |integerBinaryRound (integerSectionCoordinate S j x s) (2 * n + 1) +
        integerBinaryRound (integerSectionCoordinate S j x s) (2 * n + 2) -
          integerBinaryRound (integerSectionCoordinate S j x s) n| ≤ 2
      rw [abs_sub_comm]
      exact integerBinaryRound_children_defect _ n
  have h := boundedFamily_quotient_zero (NinfTensor S) (l + r - c) _ hc
  apply sub_eq_zero.mp
  simpa only [familyToIntegerMeasures_sub, familyToIntegerMeasures_add,
    Preadditive.sub_comp, Preadditive.add_comp] using h

/-- Tensor morphisms are determined on every actual free test section. -/
theorem measureTensor_hom_ext {A X : LightCondAb} {f g : P ⊗ A ⟶ X}
    (h : ∀ (S : LightProfinite) (x : A.obj.obj (op S)),
      (P ◁ (freeSectionEquiv S A).symm x) ≫ f =
        (P ◁ (freeSectionEquiv S A).symm x) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  ext S x
  have hh := congrArg (freeSectionEquiv S.unop ((ihom P).obj X))
    (congrArg MonoidalClosed.curry (h S.unop x))
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_left,
    freeSectionEquiv_comp, freeSectionEquiv_comp] at hh
  simp only [Equiv.apply_symm_apply] at hh
  exact hh

theorem integerMeasureRounding_binary :
    ((CWComparison.PbinaryLeft + CWComparison.PbinaryRight) ▷ integerMeasures) ≫
      integerMeasureRounding = integerMeasureRounding := by
  apply measureTensor_hom_ext
  intro S x
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    integerMeasureRounding_on_section]
  exact integerRoundQuotientTensor_binary S x

/-- Binary subdivision is an actual equality on the sheaf cokernel. -/
theorem integerQuotientAction_binary :
    ((CWComparison.PbinaryLeft + CWComparison.PbinaryRight) ▷ integerMeasureQuotient) ≫
      integerQuotientAction = integerQuotientAction := by
  apply (cancel_epi (P ◁ integerMeasureQuotientπ)).1
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    integerQuotientπ_action]
  exact integerMeasureRounding_binary

theorem measureTailSection_integerRoundTensor (S : LightProfinite)
    (x : integerMeasures.obj.obj (op S)) :
    measureTailSection S ≫ integerRoundTensor S x =
      (freeSectionEquiv S integerMeasures).symm x := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, integerRoundTensor, Pi.lift_π]
  apply (freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)).injective
  ext s
  dsimp only [measureTailSection]
  change freeHomDiscreteEquiv ℤ S (ModuleCat.of ℤ ℤ)
    ((free ℤ).map (lightProfiniteToLightCondSet.map (measureZeroSlice S)) ≫
      ((freeTensorIsoInt (ℕ∪{∞}) S).inv ≫
        (P_proj ▷ freeOn S) ≫ integerRoundCoordinate S x j)) s = _
  rw [freeHomDiscreteEquiv_map]
  change freeProductHomEquiv (ℕ∪{∞}) S
    ((P_proj ▷ freeOn S) ≫ integerRoundCoordinate S x j)
      (((0 : ℕ) : ℕ∪{∞}), s) = _
  rw [integerRoundCoordinate_numerator]
  change integerBinaryRound (integerSectionCoordinate S j x s) 0 = _
  rw [integerBinaryRound_zero]
  have hc := freeSectionEquiv_coordinate S
    ((freeSectionEquiv S integerMeasures).symm x) j
  have hx := congrArg (integerSectionCoordinate S j)
    ((freeSectionEquiv S integerMeasures).apply_symm_apply x)
  exact congrArg (fun a : LocallyConstant S ℤ => a s) (hx.symm.trans hc)

theorem integerMeasureRounding_zeroRow :
    measureTensorZeroSection integerMeasures ≫ integerMeasureRounding =
      integerMeasureQuotientπ := by
  ext S x
  have h : (freeSectionEquiv S.unop integerMeasures).symm x ≫
      measureTensorZeroSection integerMeasures ≫ integerMeasureRounding =
      (freeSectionEquiv S.unop integerMeasures).symm x ≫ integerMeasureQuotientπ := by
    rw [← Category.assoc, measureTensorZeroSection_naturality,
      measureTensorZeroSection_free, Category.assoc, integerMeasureRounding_on_section,
      integerRoundQuotientTensor, ← Category.assoc, measureTailSection_integerRoundTensor]
  have hh := congrArg (freeSectionEquiv S.unop integerMeasureQuotient) h
  simp only [freeSectionEquiv_comp, Equiv.apply_symm_apply] at hh
  exact hh

/-- The zeroth row of the actual descended quotient action is identity. -/
theorem integerQuotientAction_zeroRow :
    measureTensorZeroSection integerMeasureQuotient ≫ integerQuotientAction =
      𝟙 integerMeasureQuotient := by
  haveI : Epi integerMeasureQuotientπ := inferInstanceAs
    (Epi (cokernel.π boundedIntegerMeasuresInclusion))
  apply (cancel_epi integerMeasureQuotientπ).1
  rw [← Category.assoc, measureTensorZeroSection_naturality, Category.assoc,
    integerQuotientπ_action, integerMeasureRounding_zeroRow, Category.comp_id]

end LightCondensed.Solid

/- Owned source component: IntegerQuotientCancellation.lean. -/

/-!
Cancellation of the actual integer-measure quotient against every unbounded
derived-local target. The binary action is a proved concrete morphism, not
an assumption about a discrete real module. No DSolid realization is used.
New proofs, Apache-2.0; binary relations are supplied by the immutable
audited CWComparison.BinaryShift source.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits MonoidalCategory

namespace LightCondensed.Solid

def measureTensorOneSection (B : LightCondAb) : B ⟶ P ⊗ B :=
  (λ_ B).inv ≫ (measureFreePointUnitIso.hom ▷ B) ≫ (CWComparison.Pfinite 1 ▷ B)

theorem measureTensorZeroSection_binaryLeft (B : LightCondAb) :
    measureTensorZeroSection B ≫ (CWComparison.PbinaryLeft ▷ B) =
      measureTensorOneSection B := by
  dsimp only [measureTensorZeroSection, measureTensorOneSection]
  rw [Category.assoc, Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    CWComparison.Pfinite_binaryLeft]

theorem measureTensorZeroSection_difference (B : LightCondAb) :
    measureTensorZeroSection B ≫ (oneMinusShift ▷ B) =
      measureTensorZeroSection B - measureTensorOneSection B := by
  dsimp only [measureTensorZeroSection, measureTensorOneSection]
  rw [Category.assoc, Category.assoc, ← MonoidalCategory.comp_whiskerRight,
    CWComparison.Pfinite_oneMinusShift, IntProof.sub_whiskerRight,
    Preadditive.comp_sub, Preadditive.comp_sub]

/-- All maps from the actual quotient, in every integer degree, into an
arbitrary unbounded local target are zero. -/
theorem integerMeasureQuotient_to_local_zero (n : ℤ) (Y : DLightCondAb)
    [IsIso (solidDerivedEndomorphism.app Y)]
    (h : (DerivedCategory.singleFunctor LightCondAb n).obj integerMeasureQuotient ⟶ Y) :
    h = 0 := by
  let F := DerivedCategory.singleFunctor LightCondAb n
  let C := integerMeasureQuotient
  let t := oneMinusShift ▷ C
  let v := CWComparison.PbinaryLeft ▷ C
  let u := (CWComparison.PbinaryLeft + CWComparison.PbinaryRight) ▷ C
  let a := integerQuotientAction
  have hbij := solidTensorSingle_precomp_bijective C n Y
  change Function.Bijective
    (fun g : F.obj (P ⊗ C) ⟶ Y => F.map t ≫ g) at hbij
  obtain ⟨g, hg⟩ := hbij.surjective (F.map a ≫ h)
  change F.map t ≫ g = F.map a ≫ h at hg
  have hut : u ≫ t = t ≫ v := by
    dsimp only [u, t, v]
    rw [← MonoidalCategory.comp_whiskerRight, CWComparison.binary_P_subdivision,
      MonoidalCategory.comp_whiskerRight]
  have hua : u ≫ a = a := integerQuotientAction_binary
  have hv : F.map v ≫ g = g := by
    apply hbij.injective
    change F.map t ≫ (F.map v ≫ g) = F.map t ≫ g
    rw [← Category.assoc, ← Functor.map_comp, ← hut, Functor.map_comp,
      Category.assoc, hg, ← Category.assoc, ← Functor.map_comp, hua]
  have he : F.map (measureTensorZeroSection C) ≫ g =
      F.map (measureTensorOneSection C) ≫ g := by
    have hh := congrArg (fun k => F.map (measureTensorZeroSection C) ≫ k) hv
    rw [← Category.assoc, ← Functor.map_comp,
      measureTensorZeroSection_binaryLeft] at hh
    exact hh.symm
  have hz : F.map (measureTensorZeroSection C) ≫ F.map a ≫ h = 0 := by
    rw [← hg, ← Category.assoc, ← Functor.map_comp,
      measureTensorZeroSection_difference, Functor.map_sub, Preadditive.sub_comp,
      he, sub_self]
  rw [← Category.assoc, ← Functor.map_comp, integerQuotientAction_zeroRow,
    CategoryTheory.Functor.map_id, Category.id_comp] at hz
  exact hz

/-- Thus the constructed local reflector genuinely kills this quotient
in every degree, without an identification with DSolid. -/
theorem localIntegerMeasureQuotient_isZero (n : ℤ) :
    IsZero (solidDerivedLocalReflection.obj
      ((DerivedCategory.singleFunctor LightCondAb n).obj integerMeasureQuotient)) := by
  let X := (DerivedCategory.singleFunctor LightCondAb n).obj integerMeasureQuotient
  let Y := solidDerivedLocalReflection.obj X
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  have hzero : solidDerivedLocalReflectionAdjunction.unit.app X = 0 :=
    integerMeasureQuotient_to_local_zero n Y.obj _
  have hid : 𝟙 Y = 0 := by
    apply (solidDerivedLocalReflectionAdjunction.homEquiv X Y).injective
    change solidDerivedLocalReflectionAdjunction.unit.app X ≫
      solidDerivedLocal.ι.map (𝟙 Y) =
        solidDerivedLocalReflectionAdjunction.unit.app X ≫
          solidDerivedLocal.ι.map (0 : Y ⟶ Y)
    simp only [hzero, zero_comp]
  exact (IsZero.iff_id_eq_zero Y).2 hid

end LightCondensed.Solid

/- Owned source component: IntegerMeasureComparison.lean. -/

/-!
The actual integer-measure comparison for the protected P. The bounded
inverse and the short-exact triangle of B_Z -> M_Z -> M_Z/B_Z prove
invertibility in the constructed local derived category. No equivalence
with DSolid or existence of original derived solidification is assumed.
New proofs, Apache-2.0; research construction: Juan Esteban Rodríguez Camargo,
Notes on Solid Geometry, Lemmas 3.3.3--3.3.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Pretriangulated

namespace LightCondensed.Solid

def boundedIntegerMeasureSequence : ShortComplex LightCondAb :=
  ShortComplex.cokernelSequence boundedIntegerMeasuresInclusion

theorem boundedIntegerMeasureSequence_shortExact :
    boundedIntegerMeasureSequence.ShortExact := by
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.cokernelSequence_exact _
  · change Mono boundedIntegerMeasuresInclusion
    infer_instance
  · change Epi (cokernel.π boundedIntegerMeasuresInclusion)
    infer_instance

/-- The true short-exact triangle makes the bounded inclusion universal
against every arbitrary unbounded local target. -/
theorem boundedIntegerMeasuresInclusion_localPrecomp_bijective
    (Y : DLightCondAb) [IsIso (solidDerivedEndomorphism.app Y)] :
    Function.Bijective (fun g :
      (DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures ⟶ Y =>
        (DerivedCategory.singleFunctor LightCondAb 0).map
          boundedIntegerMeasuresInclusion ≫ g) := by
  let T := boundedIntegerMeasureSequence_shortExact.singleTriangle
  have hT := boundedIntegerMeasureSequence_shortExact.singleTriangle_distinguished
  have hc (g : T.obj₃ ⟶ Y) : g = 0 := integerMeasureQuotient_to_local_zero 0 Y g
  haveI : IsIso (solidDerivedEndomorphism.app (Y⟦(1 : ℤ)⟧)) :=
    by
      haveI : IsIso ((MonoidalClosed.pre oneMinusShift).mapDerivedCategory.app Y) :=
        (inferInstance : IsIso (solidDerivedEndomorphism.app Y))
      unfold solidDerivedEndomorphism
      rw [NatTrans.app_shift _ (1 : ℤ) Y]
      infer_instance
  have hshift (g : T.obj₃⟦(-1 : ℤ)⟧ ⟶ Y) : g = 0 := by
    let adj := (shiftEquiv DLightCondAb (-1 : ℤ)).toAdjunction
    let e := adj.homEquiv T.obj₃ Y
    letI : (shiftEquiv DLightCondAb (-1 : ℤ)).functor.Additive := by
      change (shiftFunctor DLightCondAb (-1 : ℤ)).Additive
      infer_instance
    apply e.injective
    exact (integerMeasureQuotient_to_local_zero 0 (Y⟦(1 : ℤ)⟧) (e g)).trans
      (adj.homAddEquiv_zero _ _).symm
  constructor
  · intro g h hgh
    change (DerivedCategory.singleFunctor LightCondAb 0).map
      boundedIntegerMeasuresInclusion ≫ g =
        (DerivedCategory.singleFunctor LightCondAb 0).map
          boundedIntegerMeasuresInclusion ≫ h at hgh
    have hz : T.mor₁ ≫ (g - h) = 0 := by
      change (DerivedCategory.singleFunctor LightCondAb 0).map
        boundedIntegerMeasuresInclusion ≫ (g - h) = 0
      rw [Preadditive.comp_sub, hgh, sub_self]
    obtain ⟨u, hu⟩ := T.yoneda_exact₂ hT (g - h) hz
    exact sub_eq_zero.mp (by rw [hu, hc u, comp_zero])
  · intro g
    obtain ⟨u, hu⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT)
      g (hshift (T.invRotate.mor₁ ≫ g))
    exact ⟨u, hu.symm⟩

theorem localBoundedIntegerMeasuresInclusion_isIso :
    IsIso (localMeasureStalk.map boundedIntegerMeasuresInclusion) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  haveI : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  let B := (DerivedCategory.singleFunctor LightCondAb 0).obj boundedIntegerMeasures
  let M := (DerivedCategory.singleFunctor LightCondAb 0).obj integerMeasures
  let f := (DerivedCategory.singleFunctor LightCondAb 0).map boundedIntegerMeasuresInclusion
  let eB := solidDerivedLocalReflectionAdjunction.homEquiv B Y
  let eM := solidDerivedLocalReflectionAdjunction.homEquiv M Y
  have hpre := boundedIntegerMeasuresInclusion_localPrecomp_bijective Y.obj
  have heq : (fun g : solidDerivedLocalReflection.obj M ⟶ Y =>
      solidDerivedLocalReflection.map f ≫ g) =
    (fun g => eB.symm (f ≫ eM g)) := by
    funext g
    apply eB.injective
    rw [Equiv.apply_symm_apply]
    exact solidDerivedLocalReflectionAdjunction.homEquiv_naturality_left f g
  change Function.Bijective (fun g : solidDerivedLocalReflection.obj M ⟶ Y =>
    solidDerivedLocalReflection.map f ≫ g)
  rw [heq]
  exact eB.symm.bijective.comp (hpre.comp eM.bijective)

/-- The exact canonical comparison is the reflected ordinary measure map
followed by the local-reflection counit at the already local integer product. -/
theorem localPToIntegerMeasures_eq :
    localPToIntegerMeasures = localMeasureStalk.map PToIntegerMeasures ≫
      solidDerivedLocalReflectionAdjunction.counit.app integerMeasuresDerivedLocal := by
  exact solidDerivedLocalReflectionAdjunction.homEquiv_counit _ _ _

/-- The required concrete P-measure computation is unconditional. It is
an equivalence in Dlocal, and does not identify Dlocal with DSolid. -/
theorem localPToIntegerMeasures_isIso : IsIso localPToIntegerMeasures := by
  haveI := localBoundedIntegerMeasuresInclusion_isIso
  haveI : IsIso (localMeasureStalk.map PToBoundedIntegerMeasures) :=
    localPToBoundedIntegerMeasures_isIso
  rw [localPToIntegerMeasures_eq, ← PToBoundedIntegerMeasures_comparison,
    Functor.map_comp]
  infer_instance

def localIntegerMeasureIso :
    solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P) ≅
      integerMeasuresDerivedLocal := by
  haveI := localPToIntegerMeasures_isIso
  exact asIso localPToIntegerMeasures

end LightCondensed.Solid

/- Actual public-root standard axiom audit, performed in this same compilation unit. -/
#print axioms LightCondensed.Solid.boundedTailFamily
#print axioms LightCondensed.Solid.boundedTailFamily_range
#print axioms LightCondensed.Solid.boundedTailNumerator
#print axioms LightCondensed.Solid.boundedTailNumerator_comparison
#print axioms LightCondensed.Solid.boundedTailNumerator_relation
#print axioms LightCondensed.Solid.boundedTailMap
#print axioms LightCondensed.Solid.P_proj_boundedTailMap
#print axioms LightCondensed.Solid.boundedTailMap_comparison
#print axioms LightCondensed.Solid.boundedTailMap_tensorSquare
#print axioms LightCondensed.Solid.measureTailSection_boundedTailMap
#print axioms LightCondensed.Solid.nullSeqPointsEquiv_add
#print axioms LightCondensed.Solid.measureTailCoordinate_add
#print axioms LightCondensed.Solid.measureTailMap_add
#print axioms LightCondensed.Solid.measureTailCoordinate_numerator
#print axioms LightCondensed.Solid.freeProductHomEquiv_precomp_right
#print axioms LightCondensed.Solid.measureTailMap_naturality
#print axioms LightCondensed.Solid.boundedIntegerTail
#print axioms LightCondensed.Solid.boundedIntegerTail_add
#print axioms LightCondensed.Solid.boundedIntegerTail_naturality
#print axioms LightCondensed.Solid.boundedTailPresheafMap
#print axioms LightCondensed.Solid.boundedMeasureTail
#print axioms LightCondensed.Solid.boundedMeasureTail_curry_spec
#print axioms LightCondensed.Solid.boundedMeasureTail_on_section
#print axioms LightCondensed.Solid.boundedTensor_hom_ext
#print axioms LightCondensed.Solid.boundedMeasureTail_tensorSquare
#print axioms LightCondensed.Solid.boundedMeasureTail_on_family
#print axioms LightCondensed.Solid.measureTailSection_boundedMeasureTail
#print axioms LightCondensed.Solid.P_proj_PToBoundedIntegerMeasures
#print axioms LightCondensed.Solid.measurePTail_difference_numerator
#print axioms LightCondensed.Solid.boundedMeasureCoefficient_unit
#print axioms LightCondensed.Solid.measureFreePointUnitIso
#print axioms LightCondensed.Solid.measureTensorZeroSection
#print axioms LightCondensed.Solid.measureTensorZeroSection_naturality
#print axioms LightCondensed.Solid.measureTensorZeroSection_free
#print axioms LightCondensed.Solid.measureTensorZeroSection_P
#print axioms LightCondensed.Solid.measureTensorZeroSection_P_tail
#print axioms LightCondensed.Solid.boundedIntegerCoordinates_section
#print axioms LightCondensed.Solid.boundedFreeSection_eq_family
#print axioms LightCondensed.Solid.measureTensorZeroSection_bounded_tail
#print axioms LightCondensed.Solid.localMeasureStalk
#print axioms LightCondensed.Solid.localMeasureDifference_isIso
#print axioms LightCondensed.Solid.localPToBoundedIntegerMeasures
#print axioms LightCondensed.Solid.localBoundedMeasureInverse
#print axioms LightCondensed.Solid.localBoundedMeasureInverse_unit
#print axioms LightCondensed.Solid.localBoundedMeasureUnit_inverse
#print axioms LightCondensed.Solid.localBoundedMeasureIso
#print axioms LightCondensed.Solid.localPToBoundedIntegerMeasures_isIso
#print axioms LightCondensed.Solid.integerMeasureQuotient
#print axioms LightCondensed.Solid.integerMeasureQuotientπ
#print axioms LightCondensed.Solid.integerRoundFamily
#print axioms LightCondensed.Solid.integerRoundCoordinate
#print axioms LightCondensed.Solid.integerRoundTensor
#print axioms LightCondensed.Solid.integerRoundCoordinate_numerator
#print axioms LightCondensed.Solid.integerRoundTensor_prequotient
#print axioms LightCondensed.Solid.familyToIntegerMeasures_add
#print axioms LightCondensed.Solid.familyToIntegerMeasures_sub
#print axioms LightCondensed.Solid.boundedFamily_quotient_zero
#print axioms LightCondensed.Solid.integerRoundQuotientTensor
#print axioms LightCondensed.Solid.integerRoundQuotientTensor_add
#print axioms LightCondensed.Solid.integerRoundTensor_naturality
#print axioms LightCondensed.Solid.integerRoundQuotientPresheafMap
#print axioms LightCondensed.Solid.integerMeasureRounding
#print axioms LightCondensed.Solid.integerMeasureRounding_on_section
#print axioms LightCondensed.Solid.integerRoundQuotientTensor_bounded
#print axioms LightCondensed.Solid.integerMeasureRounding_bounded
#print axioms LightCondensed.Solid.integerQuotientTensorIso
#print axioms LightCondensed.Solid.integerQuotientAction
#print axioms LightCondensed.Solid.integerQuotientπ_action
#print axioms LightCondensed.Solid.familyToIntegerMeasures_precomp
#print axioms LightCondensed.Solid.integerRoundTensor_sequence_prequotient
#print axioms LightCondensed.Solid.integerRoundQuotientTensor_binary
#print axioms LightCondensed.Solid.measureTensor_hom_ext
#print axioms LightCondensed.Solid.integerMeasureRounding_binary
#print axioms LightCondensed.Solid.integerQuotientAction_binary
#print axioms LightCondensed.Solid.measureTailSection_integerRoundTensor
#print axioms LightCondensed.Solid.integerMeasureRounding_zeroRow
#print axioms LightCondensed.Solid.integerQuotientAction_zeroRow
#print axioms LightCondensed.Solid.measureTensorOneSection
#print axioms LightCondensed.Solid.measureTensorZeroSection_binaryLeft
#print axioms LightCondensed.Solid.measureTensorZeroSection_difference
#print axioms LightCondensed.Solid.integerMeasureQuotient_to_local_zero
#print axioms LightCondensed.Solid.localIntegerMeasureQuotient_isZero
#print axioms LightCondensed.Solid.boundedIntegerMeasureSequence
#print axioms LightCondensed.Solid.boundedIntegerMeasureSequence_shortExact
#print axioms LightCondensed.Solid.boundedIntegerMeasuresInclusion_localPrecomp_bijective
#print axioms LightCondensed.Solid.localBoundedIntegerMeasuresInclusion_isIso
#print axioms LightCondensed.Solid.localPToIntegerMeasures_eq
#print axioms LightCondensed.Solid.localPToIntegerMeasures_isIso
#print axioms LightCondensed.Solid.localIntegerMeasureIso

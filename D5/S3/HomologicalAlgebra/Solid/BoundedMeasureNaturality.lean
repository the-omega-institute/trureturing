/- GID: D5/S3/HomologicalAlgebra/Solid/BoundedMeasureNaturality
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BoundedMeasureNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.MeasureFactorization

/-!
Naturality of the actual bounded-family lift and independence of its finite
coefficient range. New proofs, Apache-2.0. The free-tensor naturality proof is
the right-variable companion to the attributed freeTensorIsoInt proof in
DiscreteInt, using the official Mathlib monoidal APIs.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

local instance P_proj_tensor_epi (S : LightProfinite) : Epi (P_proj ▷ freeOn S) := by
  rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
  infer_instance

def pullIntegerFamily {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) : ℕ → LocallyConstant S' ℤ :=
  fun n => (c n).comap φ.hom.hom

theorem coefficientSelector_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    (𝟙 (ℕ∪{∞}) ⊗ₘ φ) ≫ coefficientSelector S c k =
      coefficientSelector S' (pullIntegerFamily φ c) k := by
  ext ⟨a, s⟩
  cases a using OnePoint.rec <;> rfl

@[reassoc] theorem freeTensorIsoInt_inv_naturality_right
    {A S' S : LightProfinite} (φ : S' ⟶ S) :
    (freeTensorIsoInt A S').inv ≫
        (freeOn A ◁ (free ℤ).map (lightProfiniteToLightCondSet.map φ)) =
      (free ℤ).map (lightProfiniteToLightCondSet.map (𝟙 A ⊗ₘ φ)) ≫
        (freeTensorIsoInt A S).inv := by
  dsimp [freeTensorIsoInt]
  simp only [Functor.Monoidal.μIso_inv, Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right]
  simp only [← Functor.map_comp_assoc]
  rw [Functor.OplaxMonoidal.δ_natural_right]
  simp [MonoidalCategory.id_tensorHom]

theorem coefficientSelectorNumerator_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    (freeOn (ℕ∪{∞}) ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
      coefficientSelectorNumerator S c k =
        coefficientSelectorNumerator S' (pullIntegerFamily φ c) k := by
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S').inv).1
  change (freeTensorIsoInt (ℕ∪{∞}) S').inv ≫
      (freeOn (ℕ∪{∞}) ◁ (free ℤ).map (lightProfiniteToLightCondSet.map φ)) ≫
        coefficientSelectorNumerator S c k = _
  rw [freeTensorIsoInt_inv_naturality_right_assoc]
  simp only [coefficientSelectorNumerator, Iso.inv_hom_id_assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (𝟙 (ℕ∪{∞}) ⊗ₘ φ) ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map (coefficientSelector S c k) ≫ P_proj = _
  rw [← Functor.map_comp_assoc, coefficientSelector_naturality]

theorem coefficientSelectorMap_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫ coefficientSelectorMap S c k =
      coefficientSelectorMap S' (pullIntegerFamily φ c) k := by
  apply (cancel_epi (P_proj ▷ freeOn S')).1
  calc
    (P_proj ▷ freeOn S') ≫ (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
        coefficientSelectorMap S c k =
      (freeOn (ℕ∪{∞}) ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
        (P_proj ▷ freeOn S) ≫ coefficientSelectorMap S c k := by
          rw [← Category.assoc, ← whisker_exchange, Category.assoc]
          rfl
    _ = (freeOn (ℕ∪{∞}) ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
        coefficientSelectorNumerator S c k := by rw [P_proj_coefficientSelectorMap]
    _ = coefficientSelectorNumerator S' (pullIntegerFamily φ c) k :=
      coefficientSelectorNumerator_naturality φ c k
    _ = (P_proj ▷ freeOn S') ≫ coefficientSelectorMap S' (pullIntegerFamily φ c) k :=
      (P_proj_coefficientSelectorMap _ _ _).symm

theorem boundedCoefficientMap_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) :
    (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫ boundedCoefficientMap S c F =
      boundedCoefficientMap S' (pullIntegerFamily φ c) F := by
  simp only [boundedCoefficientMap, Preadditive.comp_sum, Preadditive.comp_zsmul,
    coefficientSelectorMap_naturality]

theorem measureTailSection_naturality {S' S : LightProfinite} (φ : S' ⟶ S) :
    (lightProfiniteToLightCondSet ⋙ free ℤ).map φ ≫ measureTailSection S =
      measureTailSection S' ≫ (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) := by
  have hzero : φ ≫ measureZeroSlice S = measureZeroSlice S' ≫ (𝟙 (ℕ∪{∞}) ⊗ₘ φ) := by
    ext s <;> rfl
  calc
    (lightProfiniteToLightCondSet ⋙ free ℤ).map φ ≫ measureTailSection S =
      (lightProfiniteToLightCondSet ⋙ free ℤ).map (measureZeroSlice S') ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map (𝟙 (ℕ∪{∞}) ⊗ₘ φ) ≫
          (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S) := by
      dsimp only [measureTailSection]
      rw [← Functor.map_comp_assoc, hzero, Functor.map_comp]
      simp only [Category.assoc]
    _ = (lightProfiniteToLightCondSet ⋙ free ℤ).map (measureZeroSlice S') ≫
        (freeTensorIsoInt (ℕ∪{∞}) S').inv ≫
          (freeOn (ℕ∪{∞}) ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
            (P_proj ▷ freeOn S) := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun g => (lightProfiniteToLightCondSet ⋙ free ℤ).map (measureZeroSlice S') ≫
          g ≫ (P_proj ▷ freeOn S)) (freeTensorIsoInt_inv_naturality_right (A := ℕ∪{∞}) φ).symm
    _ = measureTailSection S' ≫ (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) := by
      simpa only [measureTailSection, Category.assoc, freeOn, Functor.comp_obj] using
        congrArg (fun g => (lightProfiniteToLightCondSet ⋙ free ℤ).map (measureZeroSlice S') ≫
          (freeTensorIsoInt (ℕ∪{∞}) S').inv ≫ g)
            (whisker_exchange P_proj ((lightProfiniteToLightCondSet ⋙ free ℤ).map φ))

theorem boundedTensorLocalLift_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) :
    (DerivedCategory.singleFunctor LightCondAb 0).map
        (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫ boundedTensorLocalLift S c F =
      boundedTensorLocalLift S' (pullIntegerFamily φ c) F := by
  let Y := solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P)
  have : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
  apply (solidTensorSingle_precomp_bijective (freeOn S') 0 Y.obj).injective
  change (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S') ≫
      ((DerivedCategory.singleFunctor LightCondAb 0).map
        (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫ boundedTensorLocalLift S c F) =
    (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S') ≫ _
  have hmaps : (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S') ≫
      (DerivedCategory.singleFunctor LightCondAb 0).map
        (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) =
    (DerivedCategory.singleFunctor LightCondAb 0).map
        (P ◁ (lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫
      (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S) := by
    simpa only [Functor.map_comp, freeOn, Functor.comp_obj] using
      congrArg ((DerivedCategory.singleFunctor LightCondAb 0).map)
        (whisker_exchange oneMinusShift ((lightProfiniteToLightCondSet ⋙ free ℤ).map φ)).symm
  rw [← Category.assoc, hmaps, Category.assoc, boundedTensorLocalLift_spec,
    boundedTensorLocalLift_spec, ← Functor.map_comp_assoc, boundedCoefficientMap_naturality]

/-- The actual bounded-family factorization is natural on all light profinite
test spaces. Its construction therefore covers empty and finite tests as well
as infinite ones, without a countable-enumeration assumption. -/
theorem boundedFamilyLocalLift_naturality {S' S : LightProfinite} (φ : S' ⟶ S)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) :
    (DerivedCategory.singleFunctor LightCondAb 0).map
        ((lightProfiniteToLightCondSet ⋙ free ℤ).map φ) ≫ boundedFamilyLocalLift S c F =
      boundedFamilyLocalLift S' (pullIntegerFamily φ c) F := by
  simp only [boundedFamilyLocalLift]
  rw [← Functor.map_comp_assoc, measureTailSection_naturality, Functor.map_comp,
    Category.assoc, boundedTensorLocalLift_naturality]

theorem coefficientSelectorMap_eq_zero (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (hk : ∀ n s, c n s ≠ k) :
    coefficientSelectorMap S c k = 0 := by
  have hnum : coefficientSelectorNumerator S c k = 0 := by
    let p : NinfTensor S ⟶ LightProfinite.of PUnit.{1} :=
      ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    have heq : coefficientSelector S c k = p ≫ ι := by
      ext ⟨a, s⟩
      cases a using OnePoint.rec
      · rfl
      · rename_i n
        change (if c n s = k then (n : ℕ∪{∞}) else ∞) = ∞
        simp [hk n s]
    simp only [coefficientSelectorNumerator, heq, Functor.map_comp, Category.assoc]
    change (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫ P_map ≫ P_proj = 0
    simp [P_proj]
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  rw [P_proj_coefficientSelectorMap, hnum, comp_zero]

theorem boundedCoefficientMap_range_independent (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F G : Finset ℤ)
    (hF : ∀ n s, c n s ∈ F) (hG : ∀ n s, c n s ∈ G) :
    boundedCoefficientMap S c F = boundedCoefficientMap S c G := by
  have hsub (A B : Finset ℤ) (hAB : A ⊆ B) (hA : ∀ n s, c n s ∈ A) :
      boundedCoefficientMap S c A = boundedCoefficientMap S c B := by
    apply Finset.sum_subset hAB
    intro k hk hnot
    have hk' : ∀ n s, c n s ≠ k := by
      intro n s heq
      exact hnot (heq ▸ hA n s)
    rw [coefficientSelectorMap_eq_zero S c k hk', smul_zero]
  exact (hsub F (F ∪ G) Finset.subset_union_left hF).trans
    (hsub G (F ∪ G) Finset.subset_union_right hG).symm

theorem boundedFamilyLocalLift_range_independent (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F G : Finset ℤ)
    (hF : ∀ n s, c n s ∈ F) (hG : ∀ n s, c n s ∈ G) :
    boundedFamilyLocalLift S c F = boundedFamilyLocalLift S c G := by
  have ht : boundedTensorLocalLift S c F = boundedTensorLocalLift S c G := by
    let Y := solidDerivedLocalReflection.obj ((DerivedCategory.singleFunctor LightCondAb 0).obj P)
    have : IsIso (solidDerivedEndomorphism.app Y.obj) := Y.property
    apply (solidTensorSingle_precomp_bijective (freeOn S) 0 Y.obj).injective
    change (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S) ≫ _ =
      (DerivedCategory.singleFunctor LightCondAb 0).map (oneMinusShift ▷ freeOn S) ≫ _
    rw [boundedTensorLocalLift_spec, boundedTensorLocalLift_spec,
      boundedCoefficientMap_range_independent S c F G hF hG]
  simp only [boundedFamilyLocalLift, ht]

end LightCondensed.Solid

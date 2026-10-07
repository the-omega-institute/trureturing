/- GID: D5/S3/HomologicalAlgebra/Solid/BoundedMeasures
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BoundedMeasures
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Measures
import D5.S3.HomologicalAlgebra.Solid.MeasureSelectors

/-! The actual bounded-coefficient tensor square for the protected measure map.
New proofs, Apache-2.0. This implements the uniformly bounded-family part of
Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.3. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

abbrev freeOn (S : LightProfinite) : LightCondAb := (free ℤ).obj S.toCondensed

/-- The numerator of one coefficient selector, followed by the protected quotient. -/
def coefficientSelectorNumerator (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (k : ℤ) : freeOn (ℕ∪{∞}) ⊗ freeOn S ⟶ P :=
  (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (coefficientSelector S c k) ≫ P_proj

theorem coefficientSelectorNumerator_relation (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    (P_map ▷ freeOn S) ≫ coefficientSelectorNumerator S c k = 0 := by
  apply (cancel_epi (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv).1
  dsimp only [coefficientSelectorNumerator, P_map]
  change (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv ≫
    ((free ℤ).map (lightProfiniteToLightCondSet.map ι) ▷ freeOn S) ≫
      (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map (coefficientSelector S c k) ≫ P_proj = _
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (ι ⊗ₘ 𝟙 S) ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (coefficientSelector S c k) ≫ P_proj = 0
  rw [← Functor.map_comp_assoc]
  let p : (LightProfinite.of PUnit.{1}) ⊗ S ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have heq : (ι ⊗ₘ 𝟙 S) ≫ coefficientSelector S c k = p ≫ ι := by
    ext x
    rfl
  rw [heq, Functor.map_comp, Category.assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫ P_map ≫ P_proj = 0
  simp [P_proj]

/-- Each selector vanishes at infinity, so descends through the actual P tensor quotient. -/
def coefficientSelectorMap (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (k : ℤ) : P ⊗ freeOn S ⟶ P :=
  (tensorCokerIsoInt P_map).hom ≫
    cokernel.desc (P_map ▷ freeOn S) (coefficientSelectorNumerator S c k)
      (coefficientSelectorNumerator_relation S c k)

@[reassoc (attr := simp)] theorem P_proj_coefficientSelectorMap (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) :
    (P_proj ▷ freeOn S) ≫ coefficientSelectorMap S c k =
      coefficientSelectorNumerator S c k := by
  have h := congrArg (· ≫ (tensorCokerIsoInt P_map :
      P ⊗ freeOn S ≅ cokernel (P_map ▷ freeOn S)).hom)
    (tensorCokerIsoInt_π_inv (C := freeOn S))
  have h' : (P_proj ▷ freeOn S) ≫ (tensorCokerIsoInt P_map).hom =
      cokernel.π (P_map ▷ freeOn S) := by simpa using h.symm
  dsimp only [coefficientSelectorMap]
  rw [← Category.assoc, h', cokernel.π_desc]

/-- A finite common range allows a finite, honest sum of selector morphisms. -/
def boundedCoefficientMap (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) : P ⊗ freeOn S ⟶ P :=
  ∑ k ∈ F, k • coefficientSelectorMap S c k

theorem coefficientSelectorMap_coordinate (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (k : ℤ) (j n : ℕ) (s : S) :
    nullSeqPointsEquiv S (coefficientSelectorMap S c k ≫ measureCoordinate j) s n =
      if c n s = k then (if n = j then 1 else 0) else 0 := by
  rw [nullSeqPointsEquiv_apply, pTensorHomSubtypeEquiv_apply_coe,
    P_proj_coefficientSelectorMap_assoc]
  dsimp only [numeratorHomEquiv, freeProductHomEquiv,
    coefficientSelectorNumerator]
  simp only [Equiv.trans_apply, Iso.homCongr_apply, Category.assoc, Iso.refl_hom, Category.comp_id,
    Iso.inv_hom_id_assoc, P_proj_measureCoordinate]
  change freeHomDiscreteEquiv ℤ (NinfTensor S) (ModuleCat.of ℤ ℤ)
    ((free ℤ).map (lightProfiniteToLightCondSet.map (coefficientSelector S c k)) ≫
      measureNumeratorCoordinate j) ((n : ℕ∪{∞}), s) = _
  rw [freeHomDiscreteEquiv_map]
  have hcoord : freeHomDiscreteEquiv ℤ (ℕ∪{∞}) (ModuleCat.of ℤ ℤ)
      (measureNumeratorCoordinate j) = measureCharacteristic j :=
    (freeHomIntAddEquiv (ℕ∪{∞})).apply_symm_apply _
  rw [hcoord]
  change measureCharacteristic j
    (if c n s = k then (n : ℕ∪{∞}) else ∞) = _
  by_cases hk : c n s = k
  · simpa only [if_pos hk] using measureCharacteristic_nat j n
  · simpa only [if_neg hk] using measureCharacteristic_infty j

/-- Additive structure on the saved tensor-Hom computation. -/
def freeProductHomIntAddEquiv (A S : LightProfinite) :
    (freeOn A ⊗ freeOn S ⟶ Zdisc) ≃+ LocallyConstant (A ⊗ S : LightProfinite) ℤ where
  __ := freeProductHomEquiv A S
  map_add' f g := by
    ext s
    have h := freeProductHomEquiv_sub_apply A S (f + g) g s
    simpa using eq_add_of_sub_eq (by simpa using h.symm)

theorem boundedCoefficientMap_coordinate (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ)
    (hF : ∀ n s, c n s ∈ F) (j n : ℕ) (s : S) :
    nullSeqPointsEquiv S (boundedCoefficientMap S c F ≫ measureCoordinate j) s n =
      if n = j then c n s else 0 := by
  rw [nullSeqPointsEquiv_apply, pTensorHomSubtypeEquiv_apply_coe]
  simp only [boundedCoefficientMap, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Preadditive.comp_sum, Preadditive.comp_zsmul]
  change (freeProductHomIntAddEquiv (ℕ∪{∞}) S)
    (∑ k ∈ F, k • ((P_proj ▷ freeOn S) ≫
      coefficientSelectorMap S c k ≫ measureCoordinate j)) ((n : ℕ∪{∞}), s) = _
  simp only [map_sum, map_zsmul]
  change (LocallyConstant.evalAddMonoidHom ((n : ℕ∪{∞}), s))
    (∑ k ∈ F, k • (freeProductHomIntAddEquiv (ℕ∪{∞}) S)
      ((P_proj ▷ freeOn S) ≫ coefficientSelectorMap S c k ≫ measureCoordinate j)) = _
  simp only [map_sum, map_zsmul]
  change (∑ k ∈ F, k • (freeProductHomIntAddEquiv (ℕ∪{∞}) S)
    ((P_proj ▷ freeOn S) ≫ coefficientSelectorMap S c k ≫ measureCoordinate j)
      ((n : ℕ∪{∞}), s)) = _
  have hcoord (k : ℤ) :
      freeProductHomIntAddEquiv (ℕ∪{∞}) S
        ((P_proj ▷ freeOn S) ≫ coefficientSelectorMap S c k ≫ measureCoordinate j)
        ((n : ℕ∪{∞}), s) =
          if c n s = k then (if n = j then 1 else 0) else 0 := by
    have h := coefficientSelectorMap_coordinate S c k j n s
    rw [nullSeqPointsEquiv_apply, pTensorHomSubtypeEquiv_apply_coe] at h
    exact h
  simp only [hcoord, zsmul_eq_mul]
  by_cases hnj : n = j
  · subst n
    simp [hF j s]
  · simp [hnj]

/-- Finite tails give a finitely supported sequence in the first tensor coordinate. -/
def measureTailSeq (j : ℕ) (z : ℤ) : SeqZ :=
  Finsupp.onFinset (Finset.range (j + 1))
    (fun n => if n ≤ j then z else 0) (by
      intro n hn
      by_cases hnj : n ≤ j
      · exact Finset.mem_range.mpr (by omega)
      · simp [hnj] at hn)

@[simp] theorem measureTailSeq_apply (j n : ℕ) (z : ℤ) :
    measureTailSeq j z n = if n ≤ j then z else 0 := rfl

/-- The tail projection as an actual tensor morphism, computed by the saved null-sequence API. -/
def measureTailCoordinate (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (j : ℕ) : P ⊗ freeOn S ⟶ Zdisc :=
  (nullSeqPointsEquiv S).symm ((c j).map (measureTailSeq j))

def measureTailMap (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ) :
    P ⊗ freeOn S ⟶ integerMeasures := Pi.lift (measureTailCoordinate S c)

/-- The finite difference of the tail projections lands in the actual protected P.
This is the genuine bounded-family version of the tensor square in Lemma 3.3.3. -/
theorem boundedMeasureTensorSquare (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ n s, c n s ∈ F) :
    (oneMinusShift ▷ freeOn S) ≫ measureTailMap S c =
      boundedCoefficientMap S c F ≫ PToIntegerMeasures := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, measureTailMap, Pi.lift_π,
    PToIntegerMeasures_coordinate]
  apply (nullSeqPointsEquiv S).injective
  ext s n
  rw [nullSeqPointsEquiv_oneMinusShift, boundedCoefficientMap_coordinate S c F hF]
  change (nullSeqPointsEquiv S (measureTailCoordinate S c j)) s n -
    (nullSeqPointsEquiv S (measureTailCoordinate S c j)) s (n + 1) = _
  rw [show nullSeqPointsEquiv S (measureTailCoordinate S c j) =
      (c j).map (measureTailSeq j) from (nullSeqPointsEquiv S).apply_symm_apply _]
  simp only [LocallyConstant.map]
  by_cases hnj : n = j
  · subst n
    simp
  · by_cases hlt : n < j
    · simp [hnj, Nat.le_of_lt hlt, show n + 1 ≤ j by omega]
    · simp [hnj, show ¬ n ≤ j by omega, show ¬ n + 1 ≤ j by omega]

end LightCondensed.Solid

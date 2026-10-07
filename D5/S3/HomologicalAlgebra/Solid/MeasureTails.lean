/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureTails
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureTails
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedMeasureNaturality

/-!
The actual protected-P tail map needed for the two-sided bounded-measure
inverse: F_P(e_n tensor e_j) = e_j if n <= j, and zero otherwise.
The pointed map is continuous and vanishes on both infinity fibers, so it
descends through both exact protected cokernels. Its zeroth-row section is
proved, rather than assumed. New proofs, Apache-2.0; the construction is in
Rodriguez Camargo's Notes on Solid Geometry, Lemma 3.3.3, and the checked
immutable realization response supplied by root.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory MonoidalClosed
open scoped BigOperators

namespace LightCondensed.Solid
open IntProof

local instance measureTail_proj_epi : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))

local instance measureTail_proj_tensor_epi (B : LightCondAb) : Epi (P_proj ▷ B) := by
  rw [← tensorCokerIsoInt_π_inv (C := B)]
  infer_instance

def measureInitialCharacteristic (j : ℕ) : LocallyConstant ℕ∪{∞} ℤ :=
  (truncIndex (j + 1)).map (fun i => if i = none then 0 else 1)

@[simp] theorem measureInitialCharacteristic_infty (j : ℕ) :
    measureInitialCharacteristic j ∞ = 0 := by
  simp [measureInitialCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun]

@[simp] theorem measureInitialCharacteristic_nat (j n : ℕ) :
    measureInitialCharacteristic j (n : ℕ∪{∞}) = if n ≤ j then 1 else 0 := by
  by_cases h : n < j + 1
  · have h' : n ≤ j := by omega
    simp [measureInitialCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun, h, h']
  · have h' : ¬ n ≤ j := by omega
    simp [measureInitialCharacteristic, LocallyConstant.map, truncIndex, truncIndexFun, h, h']

/-- Swap the two actual convergent-sequence variables. -/
def measureSequenceSwap : NinfTensor (ℕ∪{∞}) ⟶ NinfTensor (ℕ∪{∞}) :=
  ConcreteCategory.ofHom ⟨fun x => (x.2, x.1), continuous_snd.prodMk continuous_fst⟩

/-- The continuous pointed tail map on the actual product of convergent sequences. -/
def measurePointedTail : NinfTensor (ℕ∪{∞}) ⟶ ℕ∪{∞} :=
  measureSequenceSwap ≫ coefficientSelector (ℕ∪{∞}) measureInitialCharacteristic 1

@[simp] theorem measurePointedTail_first_infty (a : ℕ∪{∞}) :
    measurePointedTail (∞, a) = ∞ := by
  cases a using OnePoint.rec
  · rfl
  · rename_i m
    change (if measureInitialCharacteristic m ∞ = 1 then (m : ℕ∪{∞}) else ∞) = ∞
    rw [measureInitialCharacteristic_infty]
    norm_num

@[simp] theorem measurePointedTail_second_infty (a : ℕ∪{∞}) :
    measurePointedTail (a, ∞) = ∞ := rfl

theorem measurePointedTail_nat (n m : ℕ) :
    measurePointedTail ((n : ℕ∪{∞}), (m : ℕ∪{∞})) =
      if n ≤ m then (m : ℕ∪{∞}) else ∞ := by
  change (if measureInitialCharacteristic m (n : ℕ∪{∞}) = 1
    then (m : ℕ∪{∞}) else ∞) = _
  rw [measureInitialCharacteristic_nat]
  split_ifs <;> norm_num at *

theorem measurePointedTail_zeroSlice :
    measureZeroSlice (ℕ∪{∞}) ≫ measurePointedTail = 𝟙 (ℕ∪{∞}) := by
  ext a
  cases a using OnePoint.rec
  · rfl
  · rename_i m
    change measurePointedTail (((0 : ℕ) : ℕ∪{∞}), (m : ℕ∪{∞})) = (m : ℕ∪{∞})
    rw [measurePointedTail_nat, if_pos (Nat.zero_le m)]

def measurePTailNumerator : freeOn (ℕ∪{∞}) ⊗ freeOn (ℕ∪{∞}) ⟶ P :=
  (freeTensorIsoInt (ℕ∪{∞}) (ℕ∪{∞})).hom ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj

theorem measurePTailNumerator_first_relation :
    (P_map ▷ freeOn (ℕ∪{∞})) ≫ measurePTailNumerator = 0 := by
  apply (cancel_epi (freeTensorIsoInt (LightProfinite.of PUnit.{1}) (ℕ∪{∞})).inv).1
  change (freeTensorIsoInt (LightProfinite.of PUnit.{1}) (ℕ∪{∞})).inv ≫
      ((free ℤ).map (lightProfiniteToLightCondSet.map ι) ▷ freeOn (ℕ∪{∞})) ≫
        measurePTailNumerator = _
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [measurePTailNumerator, Iso.inv_hom_id_assoc]
  let p : (LightProfinite.of PUnit.{1}) ⊗ (ℕ∪{∞}) ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have h : (ι ⊗ₘ 𝟙 (ℕ∪{∞})) ≫ measurePointedTail = p ≫ ι := by
    ext x
    exact measurePointedTail_first_infty x.2
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (ι ⊗ₘ 𝟙 (ℕ∪{∞})) ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj = _
  rw [← Functor.map_comp_assoc, h, Functor.map_comp]
  simp [Category.assoc, P_map, P_proj]

def measurePTailFirstQuotient : P ⊗ freeOn (ℕ∪{∞}) ⟶ P :=
  (tensorCokerIsoInt P_map).hom ≫
    cokernel.desc (P_map ▷ freeOn (ℕ∪{∞})) measurePTailNumerator
      measurePTailNumerator_first_relation

@[reassoc (attr := simp)] theorem P_proj_measurePTailFirstQuotient :
    (P_proj ▷ freeOn (ℕ∪{∞})) ≫ measurePTailFirstQuotient = measurePTailNumerator := by
  have h := congrArg (· ≫ (tensorCokerIsoInt P_map :
      P ⊗ freeOn (ℕ∪{∞}) ≅ cokernel (P_map ▷ freeOn (ℕ∪{∞}))).hom)
    (tensorCokerIsoInt_π_inv (C := freeOn (ℕ∪{∞})))
  have h' : (P_proj ▷ freeOn (ℕ∪{∞})) ≫ (tensorCokerIsoInt P_map).hom =
      cokernel.π (P_map ▷ freeOn (ℕ∪{∞})) := by simpa using h.symm
  rw [measurePTailFirstQuotient, ← Category.assoc, h', cokernel.π_desc]

theorem measurePTailFirstQuotient_second_relation :
    (P ◁ P_map) ≫ measurePTailFirstQuotient = 0 := by
  apply (cancel_epi (P_proj ▷ freeOn (LightProfinite.of PUnit.{1}))).1
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    P_proj_measurePTailFirstQuotient]
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) (LightProfinite.of PUnit.{1})).inv).1
  change (freeTensorIsoInt (ℕ∪{∞}) (LightProfinite.of PUnit.{1})).inv ≫
      (freeOn (ℕ∪{∞}) ◁ (free ℤ).map (lightProfiniteToLightCondSet.map ι)) ≫
        measurePTailNumerator = _
  rw [freeTensorIsoInt_inv_naturality_right_assoc]
  simp only [measurePTailNumerator, Iso.inv_hom_id_assoc]
  let p : (ℕ∪{∞}) ⊗ (LightProfinite.of PUnit.{1}) ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have h : (𝟙 (ℕ∪{∞}) ⊗ₘ ι) ≫ measurePointedTail = p ≫ ι := by
    ext x
    exact measurePointedTail_second_infty x.1
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (𝟙 (ℕ∪{∞}) ⊗ₘ ι) ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj = _
  rw [← Functor.map_comp_assoc, h, Functor.map_comp]
  simp [Category.assoc, P_map, P_proj]

/-- The left-tensor cokernel comparison, used here to impose the second
protected quotient. This is the left-tensor companion of tensorCokerIsoInt. -/
def measureLeftTensorCokerIso :
    P ⊗ cokernel P_map ≅ cokernel (P ◁ P_map) :=
  preservesColimitIso (tensorLeft P) _ ≪≫
    HasColimit.isoOfNatIso (parallelPair.ext (Iso.refl _) (Iso.refl _) rfl
      (by exact Functor.map_zero (tensorLeft P) _ _))

/-- The actual tail morphism on P tensor P, descending both infinity relations. -/
def measurePTail : P ⊗ P ⟶ P :=
  measureLeftTensorCokerIso.hom ≫
    cokernel.desc (P ◁ P_map) measurePTailFirstQuotient
      measurePTailFirstQuotient_second_relation

@[reassoc (attr := simp)] theorem P_proj_measurePTail :
    (P ◁ P_proj) ≫ measurePTail = measurePTailFirstQuotient := by
  have h : (P ◁ P_proj) ≫ measureLeftTensorCokerIso.hom = cokernel.π (P ◁ P_map) := by
    have hi : cokernel.π (P ◁ P_map) ≫ measureLeftTensorCokerIso.inv = P ◁ P_proj := by
      simp [measureLeftTensorCokerIso, P_proj]
    have hh := congrArg (· ≫ measureLeftTensorCokerIso.hom) hi
    simpa using hh.symm
  rw [measurePTail, ← Category.assoc, h, cokernel.π_desc]

theorem measurePTail_both_quotients :
    (P_proj ⊗ₘ P_proj) ≫ measurePTail = measurePTailNumerator := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    P_proj_measurePTail, P_proj_measurePTailFirstQuotient]

def measurePTailZeroNumerator : freeOn (ℕ∪{∞}) ⟶ P ⊗ P :=
  measureTailSection (ℕ∪{∞}) ≫ (P ◁ P_proj)

theorem measurePTailZeroNumerator_tail :
    measurePTailZeroNumerator ≫ measurePTail = P_proj := by
  simp only [measurePTailZeroNumerator, Category.assoc, P_proj_measurePTail,
    measureTailSection, P_proj_measurePTailFirstQuotient]
  simp only [measurePTailNumerator, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, measurePointedTail_zeroSlice,
    CategoryTheory.Functor.map_id, Category.id_comp]

theorem measurePTailZeroNumerator_relation : P_map ≫ measurePTailZeroNumerator = 0 := by
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map ι ≫
    (measureTailSection (ℕ∪{∞}) ≫ (P ◁ P_proj)) = 0
  rw [← Category.assoc, measureTailSection_naturality, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp]
  change measureTailSection (LightProfinite.of PUnit.{1}) ≫ P ◁ (P_map ≫ P_proj) = 0
  rw [show P_map ≫ P_proj = 0 from cokernel.condition P_map]
  change measureTailSection (LightProfinite.of PUnit.{1}) ≫
    (tensorLeft P).map (0 : freeOn (LightProfinite.of PUnit.{1}) ⟶ P) = 0
  rw [Functor.map_zero, comp_zero]

/-- The actual zeroth-row section, now defined on the protected P itself. -/
def measurePTailSection : P ⟶ P ⊗ P :=
  P_homMk _ measurePTailZeroNumerator measurePTailZeroNumerator_relation

/-- F_P epsilon_P = 1, the second inverse identity required by the bounded
measure argument. This is an actual equality of condensed morphisms. -/
theorem measurePTailSection_tail : measurePTailSection ≫ measurePTail = 𝟙 P := by
  apply (cancel_epi P_proj).1
  simp only [measurePTailSection, P_homMk, P_proj, cokernel.π_desc_assoc, Category.comp_id]
  exact measurePTailZeroNumerator_tail

end LightCondensed.Solid

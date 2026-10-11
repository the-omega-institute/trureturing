/- GID: D5/S3/HomologicalAlgebra/Solid/MeasureDiagonal
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/MeasureDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.CoefficientLinearity
import D5.S3.HomologicalAlgebra.Solid.MeasureTails

/-!
The actual diagonal/tail-difference identity, by a two-piece closed cover.
This compares morphisms into the protected P itself; no injectivity of its
map into integer measures is assumed. New proofs, Apache-2.0; research
construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry,
Lemma 3.3.3.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

abbrev measureDiagonalSelector : NinfTensor (ℕ∪{∞}) ⟶ ℕ∪{∞} :=
  coefficientSelector (ℕ∪{∞}) measureCharacteristic 1

def measureShiftedPointedTail : NinfTensor (ℕ∪{∞}) ⟶ ℕ∪{∞} :=
  (LightProfinite.shift ⊗ₘ 𝟙 (ℕ∪{∞})) ≫ measurePointedTail

/-- The pieces are closed equalizers of actual continuous pointed maps. -/
def measureTailDifferencePiece (b : Bool) : Set (NinfTensor (ℕ∪{∞})) :=
  if b then {x | measurePointedTail x = measureDiagonalSelector x ∧
    measureShiftedPointedTail x = ∞}
  else {x | measurePointedTail x = measureShiftedPointedTail x ∧
    measureDiagonalSelector x = ∞}

theorem measureTailDifferencePiece_closed (b : Bool) :
    IsClosed (measureTailDifferencePiece b) := by
  cases b
  · exact (isClosed_eq measurePointedTail.hom.hom.continuous
      measureShiftedPointedTail.hom.hom.continuous).inter
        (isClosed_eq measureDiagonalSelector.hom.hom.continuous continuous_const)
  · exact (isClosed_eq measurePointedTail.hom.hom.continuous
      measureDiagonalSelector.hom.hom.continuous).inter
        (isClosed_eq measureShiftedPointedTail.hom.hom.continuous continuous_const)

theorem measureTailDifferencePiece_cover (x : NinfTensor (ℕ∪{∞})) :
    ∃ b : Bool, x ∈ measureTailDifferencePiece b := by
  rcases x with ⟨a, s⟩
  cases a using OnePoint.rec
  · refine ⟨false, ?_⟩
    change measurePointedTail (∞, s) = measurePointedTail (∞, s) ∧
      coefficientSelector (ℕ∪{∞}) measureCharacteristic 1 (∞, s) = ∞
    exact ⟨rfl, rfl⟩
  · rename_i n
    cases s using OnePoint.rec
    · refine ⟨false, ?_⟩
      change measurePointedTail ((n : ℕ∪{∞}), ∞) =
        measurePointedTail (((n + 1 : ℕ) : ℕ∪{∞}), ∞) ∧
          (if measureCharacteristic n ∞ = 1 then (n : ℕ∪{∞}) else ∞) = ∞
      refine ⟨rfl, ?_⟩
      exact if_neg (by
        intro h
        have hc := measureCharacteristic_infty n
        exact zero_ne_one (hc.symm.trans h))
    · rename_i m
      by_cases hnm : n = m
      · subst m
        refine ⟨true, ?_⟩
        change measurePointedTail ((n : ℕ∪{∞}), (n : ℕ∪{∞})) =
          (if measureCharacteristic n (n : ℕ∪{∞}) = 1 then (n : ℕ∪{∞}) else ∞) ∧
          measurePointedTail (((n + 1 : ℕ) : ℕ∪{∞}), (n : ℕ∪{∞})) = ∞
        have hc : measureCharacteristic n (n : ℕ∪{∞}) = 1 :=
          (measureCharacteristic_nat n n).trans (if_pos rfl)
        exact ⟨(measurePointedTail_nat n n).trans (if_pos (le_refl n)) |>.trans
          (if_pos hc).symm,
          (measurePointedTail_nat (n + 1) n).trans (if_neg (by omega))⟩
      · refine ⟨false, ?_⟩
        change measurePointedTail ((n : ℕ∪{∞}), (m : ℕ∪{∞})) =
          measurePointedTail (((n + 1 : ℕ) : ℕ∪{∞}), (m : ℕ∪{∞})) ∧
          (if measureCharacteristic n (m : ℕ∪{∞}) = 1 then (n : ℕ∪{∞}) else ∞) = ∞
        have hle : n ≤ m ↔ n + 1 ≤ m := by omega
        have hc : measureCharacteristic n (m : ℕ∪{∞}) = 0 :=
          (measureCharacteristic_nat n m).trans (if_neg (Ne.symm hnm))
        refine ⟨?_, if_neg (by intro h; exact zero_ne_one (hc.symm.trans h))⟩
        exact (measurePointedTail_nat n m).trans
          ((by simp only [hle] :
            (if n ≤ m then (m : ℕ∪{∞}) else ∞) =
              (if n + 1 ≤ m then (m : ℕ∪{∞}) else ∞)).trans
            (measurePointedTail_nat (n + 1) m).symm)

/-- The diagonal identity holds in free condensed P by genuine closed-cover
joint epimorphy, not by testing coordinates of the integer-measure map. -/
theorem measurePointedTail_difference :
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj -
      (lightProfiniteToLightCondSet ⋙ free ℤ).map measureShiftedPointedTail ≫ P_proj =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map measureDiagonalSelector ≫ P_proj := by
  let E : Bool → LightProfinite := fun b => by
    let C := measureTailDifferencePiece b
    letI : CompactSpace C := isCompact_iff_compactSpace.mp
      (measureTailDifferencePiece_closed b).isCompact
    exact LightProfinite.of C
  let a : (b : Bool) → E b ⟶ NinfTensor (ℕ∪{∞}) := fun _ =>
    ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let T := CompHausLike.finiteCoproduct E
  let p : T ⟶ NinfTensor (ℕ∪{∞}) := CompHausLike.finiteCoproduct.desc E a
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨b, hb⟩ := measureTailDifferencePiece_cover x
    exact ⟨⟨b, ⟨x, hb⟩⟩, rfl⟩
  haveI := freeOnMap_epi_of_surjective p hp
  apply (cancel_epi ((lightProfiniteToLightCondSet ⋙ free ℤ).map p)).1
  apply (isColimitOfPreserves (lightProfiniteToLightCondSet ⋙ free ℤ)
    (CompHausLike.finiteCoproduct.isColimit E)).hom_ext
  rintro ⟨b⟩
  simp only [Preadditive.comp_sub]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CompHausLike.finiteCoproduct.ι E b) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫
          (lightProfiniteToLightCondSet ⋙ free ℤ).map measurePointedTail ≫ P_proj -
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CompHausLike.finiteCoproduct.ι E b) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫
          (lightProfiniteToLightCondSet ⋙ free ℤ).map measureShiftedPointedTail ≫ P_proj =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CompHausLike.finiteCoproduct.ι E b) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫
          (lightProfiniteToLightCondSet ⋙ free ℤ).map measureDiagonalSelector ≫ P_proj
  simp only [← Functor.map_comp_assoc, p, CompHausLike.finiteCoproduct.ι_desc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (a b ≫ measurePointedTail) ≫ P_proj -
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (a b ≫ measureShiftedPointedTail) ≫ P_proj =
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (a b ≫ measureDiagonalSelector) ≫ P_proj
  let z : E b ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have hz : (lightProfiniteToLightCondSet ⋙ free ℤ).map (z ≫ ι) ≫ P_proj = 0 := by
    rw [Functor.map_comp]
    simp [Category.assoc, P_map, P_proj]
  cases b
  · have ht : a false ≫ measurePointedTail = a false ≫ measureShiftedPointedTail := by
      ext x
      exact x.property.1
    have hd : a false ≫ measureDiagonalSelector = z ≫ ι := by
      ext x
      exact x.property.2
    rw [ht, sub_self, hd, hz]
  · have ht : a true ≫ measurePointedTail = a true ≫ measureDiagonalSelector := by
      ext x
      exact x.property.1
    have hs : a true ≫ measureShiftedPointedTail = z ≫ ι := by
      ext x
      exact x.property.2
    rw [ht, hs, hz, sub_zero]

/-- The coefficient map on the unit-vector family is its sole nonzero
selector, with coefficients {0,1}. -/
theorem boundedCoefficientMap_unitVectors :
    boundedCoefficientMap (ℕ∪{∞}) measureCharacteristic {0, 1} =
      coefficientSelectorMap (ℕ∪{∞}) measureCharacteristic 1 := by
  simp [boundedCoefficientMap]

end LightCondensed.Solid

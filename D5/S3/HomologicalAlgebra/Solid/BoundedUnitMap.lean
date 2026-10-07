/- GID: D5/S3/HomologicalAlgebra/Solid/BoundedUnitMap
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/BoundedUnitMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.BoundedObject

/-!
The canonical protected map q : P -> B_Z and its exact factorization of
PToIntegerMeasures. All bounded test families have actual free maps to B_Z.
New proofs, Apache-2.0; the concrete bounded intermediary is from Rodríguez
Camargo's Notes on Solid Geometry, Lemmas 3.3.3--3.3.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

theorem boundedIntegerUnit_inclusion :
    toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf ≫
      boundedIntegerMeasuresInclusion.hom = boundedIntegerPresheafInclusion := by
  change toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf ≫
    (sheafifyMap (coherentTopology LightProfinite) boundedIntegerPresheafInclusion ≫
      (isoSheafify (coherentTopology LightProfinite) integerMeasures.property).inv) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  rw [show toSheafify (coherentTopology LightProfinite) integerMeasures.obj =
    (isoSheafify (coherentTopology LightProfinite) integerMeasures.property).hom from rfl,
    Iso.hom_inv_id, Category.comp_id]

theorem freeSectionEquiv_comp (S : LightProfinite) {A B : LightCondAb}
    (f : freeOn S ⟶ A) (g : A ⟶ B) :
    freeSectionEquiv S B (f ≫ g) = g.hom.app (op S) (freeSectionEquiv S A f) := by
  let α : (coherentTopology LightProfinite).yoneda.obj S ⟶ (forget ℤ).obj A :=
    (freeForgetAdjunction ℤ).homEquiv S.toCondensed A f
  have hα : (freeForgetAdjunction ℤ).homEquiv S.toCondensed B (f ≫ g) =
      α ≫ (forget ℤ).map g :=
    (freeForgetAdjunction ℤ).homEquiv_naturality_right f g
  have h := congrArg
    (fun β : (coherentTopology LightProfinite).yoneda.obj S ⟶ (forget ℤ).obj B =>
      (coherentTopology LightProfinite).yonedaEquiv β) hα
  exact h.trans (GrothendieckTopology.yonedaEquiv_comp
    (coherentTopology LightProfinite) α ((forget ℤ).map g))

/-- The actual free map into B_Z associated with a bounded measure section. -/
def boundedFreeSection (S : LightProfinite) (x : boundedIntegerSections S) :
    freeOn S ⟶ boundedIntegerMeasures :=
  (freeSectionEquiv S boundedIntegerMeasures).symm
    ((toSheafify (coherentTopology LightProfinite) boundedIntegerPresheaf).app (op S) x)

theorem boundedFreeSection_comparison (S : LightProfinite)
    (x : boundedIntegerSections S) :
    boundedFreeSection S x ≫ boundedIntegerMeasuresInclusion =
      (freeSectionEquiv S integerMeasures).symm x.val := by
  apply (freeSectionEquiv S integerMeasures).injective
  rw [freeSectionEquiv_comp, boundedFreeSection, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app boundedIntegerUnit_inclusion (op S)) x

/-- Every uniformly bounded family is a genuine section of B_Z, with
infinitely many coordinates allowed. -/
def boundedFamilySection (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) : boundedIntegerSections S := by
  refine ⟨freeSectionEquiv S integerMeasures (familyToIntegerMeasures S c),
    F.sup Int.natAbs, ?_⟩
  intro j s
  rw [freeSectionEquiv_coordinate]
  simp only [familyToIntegerMeasures, Pi.lift_π,
    AddEquiv.apply_symm_apply]
  rw [← Int.natCast_natAbs]
  exact_mod_cast Finset.le_sup (f := Int.natAbs) (hF j s)

def boundedFamilyMap (S : LightProfinite) (c : ℕ → LocallyConstant S ℤ)
    (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) : freeOn S ⟶ boundedIntegerMeasures :=
  boundedFreeSection S (boundedFamilySection S c F hF)

theorem boundedFamilyMap_comparison (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F : Finset ℤ) (hF : ∀ j s, c j s ∈ F) :
    boundedFamilyMap S c F hF ≫ boundedIntegerMeasuresInclusion =
      familyToIntegerMeasures S c := by
  rw [boundedFamilyMap, boundedFreeSection_comparison]
  exact (freeSectionEquiv S integerMeasures).symm_apply_apply _

/-- The numerator of the unit-vector map has common coefficient range {0,1}. -/
def boundedMeasureNumerator : freeOn (ℕ∪{∞}) ⟶ boundedIntegerMeasures :=
  boundedFamilyMap (ℕ∪{∞}) measureCharacteristic {0, 1} (by
    intro j s
    cases s using OnePoint.rec
    · exact Finset.mem_insert.mpr (Or.inl (measureCharacteristic_infty j))
    · rename_i n
      rw [measureCharacteristic_nat]
      split_ifs <;> simp)

theorem boundedMeasureNumerator_comparison :
    boundedMeasureNumerator ≫ boundedIntegerMeasuresInclusion =
      P_proj ≫ PToIntegerMeasures := by
  rw [boundedMeasureNumerator, boundedFamilyMap_comparison]
  apply Pi.hom_ext
  intro j
  simp only [familyToIntegerMeasures, Pi.lift_π, Category.assoc,
    PToIntegerMeasures_coordinate, P_proj_measureCoordinate]
  rfl

theorem boundedMeasureNumerator_relation : P_map ≫ boundedMeasureNumerator = 0 := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [Category.assoc, boundedMeasureNumerator_comparison, ← Category.assoc]
  simp [P_map, P_proj]

/-- The genuine map from the exact protected cokernel P to bounded measures. -/
def PToBoundedIntegerMeasures : P ⟶ boundedIntegerMeasures :=
  P_homMk _ boundedMeasureNumerator boundedMeasureNumerator_relation

theorem PToBoundedIntegerMeasures_comparison :
    PToBoundedIntegerMeasures ≫ boundedIntegerMeasuresInclusion = PToIntegerMeasures := by
  haveI : Epi P_proj := inferInstanceAs (Epi (cokernel.π P_map))
  apply (cancel_epi P_proj).1
  simp only [PToBoundedIntegerMeasures, P_homMk, P_proj, cokernel.π_desc_assoc]
  exact boundedMeasureNumerator_comparison

/-- The ordinary maps into B_Z do not depend on a presentation of the bound. -/
theorem boundedFamilyMap_range_independent (S : LightProfinite)
    (c : ℕ → LocallyConstant S ℤ) (F G : Finset ℤ)
    (hF : ∀ j s, c j s ∈ F) (hG : ∀ j s, c j s ∈ G) :
    boundedFamilyMap S c F hF = boundedFamilyMap S c G hG := by
  apply (cancel_mono boundedIntegerMeasuresInclusion).1
  rw [boundedFamilyMap_comparison, boundedFamilyMap_comparison]

end LightCondensed.Solid

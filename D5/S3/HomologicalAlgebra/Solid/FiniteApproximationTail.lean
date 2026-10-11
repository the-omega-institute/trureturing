/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationTail
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationCoefficient

/-!
The actual tail-remainder morphism P tensor free(S) -> free(S). Its finite
row n is identity minus r_(n-1), and its infinity row is zero. Row zero is
identity minus r_0; the finite initial quotient must therefore be retained
in the final retract. No invalid enumeration or free(S)=P assertion is used.
New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry,
Lemma 3.3.2, with the finite initial contribution kept explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory Filter Topology

namespace CWSolid

def finiteApproximationPrevious : ℕ∪{∞} ⟶ ℕ∪{∞} := ConcreteCategory.ofHom {
  toFun := OnePoint.map (fun n : ℕ => n - 1)
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    have ht : Tendsto (OnePoint.some : ℕ → OnePoint ℕ) atTop (𝓝 ∞) := by
      simpa only [coclosedCompact_eq_cocompact, cocompact_eq_cofinite,
        Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))
    apply ht.comp
    refine tendsto_atTop.mpr (fun k => eventually_atTop.mpr ⟨k + 1, ?_⟩)
    intro n hn
    omega }

end CWSolid

namespace LightCondensed.Solid
open IntProof

def finiteApproximationSecondProjection (S : LightProfinite) : NinfTensor S ⟶ S :=
  ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩

def finiteApproximationPreviousFamily (S : LightProfinite) : NinfTensor S ⟶ S :=
  (CWSolid.finiteApproximationPrevious ▷ S) ≫ CWSolid.finiteApproximationFamily S

def finiteApproximationRemainderNumerator (S : LightProfinite) :
    freeOn (ℕ∪{∞}) ⊗ freeOn S ⟶ freeOn S :=
  (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
    ((lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteApproximationSecondProjection S) -
      (lightProfiniteToLightCondSet ⋙ free ℤ).map (finiteApproximationPreviousFamily S))

theorem finiteApproximationRemainderNumerator_relation (S : LightProfinite) :
    (P_map ▷ freeOn S) ≫ finiteApproximationRemainderNumerator S = 0 := by
  apply (cancel_epi (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv).1
  dsimp only [finiteApproximationRemainderNumerator, P_map]
  change (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv ≫
    ((free ℤ).map (lightProfiniteToLightCondSet.map ι) ▷ freeOn S) ≫
      (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫ _ = _
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc, Preadditive.comp_sub, comp_zero]
  change
    (lightProfiniteToLightCondSet ⋙ free ℤ).map (ι ⊗ₘ 𝟙 S) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map
          (finiteApproximationSecondProjection S) -
      (lightProfiniteToLightCondSet ⋙ free ℤ).map (ι ⊗ₘ 𝟙 S) ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map
          (finiteApproximationPreviousFamily S) = 0
  rw [← Functor.map_comp, ← Functor.map_comp]
  have h : (ι ⊗ₘ 𝟙 S) ≫ finiteApproximationSecondProjection S =
      (ι ⊗ₘ 𝟙 S) ≫ finiteApproximationPreviousFamily S := by
    let p : (LightProfinite.of PUnit.{1}) ⊗ S ⟶ S :=
      ConcreteCategory.ofHom ⟨Prod.snd, continuous_snd⟩
    have hp : (ι ⊗ₘ 𝟙 S) ≫ (CWSolid.finiteApproximationPrevious ▷ S) =
        p ≫ CWSolid.finiteApproximationFamilySlice S ∞ := by
      ext x <;> rfl
    rw [finiteApproximationPreviousFamily, ← Category.assoc, hp, Category.assoc,
      CWSolid.finiteApproximationFamily_inftySlice, Category.comp_id]
    rfl
  rw [h, sub_self]

def finiteApproximationRemainder (S : LightProfinite) : P ⊗ freeOn S ⟶ freeOn S :=
  (tensorCokerIsoInt P_map).hom ≫
    cokernel.desc (P_map ▷ freeOn S) (finiteApproximationRemainderNumerator S)
      (finiteApproximationRemainderNumerator_relation S)

@[reassoc (attr := simp)] theorem P_proj_finiteApproximationRemainder (S : LightProfinite) :
    (P_proj ▷ freeOn S) ≫ finiteApproximationRemainder S =
      finiteApproximationRemainderNumerator S := by
  have h := congrArg (· ≫ (tensorCokerIsoInt P_map :
      P ⊗ freeOn S ≅ cokernel (P_map ▷ freeOn S)).hom)
    (tensorCokerIsoInt_π_inv (C := freeOn S))
  have h' : (P_proj ▷ freeOn S) ≫ (tensorCokerIsoInt P_map).hom =
      cokernel.π (P_map ▷ freeOn S) := by simpa using h.symm
  rw [finiteApproximationRemainder, ← Category.assoc, h', cokernel.π_desc]

def finiteApproximationRowSection (S : LightProfinite) (n : ℕ) :
    freeOn S ⟶ P ⊗ freeOn S :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (CWSolid.finiteApproximationFamilySlice S (n : OnePoint ℕ)) ≫
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫ (P_proj ▷ freeOn S)

theorem finiteApproximationRowSection_remainder (S : LightProfinite) (n : ℕ) :
    finiteApproximationRowSection S n ≫ finiteApproximationRemainder S =
      𝟙 (freeOn S) -
        (free ℤ).map (lightProfiniteToLightCondSet.map
          (CWSolid.finiteApproximation S (n - 1))) := by
  simp only [finiteApproximationRowSection, Category.assoc,
    P_proj_finiteApproximationRemainder, finiteApproximationRemainderNumerator,
    Iso.inv_hom_id_assoc, Preadditive.comp_sub]
  change
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (CWSolid.finiteApproximationFamilySlice S (n : OnePoint ℕ)) ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (finiteApproximationSecondProjection S) -
      (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (CWSolid.finiteApproximationFamilySlice S (n : OnePoint ℕ)) ≫
      (lightProfiniteToLightCondSet ⋙ free ℤ).map
        (finiteApproximationPreviousFamily S) =
      𝟙 ((lightProfiniteToLightCondSet ⋙ free ℤ).obj S) -
        (lightProfiniteToLightCondSet ⋙ free ℤ).map
          (CWSolid.finiteApproximation S (n - 1))
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hs : CWSolid.finiteApproximationFamilySlice S (n : OnePoint ℕ) ≫
      finiteApproximationSecondProjection S = 𝟙 S := by
    ext s
    rfl
  have hp : CWSolid.finiteApproximationFamilySlice S (n : OnePoint ℕ) ≫
      (CWSolid.finiteApproximationPrevious ▷ S) =
        CWSolid.finiteApproximationFamilySlice S ((n - 1 : ℕ) : OnePoint ℕ) := by
    ext s <;> rfl
  rw [hs, CategoryTheory.Functor.map_id, finiteApproximationPreviousFamily, ← Category.assoc, hp,
    CWSolid.finiteApproximationFamily_finiteSlice]

end LightCondensed.Solid

/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationCoefficient
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationSelector
import D5.S3.HomologicalAlgebra.Solid.BoundedMeasures

/-!
The actual coefficient morphism D_S : P tensor free(S) -> P for the
free-profinite generator retract. It descends the continuous representative
selector through the exact protected infinity cokernel. This is an ordinary
condensed morphism, with no realization or derived-adjunction premise.
New proofs, Apache-2.0; Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint MonoidalCategory

namespace LightCondensed.Solid
open IntProof

def finiteApproximationCoefficientSelector (S : LightProfinite) : NinfTensor S ⟶ ℕ∪{∞} :=
  CWSolid.finiteApproximationSelector S

def finiteApproximationCoefficientNumerator (S : LightProfinite) :
    freeOn (ℕ∪{∞}) ⊗ freeOn S ⟶ P :=
  (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (finiteApproximationCoefficientSelector S) ≫ P_proj

theorem finiteApproximationCoefficientNumerator_relation (S : LightProfinite) :
    (P_map ▷ freeOn S) ≫ finiteApproximationCoefficientNumerator S = 0 := by
  apply (cancel_epi (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv).1
  dsimp only [finiteApproximationCoefficientNumerator, P_map]
  change (freeTensorIsoInt (LightProfinite.of PUnit.{1}) S).inv ≫
    ((free ℤ).map (lightProfiniteToLightCondSet.map ι) ▷ freeOn S) ≫
      (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
        (lightProfiniteToLightCondSet ⋙ free ℤ).map
          (finiteApproximationCoefficientSelector S) ≫ P_proj = _
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map (ι ⊗ₘ 𝟙 S) ≫
    (lightProfiniteToLightCondSet ⋙ free ℤ).map
      (finiteApproximationCoefficientSelector S) ≫ P_proj = 0
  rw [← Functor.map_comp_assoc]
  let p : (LightProfinite.of PUnit.{1}) ⊗ S ⟶ LightProfinite.of PUnit.{1} :=
    ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  have he : (ι ⊗ₘ 𝟙 S) ≫ finiteApproximationCoefficientSelector S = p ≫ ι := by
    ext x
    rfl
  rw [he, Functor.map_comp, Category.assoc]
  change (lightProfiniteToLightCondSet ⋙ free ℤ).map p ≫ P_map ≫ P_proj = 0
  simp [P_proj]

def finiteApproximationCoefficient (S : LightProfinite) : P ⊗ freeOn S ⟶ P :=
  (tensorCokerIsoInt P_map).hom ≫
    cokernel.desc (P_map ▷ freeOn S) (finiteApproximationCoefficientNumerator S)
      (finiteApproximationCoefficientNumerator_relation S)

@[reassoc (attr := simp)] theorem P_proj_finiteApproximationCoefficient
    (S : LightProfinite) :
    (P_proj ▷ freeOn S) ≫ finiteApproximationCoefficient S =
      finiteApproximationCoefficientNumerator S := by
  have h := congrArg (· ≫ (tensorCokerIsoInt P_map :
      P ⊗ freeOn S ≅ cokernel (P_map ▷ freeOn S)).hom)
    (tensorCokerIsoInt_π_inv (C := freeOn S))
  have h' : (P_proj ▷ freeOn S) ≫ (tensorCokerIsoInt P_map).hom =
      cokernel.π (P_map ▷ freeOn S) := by simpa using h.symm
  rw [finiteApproximationCoefficient, ← Category.assoc, h', cokernel.π_desc]

end LightCondensed.Solid

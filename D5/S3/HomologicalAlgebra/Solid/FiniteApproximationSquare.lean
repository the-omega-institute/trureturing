/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximationSquare
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximationSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationDescent
import D5.S3.HomologicalAlgebra.Solid.FiniteApproximationTail
import D5.S3.HomologicalAlgebra.Solid.FiniteFreeSolid

/-!
The actual representative-difference square. Its map into the compact
parameter cover is continuous and lands in its full closure by density
of finite rows. Thus equality is of condensed morphisms, not merely
finite-point values. The zeroth row retains the finite initial quotient.
New proofs, Apache-2.0; Rodríguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits LightProfinite OnePoint LightCondensed MonoidalCategory

namespace CWSolid
open LightCondensed.Solid
open LightCondensed.Solid.IntProof

/-- The same continuous family, bundled on the actual tensor test object.
The accepted original family and its domain are kept unchanged. -/
def finiteApproximationTensorFamily (S : LightProfinite) : NinfTensor S ⟶ S :=
  ConcreteCategory.ofHom (finiteApproximationFamily S).hom.hom

def finiteApproximationDifferenceLiftAmbient (S : LightProfinite) :
    C(NinfTensor S, OnePoint ℕ × S × S) := {
  toFun := fun x => (finiteApproximationSelector S x,
    finiteApproximationFamily S x, finiteApproximationPreviousFamily S x)
  continuous_toFun := (finiteApproximationSelector S).hom.hom.continuous.prodMk
    ((finiteApproximationFamily S).hom.hom.continuous.prodMk
      (finiteApproximationPreviousFamily S).hom.hom.continuous) }

/-- Every finite row gives exactly the prescribed coded representative pair. -/
theorem finiteApproximationDifferenceLiftAmbient_finite (S : LightProfinite)
    (s₀ : S) (n : ℕ) (s : S) :
    finiteApproximationDifferenceLiftAmbient S ((n : OnePoint ℕ), s) =
      ((finiteApproximationIndexCode S ⟨n, S.proj n s⟩ : OnePoint ℕ),
        finiteApproximationDifferencePairAt S s₀
          (finiteApproximationIndexCode S ⟨n, S.proj n s⟩)) := by
  have hrow : finiteApproximationFamily S ((n : OnePoint ℕ), s) =
      finiteApproximation S n s :=
    ConcreteCategory.congr_hom (finiteApproximationFamily_finiteSlice S n) s
  have hprev : finiteApproximationPreviousFamily S ((n : OnePoint ℕ), s) =
      finiteApproximation S (n - 1) s := by
    change finiteApproximationFamily S ((n - 1 : ℕ), s) = _
    exact ConcreteCategory.congr_hom (finiteApproximationFamily_finiteSlice S (n - 1)) s
  have habsorb : finiteApproximation S (n - 1) (finiteApproximation S n s) =
      finiteApproximation S (n - 1) s := by
    exact congrArg (compatibleFiniteSection S (n - 1)).val
      (ConcreteCategory.congr_hom (finiteApproximation_projLE S (Nat.sub_le n 1)) s)
  change ((finiteApproximationIndexCode S ⟨n, S.proj n s⟩ : OnePoint ℕ),
    (finiteApproximationFamily S ((n : OnePoint ℕ), s),
      finiteApproximationPreviousFamily S ((n : OnePoint ℕ), s))) = _
  refine Prod.ext rfl ?_
  rw [finiteApproximationDifferencePairAt_code]
  change (finiteApproximationFamily S ((n : OnePoint ℕ), s),
      finiteApproximationPreviousFamily S ((n : OnePoint ℕ), s)) =
    (finiteApproximation S n s,
      finiteApproximation S (n - 1) (finiteApproximation S n s))
  exact Prod.ext hrow (hprev.trans habsorb.symm)

/-- The continuous lift lands in the actual compact closure on all rows,
including infinity; this is the substantive sheaf descent comparison. -/
theorem finiteApproximationDifferenceLiftAmbient_mem (S : LightProfinite)
    (s₀ : S) (x : NinfTensor S) :
    finiteApproximationDifferenceLiftAmbient S x ∈
      closure (Set.range (fun k : ℕ =>
        ((k : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ k))) := by
  let e : ℕ × S → NinfTensor S := fun p => ((p.1 : OnePoint ℕ), p.2)
  have he : DenseRange e := OnePoint.denseRange_coe.prodMap denseRange_id
  refine he.induction_on (p := fun y => finiteApproximationDifferenceLiftAmbient S y ∈
    closure (Set.range (fun k : ℕ =>
      ((k : OnePoint ℕ), finiteApproximationDifferencePairAt S s₀ k)))) x ?_ ?_
  · exact isClosed_closure.preimage (finiteApproximationDifferenceLiftAmbient S).continuous
  · rintro ⟨n, s⟩
    change finiteApproximationDifferenceLiftAmbient S ((n : OnePoint ℕ), s) ∈ _
    rw [finiteApproximationDifferenceLiftAmbient_finite]
    exact subset_closure ⟨finiteApproximationIndexCode S ⟨n, S.proj n s⟩, rfl⟩

def finiteApproximationDifferenceLift (S : LightProfinite) (s₀ : S) :
    NinfTensor S ⟶ finiteApproximationDifferenceSpace S s₀ :=
  ConcreteCategory.ofHom {
    toFun := fun x => ⟨finiteApproximationDifferenceLiftAmbient S x,
      finiteApproximationDifferenceLiftAmbient_mem S s₀ x⟩
    continuous_toFun := (finiteApproximationDifferenceLiftAmbient S).continuous.subtype_mk
      (fun x => finiteApproximationDifferenceLiftAmbient_mem S s₀ x) }

@[reassoc] theorem finiteApproximationDifferenceLift_projection
    (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceLift S s₀ ≫ finiteApproximationDifferenceProjection S s₀ =
      finiteApproximationCoefficientSelector S := rfl

@[reassoc] theorem finiteApproximationDifferenceLift_first
    (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceLift S s₀ ≫ finiteApproximationDifferenceFirst S s₀ =
      finiteApproximationTensorFamily S := by ext x; rfl

@[reassoc] theorem finiteApproximationDifferenceLift_second
    (S : LightProfinite) (s₀ : S) :
    finiteApproximationDifferenceLift S s₀ ≫ finiteApproximationDifferenceSecond S s₀ =
      finiteApproximationPreviousFamily S := rfl

/-- The predecessor cancels the protected successor shift, including infinity. -/
theorem finiteApproximationShiftPrevious : shift ≫ finiteApproximationPrevious =
    𝟙 (ℕ∪{∞}) := by
  ext a
  cases a using OnePoint.rec <;> rfl

end CWSolid

namespace LightCondensed.Solid
open IntProof
local notation "F" => (lightProfiniteToLightCondSet ⋙ free ℤ)

/-- The free coefficient map factors through the genuine descended sequence. -/
theorem finiteApproximationCoefficient_numerator_square
    (S : LightProfinite) (s₀ : S) :
    finiteApproximationCoefficientNumerator S ≫ finiteApproximationPMap S s₀ =
      (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
        ((F).map (CWSolid.finiteApproximationTensorFamily S) -
          (F).map (finiteApproximationPreviousFamily S)) := by
  dsimp only [finiteApproximationCoefficientNumerator]
  simp only [Category.assoc]
  rw [finiteApproximationPMap_fac,
    ← CWSolid.finiteApproximationDifferenceLift_projection S s₀,
    Functor.map_comp, Category.assoc, finiteApproximationFreeSequence_fac]
  change (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫
    (F).map (CWSolid.finiteApproximationDifferenceLift S s₀) ≫
      ((F).map (CWSolid.finiteApproximationDifferenceFirst S s₀) -
        (F).map (CWSolid.finiteApproximationDifferenceSecond S s₀)) = _
  simp only [Preadditive.comp_sub, ← Functor.map_comp,
    CWSolid.finiteApproximationDifferenceLift_first,
    CWSolid.finiteApproximationDifferenceLift_second]

/-- The actual finite-difference square, in the original ordinary category. -/
theorem finiteApproximationRemainder_square (S : LightProfinite) (s₀ : S) :
    (oneMinusShift ▷ freeOn S) ≫ finiteApproximationRemainder S =
      finiteApproximationCoefficient S ≫ finiteApproximationPMap S s₀ := by
  haveI : Epi (P_proj ▷ freeOn S) := by
    rw [← tensorCokerIsoInt_π_inv (C := freeOn S)]
    infer_instance
  apply (cancel_epi (P_proj ▷ freeOn S)).1
  rw [← Category.assoc, P_proj_tensor_oneMinusShift, Category.assoc,
    P_proj_finiteApproximationRemainder,
    ← Category.assoc, P_proj_finiteApproximationCoefficient,
    finiteApproximationCoefficient_numerator_square]
  apply (cancel_epi (freeTensorIsoInt (ℕ∪{∞}) S).inv).1
  dsimp only [oneMinusShift', finiteApproximationRemainderNumerator]
  rw [sub_whiskerRight, Preadditive.sub_comp, Preadditive.comp_sub]
  change
    (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫
        (𝟙 (freeOn (ℕ∪{∞})) ▷ freeOn S) ≫
          (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫ _ -
      (freeTensorIsoInt (ℕ∪{∞}) S).inv ≫
        ((free ℤ).map (lightProfiniteToLightCondSet.map shift) ▷ freeOn S) ≫
          (freeTensorIsoInt (ℕ∪{∞}) S).hom ≫ _ = _
  simp only [id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc]
  rw [freeTensorIsoInt_inv_naturality_left_assoc]
  simp only [Iso.inv_hom_id_assoc]
  change ((F).map (finiteApproximationSecondProjection S) -
      (F).map (finiteApproximationPreviousFamily S)) -
    (F).map (shift ⊗ₘ 𝟙 S) ≫ ((F).map (finiteApproximationSecondProjection S) -
      (F).map (finiteApproximationPreviousFamily S)) =
    (F).map (CWSolid.finiteApproximationTensorFamily S) -
      (F).map (finiteApproximationPreviousFamily S)
  rw [Preadditive.comp_sub, ← Functor.map_comp, ← Functor.map_comp]
  have hs : (shift ⊗ₘ 𝟙 S) ≫ finiteApproximationSecondProjection S =
      finiteApproximationSecondProjection S := by ext x; rfl
  have hp : (shift ⊗ₘ 𝟙 S) ≫ finiteApproximationPreviousFamily S =
      CWSolid.finiteApproximationTensorFamily S := by
    ext ⟨a, s⟩
    cases a using OnePoint.rec <;> rfl
  rw [hs, hp]
  abel

end LightCondensed.Solid

/- Fresh public-root audits of this square and its actual finite-free supplier. -/
#print axioms CWSolid.finiteApproximationTensorFamily
#print axioms CWSolid.finiteApproximationDifferenceLiftAmbient
#print axioms CWSolid.finiteApproximationDifferenceLiftAmbient_finite
#print axioms CWSolid.finiteApproximationDifferenceLiftAmbient_mem
#print axioms CWSolid.finiteApproximationDifferenceLift
#print axioms CWSolid.finiteApproximationDifferenceLift_projection
#print axioms CWSolid.finiteApproximationDifferenceLift_first
#print axioms CWSolid.finiteApproximationDifferenceLift_second
#print axioms CWSolid.finiteApproximationShiftPrevious
#print axioms LightCondensed.Solid.finiteApproximationCoefficient_numerator_square
#print axioms LightCondensed.Solid.finiteApproximationRemainder_square
#print axioms LightCondensed.Solid.freeProfinitePointIsoInt
#print axioms LightCondensed.Solid.isSolid_freeProfinitePoint
#print axioms LightCondensed.Solid.finiteProfinitePointsIso
#print axioms LightCondensed.Solid.isSolid_free_finite
#print axioms LightCondensed.Solid.isSolid_free_initialComponent

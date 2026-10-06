/- GID: D5/S3/HomologicalAlgebra/Solid/LowerTruncationLayers
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/LowerTruncationLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.UnboundedTruncationColimit
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
Copyright (c) 2026. Released under the Apache 2.0 license.
The concrete one-term filtration of the verified brutal lower truncations.
For arbitrary unbounded K, increasing the truncation cutoff by one fits
into an actual short exact sequence with the newly added coefficient as
its single-complex quotient. These are the finite cone steps used with
the actual generator resolution and the two unbounded telescopes.
Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomologicalComplex

namespace CWSolid

variable {C : Type*} [Category* C] [Abelian C]

/-- Project the newly added bottom coefficient onto its literal stalk. -/
def lowerTruncationLayerProjection (K : CochainComplex C ℤ) (m : ℕ) :
    lowerTruncation K (m + 1) ⟶
      (CochainComplex.singleFunctor C (-((m + 1 : ℕ) : ℤ))).obj
        (K.X (-((m + 1 : ℕ) : ℤ))) :=
  mkHomToSingle (eqToHom (by simp [lowerTruncation])) (by
    intro i hi
    have hi' : i + 1 = -((m + 1 : ℕ) : ℤ) := hi
    have h : ¬ -((m + 1 : ℕ) : ℤ) ≤ i := by omega
    simp only [lowerTruncation, dif_neg h, zero_comp])

@[simp] theorem lowerTruncationLayerProjection_f (K : CochainComplex C ℤ) (m : ℕ) :
    (lowerTruncationLayerProjection K m).f (-((m + 1 : ℕ) : ℤ)) =
      eqToHom (by simp [lowerTruncation]) ≫
        (singleObjXSelf (.up ℤ) (-((m + 1 : ℕ) : ℤ))
          (K.X (-((m + 1 : ℕ) : ℤ)))).inv := by
  exact mkHomToSingle_f _ _

private theorem lowerTruncationMap_layerProjection (K : CochainComplex C ℤ) (m : ℕ) :
    lowerTruncationMap K m (m + 1) (Nat.le_succ m) ≫
      lowerTruncationLayerProjection K m = 0 := by
  apply to_single_hom_ext
  rw [comp_f, zero_f]
  have h : ¬ -(m : ℤ) ≤ -((m + 1 : ℕ) : ℤ) := by omega
  simp [lowerTruncationMap, h]

def lowerTruncationLayerSequence (K : CochainComplex C ℤ) (m : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (lowerTruncationMap K m (m + 1) (Nat.le_succ m))
    (lowerTruncationLayerProjection K m) (lowerTruncationMap_layerProjection K m)

/-- The filtration is short exact on all integer coefficients, including
the zero coefficients below the cutoff. No boundedness of K is used. -/
theorem lowerTruncationLayerSequence_shortExact (K : CochainComplex C ℤ) (m : ℕ) :
    (lowerTruncationLayerSequence K m).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let S := (lowerTruncationLayerSequence K m).map (eval C (.up ℤ) i)
  change S.ShortExact
  by_cases hi : i = -((m + 1 : ℕ) : ℤ)
  · subst i
    have h₁ : IsZero S.X₁ := by
      change IsZero ((lowerTruncation K m).X (-((m + 1 : ℕ) : ℤ)))
      simp only [lowerTruncation, if_neg (show ¬ -(m : ℤ) ≤ -((m + 1 : ℕ) : ℤ) by omega)]
      exact isZero_zero C
    haveI : Mono S.f := h₁.mono _
    haveI : IsIso S.g := by
      change IsIso ((lowerTruncationLayerProjection K m).f (-((m + 1 : ℕ) : ℤ)))
      rw [lowerTruncationLayerProjection_f]
      infer_instance
    exact { exact := (S.exact_iff_epi_kernel_lift).2 ((isZero_kernel_of_mono S.g).epi _) }
  · have h₃ : IsZero S.X₃ :=
      isZero_single_obj_X (.up ℤ) (-((m + 1 : ℕ) : ℤ))
        (K.X (-((m + 1 : ℕ) : ℤ))) i hi
    haveI : Epi S.g := h₃.epi _
    by_cases hm : -(m : ℤ) ≤ i
    · haveI : IsIso S.f := by
        change IsIso ((lowerTruncationMap K m (m + 1) (Nat.le_succ m)).f i)
        simp only [lowerTruncationMap, dif_pos hm]
        infer_instance
      haveI : Epi (kernel.ι S.g) := epi_of_epi_fac (kernel.lift_ι S.g S.f S.zero)
      haveI : IsIso (kernel.ι S.g) := isIso_of_mono_of_epi _
      have he : kernel.lift S.g S.f S.zero = S.f ≫ inv (kernel.ι S.g) := by
        apply (cancel_mono (kernel.ι S.g)).1
        simp only [Category.assoc, kernel.lift_ι, IsIso.inv_hom_id, Category.comp_id]
      exact { exact := (S.exact_iff_epi_kernel_lift).2 (by rw [he]; infer_instance) }
    · have h₁ : IsZero S.X₁ := by
        change IsZero ((lowerTruncation K m).X i)
        simp only [lowerTruncation, if_neg hm]
        exact isZero_zero C
      have h₂ : IsZero S.X₂ := by
        change IsZero ((lowerTruncation K (m + 1)).X i)
        have h : ¬ -((m + 1 : ℕ) : ℤ) ≤ i := by omega
        simp only [lowerTruncation, if_neg h]
        exact isZero_zero C
      haveI : Mono S.f := h₁.mono _
      exact { exact := S.exact_of_isZero_X₂ h₂ }

end CWSolid

#print axioms CWSolid.lowerTruncationLayerProjection
#print axioms CWSolid.lowerTruncationLayerProjection_f
#print axioms CWSolid.lowerTruncationLayerSequence
#print axioms CWSolid.lowerTruncationLayerSequence_shortExact

import GRH.Lib.Adelic.CuspForms.SmoothFormPairing
import GRH.Lib.GLn.SchurModule.SchurOrthogonality
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular forms
(known result; see Lib.Adelic.CuspForms.Petersson).

This file: Algebraic modular forms: invariant inner product, finite dimension per level. -/

open Submodule Subgroup ComplexOrder

namespace Space

variable {E n} [Field E] [Fintype n] [CMType E] (V : Space E n 1) (κ)

/-- The space of forms of weight κ on a positive definite V carries an inner product for which
right translation is unitary. -/
lemma exists_isUnitary_formTranslation : ∃ B, IsUnitary (V.formTranslation κ) B :=
  ⟨smoothPairing _ (gramForm_conjWeylRep ∘' _), fun φ h ↦ by
  obtain ⟨⟨l, o⟩, g, h⟩ := pairing_mem_smoothInvariants (fun _ ↦ gramForm_conjWeylRep _) φ φ,
    Function.ne_iff.1 (h ∘ Subtype.ext)
  refine smul_pos (by positivity [isCompact_Kf.relIndex_ne_zero o]) (classSum_pos (H :=
    .of_le inf_le_right (o.and isOpen_Kf)) ?_ ((apply_doubleCoset_out l inf_le_left g).trans_gt ?_))
    <;> simp [gramForm, weylGram_posDef.posSemidef, weylGram_posDef.dotProduct_mulVec_pos h],
  smoothPairing_formTranslation _⟩

/-- For an open subgroup K of the finite adelic points and a character χ of K, the forms of
weight κ on a positive definite V on which K acts through χ form a finite-dimensional
complex vector space. -/
lemma finite_formTranslation_levelSpace {K : Subgroup _} (hK : K.IsOpen) (χ : K →* ℂ := 1) :
  Module.Finite ℂ (levelSpace (V.formTranslation κ) K χ) :=
  @finiteDimensional_of_le _ _ _ _ _ _ _ (finite_levelSpace_smoothFormRep (H := .of_le
  inf_le_right (hK.and isOpen_Kf)) (χ := χ.comp (inclusion inf_le_left))) fun _ h k ↦ h ⟨k, k.2.1⟩

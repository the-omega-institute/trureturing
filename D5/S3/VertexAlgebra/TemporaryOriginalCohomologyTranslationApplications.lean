import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields
import D5.S3.VertexAlgebra.LatticeBcGhostBrstNilpotence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace TemporaryOriginalCohomologyTranslationApplications

open D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality
open LatticeBcGhostBrstCharge (State Q B)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes (product)
open LatticeBcGhostCohomologyFields (cycleTranslation translation field stateField)
open scoped VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

theorem original_translation_homotopy
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    LatticeBcGhostTensorStateField.translation D =
      Q D H * B D (-1) + B D (-1) * Q D H := by
  rw [LatticeBcGhostTensorStateField.translation_original D H hHG hGH]
  exact (LatticeBcGhostBrstCharge.ward_identity D H (-1)).symm

theorem cycle_translation_preimage
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCycles D H) :
    LatticeBcGhostTensorStateField.translation D state.val = Q D H (B D (-1) state.val) := by
  rw [original_translation_homotopy D H hHG hGH]
  simp only [LinearMap.add_apply, Module.End.mul_apply,
    show Q D H state.val = 0 from state.property, map_zero, add_zero]

theorem cycle_translation_is_boundary
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCycles D H) :
    cycleTranslation D H state ∈ OriginalBoundaries D H := by
  change ∃ preimage : State D, Q D H preimage =
    LatticeBcGhostTensorStateField.translation D state.val
  exact ⟨B D (-1) state.val, (cycle_translation_preimage D H hHG hGH state).symm⟩

theorem quotient_translation_zero
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    translation D H = 0 := by
  apply LinearMap.ext
  intro state
  refine Submodule.Quotient.induction_on (OriginalBoundaries D H) state ?_
  intro representative
  change translation D H ((OriginalBoundaries D H).mkQ representative) = 0
  rw [LatticeBcGhostCohomologyFields.translation_mk]
  exact (Submodule.Quotient.mk_eq_zero (OriginalBoundaries D H)).mpr
    (cycle_translation_is_boundary D H hHG hGH representative)

theorem quotient_nonminusone_mode_zero
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state input : OriginalCohomology D H) (mode : ℤ) (other : mode ≠ -1) :
    product D H mode state input = 0 := by
  have integerNonzero : mode + 1 ≠ 0 := by omega
  have scalarNonzero : -((mode + 1 : ℤ) : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (Int.cast_ne_zero.mpr integerNonzero)
  have killed := LatticeBcGhostCohomologyFields.derivative D H state input (mode + 1)
  simp only [quotient_translation_zero D H hHG hGH, LinearMap.zero_apply,
    map_zero, show mode + 1 - 1 = mode by omega] at killed
  exact (smul_eq_zero.mp killed.symm).resolve_left scalarNonzero

theorem quotient_nonminusone_mode_operator_zero
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCohomology D H) (mode : ℤ) (other : mode ≠ -1) :
    product D H mode state = 0 := by
  apply LinearMap.ext
  intro input
  exact quotient_nonminusone_mode_zero D H hHG hGH state input mode other

def constantMinusOneField (state : OriginalCohomology D H) :
    VertexOperator ℂ (OriginalCohomology D H) :=
  VertexOperator.of_coeff
    (fun degree => if degree = 0 then product D H (-1) state else 0)
    (fun input => by
      refine ⟨0, ?_⟩
      intro degree nonzero
      by_cases chosen : degree = 0
      · subst degree
        exact le_rfl
      · exact False.elim (nonzero (by simp only [if_neg chosen, LinearMap.zero_apply])))

theorem constantMinusOneField_mode (state : OriginalCohomology D H) (mode : ℤ) :
    ((constantMinusOneField D H state)[[mode]]) =
      if mode = -1 then product D H (-1) state else 0 := by
  simp only [constantMinusOneField, VertexOperator.ncoeff_of_coeff,
    show (-mode - 1 = 0) ↔ mode = -1 by omega]

theorem original_field_is_constant
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCohomology D H) :
    field D H state = constantMinusOneField D H state := by
  apply HVertexOperator.coeff_inj
  funext degree
  apply LinearMap.ext
  intro input
  simp only [VertexOperator.coeff_eq_ncoeff,
    LatticeBcGhostCohomologyFields.field_mode, constantMinusOneField_mode]
  by_cases chosen : -degree - 1 = -1
  · rw [if_pos chosen, chosen]
  · rw [if_neg chosen]
    exact quotient_nonminusone_mode_zero D H hHG hGH state input (-degree - 1) chosen

theorem original_stateField_is_constant
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCohomology D H) :
    stateField D H state = constantMinusOneField D H state :=
  original_field_is_constant D H hHG hGH state

theorem original_stateField_modes
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (state : OriginalCohomology D H) (mode : ℤ) :
    ((stateField D H state)[[mode]]) =
      if mode = -1 then product D H (-1) state else 0 := by
  rw [original_stateField_is_constant D H hHG hGH, constantMinusOneField_mode]

theorem critical_original_complex_and_constant_field
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (rank26 : D.rank = 26) :
    Q D H * Q D H = 0 ∧
      LinearMap.range (Q D H) ≤ OriginalCycles D H ∧
      LatticeBcGhostTensorStateField.translation D = Q D H * B D (-1) + B D (-1) * Q D H ∧
      translation D H = 0 ∧
      (∀ state input : OriginalCohomology D H, ∀ mode : ℤ, mode ≠ -1 →
        product D H mode state input = 0) ∧
      (∀ state : OriginalCohomology D H,
        stateField D H state = constantMinusOneField D H state) := by
  exact ⟨LatticeBcGhostBrstNilpotence.nilpotent D H hHG hGH rank26,
    LatticeBcGhostNeutralCohomology.original_image_in_cycles D H hHG hGH rank26,
    original_translation_homotopy D H hHG hGH,
    quotient_translation_zero D H hHG hGH,
    quotient_nonminusone_mode_zero D H hHG hGH,
    original_stateField_is_constant D H hHG hGH⟩

#print axioms original_translation_homotopy
#print axioms cycle_translation_is_boundary
#print axioms quotient_translation_zero
#print axioms quotient_nonminusone_mode_zero
#print axioms original_stateField_modes
#print axioms critical_original_complex_and_constant_field

end TemporaryOriginalCohomologyTranslationApplications

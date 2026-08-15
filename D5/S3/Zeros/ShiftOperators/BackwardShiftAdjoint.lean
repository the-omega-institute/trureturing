/- GID: D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint
   generality: I
   mirror-B: D5/B/S3/Zeros/ShiftOperators/BackwardShiftAdjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Upgrade the shift pairing to the Hilbert adjoint and its defect projection. -/

import D5.S3.Zeros.ShiftOperators.ShiftRangeProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Backward shift adjoint

## Audit trail and scope

The private helper `translate_dvd` mirrors the private fact
`BackwardShiftOperator.normalizedTableAdd_dvd`; SL-008 freezes that source module, so
de-privatizing it is forbidden and the local re-proof preserves the boundary. This is the
same boundary already documented in `ShiftRangeProjection`.

Not covered here: the coprime double commutation of the backward shift with a forward
translation, and the Nica lattice reading of the coprime projection relation.
-/

namespace D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open D5.S3.Zeros.ShiftOperators.BackwardShiftOperator
open D5.S3.Zeros.ShiftOperators.BackwardShiftCoisometry
open D5.S3.Zeros.ShiftOperators.ShiftRangeProjection

noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

private theorem translate_dvd (a u : PrimeAxisTable) :
    primeAxisEncoding u ∣ primeAxisEncoding (normalizedTableAdd a u) :=
  ⟨primeAxisEncoding a, by simp [normalizedTableAdd, mul_comm]⟩

/-- The zero-extended translation is the Hilbert adjoint of the backward shift. -/
theorem adjoint_backwardShiftCLM (u : PrimeAxisTable) :
    ContinuousLinearMap.adjoint (backwardShiftCLM u) = forwardTranslationCLM u := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simpa [sourcePairing] using (backward_shift_sourcePairing_adjoint u y x).symm

/-- Dually, the backward shift is the Hilbert adjoint of the zero-extended translation. -/
theorem adjoint_forwardTranslationCLM (u : PrimeAxisTable) :
    ContinuousLinearMap.adjoint (forwardTranslationCLM u) = backwardShiftCLM u := by
  rw [← adjoint_backwardShiftCLM u, ContinuousLinearMap.adjoint_adjoint]

/-- The zero-extended translation is an isometry in star form. -/
theorem forward_translation_star_isometry (u : PrimeAxisTable) :
    (ContinuousLinearMap.adjoint (forwardTranslationCLM u)).comp
        (forwardTranslationCLM u) = 1 :=
  ContinuousLinearMap.norm_map_iff_adjoint_comp_self _ |>.1
    (forward_translation_norm_eq u)

/-- The backward shift is a coisometry in star form. -/
theorem backward_shift_star_coisometry (u : PrimeAxisTable) :
    (backwardShiftCLM u).comp
        (ContinuousLinearMap.adjoint (backwardShiftCLM u)) = 1 := by
  rw [adjoint_backwardShiftCLM]
  apply ContinuousLinearMap.ext
  intro x
  simpa using backward_shift_comp_forward_translation u x

/-- The defect projection is the star square of the backward shift, so the shift is a
partial isometry with support projection `shiftRangeProjection u`. -/
theorem adjoint_backward_shift_comp_self (u : PrimeAxisTable) :
    (ContinuousLinearMap.adjoint (backwardShiftCLM u)).comp (backwardShiftCLM u) =
      shiftRangeProjection u := by
  rw [adjoint_backwardShiftCLM]
  rfl

/-- The defect projection is self-adjoint, not merely symmetric for the source pairing. -/
theorem shift_range_projection_isSelfAdjoint (u : PrimeAxisTable) :
    IsSelfAdjoint (shiftRangeProjection u) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', shiftRangeProjection,
    ContinuousLinearMap.adjoint_comp, adjoint_forwardTranslationCLM,
    adjoint_backwardShiftCLM]

/-- The defect projection is a star projection. -/
theorem shift_range_projection_isStarProjection (u : PrimeAxisTable) :
    IsStarProjection (shiftRangeProjection u) :=
  ⟨shift_range_projection_idempotent u, shift_range_projection_isSelfAdjoint u⟩

/-- The subspace of coefficient families supported on the multiples of `u`. -/
def divisibleSubspace (u : PrimeAxisTable) : Submodule ℂ ZetaHilbertSpace where
  carrier := {x | ∀ b, ¬primeAxisEncoding u ∣ primeAxisEncoding b → x b = 0}
  add_mem' hx hy b hb := by simp [hx b hb, hy b hb]
  zero_mem' b _ := rfl
  smul_mem' c x hx b hb := by simp [hx b hb]

@[simp]
theorem mem_divisibleSubspace {u : PrimeAxisTable} {x : ZetaHilbertSpace} :
    x ∈ divisibleSubspace u ↔
      ∀ b, ¬primeAxisEncoding u ∣ primeAxisEncoding b → x b = 0 := Iff.rfl

/-- The defect projection fixes exactly the families supported on multiples of `u`. -/
theorem shift_range_projection_eq_self_iff (u : PrimeAxisTable) (x : ZetaHilbertSpace) :
    shiftRangeProjection u x = x ↔ x ∈ divisibleSubspace u := by
  constructor
  · intro h b hb
    have hb' := congrArg (fun z : ZetaHilbertSpace => z b) h
    rw [shiftRangeProjection_apply, if_neg hb] at hb'
    exact hb'.symm
  · intro h
    apply lp.ext
    funext b
    rw [shiftRangeProjection_apply]
    by_cases hb : primeAxisEncoding u ∣ primeAxisEncoding b
    · rw [if_pos hb]
    · rw [if_neg hb, h b hb]

/-- The zero-extended translation has exactly the divisible families as range. -/
theorem range_forwardTranslationCLM (u : PrimeAxisTable) :
    LinearMap.range (forwardTranslationCLM u : ZetaHilbertSpace →ₗ[ℂ] ZetaHilbertSpace) =
      divisibleSubspace u := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩ b hb
    exact forward_translation_apply_of_not_dvd u b y hb
  · intro x hx
    exact ⟨backwardShiftCLM u x, (shift_range_projection_eq_self_iff u x).2 hx⟩

/-- The defect projection has the same range as the zero-extended translation. -/
theorem range_shiftRangeProjection (u : PrimeAxisTable) :
    LinearMap.range (shiftRangeProjection u : ZetaHilbertSpace →ₗ[ℂ] ZetaHilbertSpace) =
      divisibleSubspace u := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩ b hb
    exact forward_translation_apply_of_not_dvd u b _ hb
  · intro x hx
    exact ⟨x, (shift_range_projection_eq_self_iff u x).2 hx⟩

instance divisibleSubspace_hasOrthogonalProjection (u : PrimeAxisTable) :
    (divisibleSubspace u).HasOrthogonalProjection := by
  rw [← range_shiftRangeProjection u]
  obtain ⟨h, -⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp
      (shift_range_projection_isStarProjection u)
  exact h

/-- The divisibility filter is the orthogonal projection onto the divisible subspace. -/
theorem shift_range_projection_eq_starProjection (u : PrimeAxisTable) :
    shiftRangeProjection u = (divisibleSubspace u).starProjection := by
  obtain ⟨h, hp⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp
      (shift_range_projection_isStarProjection u)
  rw [hp]
  congr 1
  exact range_shiftRangeProjection u

/-- The backward shift kernel is the orthogonal complement of the divisible subspace. -/
theorem ker_backwardShiftCLM (u : PrimeAxisTable) :
    LinearMap.ker (backwardShiftCLM u : ZetaHilbertSpace →ₗ[ℂ] ZetaHilbertSpace) =
      (divisibleSubspace u)ᗮ := by
  rw [← range_forwardTranslationCLM u, ← adjoint_forwardTranslationCLM u,
    ← ContinuousLinearMap.orthogonal_range]

/-- The wandering complement is the families supported off the multiples of `u`. -/
theorem mem_orthogonal_divisibleSubspace (u : PrimeAxisTable) (x : ZetaHilbertSpace) :
    x ∈ (divisibleSubspace u)ᗮ ↔
      ∀ b, primeAxisEncoding u ∣ primeAxisEncoding b → x b = 0 := by
  rw [← ker_backwardShiftCLM u]
  constructor
  · intro hx b hb
    have hx' : backwardShiftCLM u x = 0 := hx
    have hval := congrArg (fun z : ZetaHilbertSpace => z (normalizedTableSub b u)) hx'
    simpa [backwardShiftCLM_apply, backwardShift,
      normalizedTableSub_add_cancel hb] using hval
  · intro hx
    show backwardShiftCLM u x = 0
    apply lp.ext
    funext a
    simpa [backwardShiftCLM_apply, backwardShift] using hx _ (translate_dvd a u)

#print axioms adjoint_backwardShiftCLM
#print axioms adjoint_backward_shift_comp_self
#print axioms shift_range_projection_isStarProjection
#print axioms range_forwardTranslationCLM
#print axioms shift_range_projection_eq_starProjection
#print axioms ker_backwardShiftCLM
#print axioms mem_orthogonal_divisibleSubspace

end D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint

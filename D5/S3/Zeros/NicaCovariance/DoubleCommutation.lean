/- GID: D5/S3/Zeros/NicaCovariance/DoubleCommutation
   generality: I
   mirror-B: D5/B/S3/Zeros/NicaCovariance/DoubleCommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove coprime double commutation and identify the corresponding subspace meet. -/

import D5.S3.Zeros.NicaCovariance.SemigroupRelations
import D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint

/-!
# Double commutation

## Audit trail and scope

The private helper `normalizedTableAdd_swap_right` locally re-proves a consequence of the
private address-addition facts in `SemigroupRelations`; SL-008 freezes that source module,
so de-privatizing them is forbidden and the local private proof preserves the boundary.
The private helper `normalizedTableAdd_dvd_iff_of_coprime` mirrors the divisibility
equivalence embedded in the frozen proof of
`SemigroupRelations.shift_range_projection_comp_of_coprime`; it remains private for the
same reason. The cancellation helper is a module-local implementation detail.

This module pays the two deferrals recorded in `BackwardShiftAdjoint`: coprime double
commutation and the Nica lattice reading of the coprime projection relation.
-/

namespace D5.S3.Zeros.NicaCovariance.DoubleCommutation

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open D5.S3.Zeros.NicaCovariance.SemigroupRelations
open D5.S3.Zeros.ShiftOperators.BackwardShiftOperator
open D5.S3.Zeros.ShiftOperators.ShiftRangeProjection
open D5.S3.Zeros.ShiftOperators.BackwardShiftAdjoint

noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

private theorem normalizedTableAdd_swap_right (a u v : PrimeAxisTable) :
    normalizedTableAdd (normalizedTableAdd a v) u =
      normalizedTableAdd (normalizedTableAdd a u) v := by
  apply primeAxisEncoding.injective
  simp [normalizedTableAdd, mul_comm, mul_left_comm]

private theorem normalizedTableAdd_dvd_cancel_right_of_coprime
    (a u v : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    primeAxisEncoding v ∣ primeAxisEncoding (normalizedTableAdd a u) ↔
      primeAxisEncoding v ∣ primeAxisEncoding a := by
  simp only [PNat.dvd_iff]
  rw [show ((primeAxisEncoding (normalizedTableAdd a u) : ℕ+) : ℕ) =
      (primeAxisEncoding a : ℕ) * (primeAxisEncoding u : ℕ) by
    simp [normalizedTableAdd]]
  exact hcop.symm.dvd_mul_right

private theorem normalizedTableAdd_dvd_iff_of_coprime
    (u v b : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    primeAxisEncoding (normalizedTableAdd u v) ∣ primeAxisEncoding b ↔
      primeAxisEncoding u ∣ primeAxisEncoding b ∧
        primeAxisEncoding v ∣ primeAxisEncoding b := by
  simp only [PNat.dvd_iff]
  rw [show ((primeAxisEncoding (normalizedTableAdd u v) : ℕ+) : ℕ) =
      (primeAxisEncoding u : ℕ) * (primeAxisEncoding v : ℕ) by
    simp [normalizedTableAdd]]
  constructor
  · intro huv
    exact ⟨(dvd_mul_right _ _).trans huv, (dvd_mul_left _ _).trans huv⟩
  · rintro ⟨hu, hv⟩
    exact hcop.mul_dvd_of_dvd_of_dvd hu hv

/-- Backward shift by `u` commutes with forward translation by a coprime `v`. -/
theorem backward_shift_comp_forward_translation_of_coprime
    (u v : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    (backwardShiftCLM u).comp (forwardTranslationCLM v) =
      (forwardTranslationCLM v).comp (backwardShiftCLM u) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext a
  change forwardTranslationCLM v x (normalizedTableAdd a u) =
    forwardTranslationCLM v (backwardShiftCLM u x) a
  by_cases ha : primeAxisEncoding v ∣ primeAxisEncoding a
  · let c := normalizedTableSub a v
    have hcv : normalizedTableAdd c v = a := normalizedTableSub_add_cancel ha
    calc
      forwardTranslationCLM v x (normalizedTableAdd a u) =
          forwardTranslationCLM v x (normalizedTableAdd (normalizedTableAdd c u) v) := by
        rw [← hcv, normalizedTableAdd_swap_right]
      _ = x (normalizedTableAdd c u) :=
        forward_translation_apply_translate v (normalizedTableAdd c u) x
      _ = backwardShiftCLM u x c := rfl
      _ = forwardTranslationCLM v (backwardShiftCLM u x) (normalizedTableAdd c v) :=
        (forward_translation_apply_translate v c (backwardShiftCLM u x)).symm
      _ = forwardTranslationCLM v (backwardShiftCLM u x) a := by rw [hcv]
  · have hau : ¬primeAxisEncoding v ∣
        primeAxisEncoding (normalizedTableAdd a u) :=
      fun h ↦ ha ((normalizedTableAdd_dvd_cancel_right_of_coprime a u v hcop).1 h)
    rw [forward_translation_apply_of_not_dvd v _ _ hau,
      forward_translation_apply_of_not_dvd v _ _ ha]

/-- Coprime forward translations satisfy the standard doubly-commuting isometry relation. -/
theorem adjoint_forward_translation_comp_of_coprime
    (u v : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    (ContinuousLinearMap.adjoint (forwardTranslationCLM u)).comp
        (forwardTranslationCLM v) =
      (forwardTranslationCLM v).comp
        (ContinuousLinearMap.adjoint (forwardTranslationCLM u)) := by
  rw [adjoint_forwardTranslationCLM]
  exact backward_shift_comp_forward_translation_of_coprime u v hcop

/-- Coprime divisibility subspaces meet at the product address. -/
theorem divisibleSubspace_inf_of_coprime
    (u v : PrimeAxisTable)
    (hcop : Nat.Coprime (primeAxisEncoding u) (primeAxisEncoding v)) :
    divisibleSubspace u ⊓ divisibleSubspace v =
      divisibleSubspace (normalizedTableAdd u v) := by
  ext x
  simp only [Submodule.mem_inf, mem_divisibleSubspace]
  constructor
  · rintro ⟨hu, hv⟩ b hb
    rw [normalizedTableAdd_dvd_iff_of_coprime u v b hcop] at hb
    rcases not_and_or.mp hb with hbu | hbv
    · exact hu b hbu
    · exact hv b hbv
  · intro huv
    constructor
    · intro b hbu
      exact huv b fun hb ↦ hbu
        ((normalizedTableAdd_dvd_iff_of_coprime u v b hcop).1 hb).1
    · intro b hbv
      exact huv b fun hb ↦ hbv
        ((normalizedTableAdd_dvd_iff_of_coprime u v b hcop).1 hb).2

#print axioms backward_shift_comp_forward_translation_of_coprime
#print axioms adjoint_forward_translation_comp_of_coprime
#print axioms divisibleSubspace_inf_of_coprime

end D5.S3.Zeros.NicaCovariance.DoubleCommutation

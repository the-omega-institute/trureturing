/- GID: D5/S3/Zeros/ShiftOperators/ShiftRangeProjection
   generality: I
   mirror-B: D5/B/S3/Zeros/ShiftOperators/ShiftRangeProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the backward shift defect projection as the address divisibility filter. -/

import D5.S3.Zeros.ShiftOperators.BackwardShiftCoisometry

/-!
# Shift range projection

## Audit trail and scope

The private helpers `translate_dvd` and `labeledZetaCoefficient_add` mirror the private facts
`BackwardShiftOperator.normalizedTableAdd_dvd` and
`SpectralDynamics.labeledZetaCoefficient_add`, respectively. SL-008 freezes those source modules,
so de-privatizing either fact is forbidden; the two local re-proofs preserve that boundary.

Not covered here: identifying the range as a submodule or phrasing this operator as an
`orthogonalProjection`. Those refinements are reserved for a future node that develops the Nica
relations.
-/

namespace D5.S3.Zeros.ShiftOperators.ShiftRangeProjection

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open D5.S3.Weil.Convention
open D5.S3.Zeros.ShiftOperators.BackwardShiftOperator
open D5.S3.Zeros.ShiftOperators.BackwardShiftCoisometry
open scoped ComplexConjugate

attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

private theorem translate_dvd (a u : PrimeAxisTable) :
    primeAxisEncoding u ∣ primeAxisEncoding (normalizedTableAdd a u) :=
  ⟨primeAxisEncoding a, by simp [normalizedTableAdd, mul_comm]⟩

/-- Zero-extension restores the coefficient sitting at a translated address. -/
theorem forward_translation_apply_translate (u a : PrimeAxisTable)
    (x : ZetaHilbertSpace) :
    forwardTranslationCLM u x (normalizedTableAdd a u) = x a := by
  have h := congrArg (fun y : ZetaHilbertSpace => y a)
    (backward_shift_comp_forward_translation u x)
  simpa [backwardShiftCLM_apply, backwardShift] using h

/-- On a divisible address the zero-extension reads the exact quotient. -/
theorem forward_translation_apply_of_dvd (u b : PrimeAxisTable)
    (x : ZetaHilbertSpace) (h : primeAxisEncoding u ∣ primeAxisEncoding b) :
    forwardTranslationCLM u x b = x (normalizedTableSub b u) := by
  conv_lhs => rw [← normalizedTableSub_add_cancel h]
  exact forward_translation_apply_translate u (normalizedTableSub b u) x

/-- Off the multiples of `u` the zero-extension vanishes. -/
theorem forward_translation_apply_of_not_dvd (u b : PrimeAxisTable)
    (x : ZetaHilbertSpace) (h : ¬primeAxisEncoding u ∣ primeAxisEncoding b) :
    forwardTranslationCLM u x b = 0 := by
  have hb : ¬∃ a, normalizedTableAdd a u = b := by
    rintro ⟨a, rfl⟩
    exact h (translate_dvd a u)
  change Function.extend (fun a : PrimeAxisTable => normalizedTableAdd a u)
      (x : PrimeAxisTable → ℂ) 0 b = 0
  exact Function.extend_apply' _ _ _ hb

/-- The defect projection of the backward shift: pull back, then translate forward. -/
noncomputable def shiftRangeProjection (u : PrimeAxisTable) :
    ZetaHilbertSpace →L[ℂ] ZetaHilbertSpace :=
  (forwardTranslationCLM u).comp (backwardShiftCLM u)

/-- The defect projection acts diagonally as the divisibility indicator. -/
theorem shiftRangeProjection_apply (u : PrimeAxisTable) (x : ZetaHilbertSpace)
    (b : PrimeAxisTable) :
    shiftRangeProjection u x b =
      if primeAxisEncoding u ∣ primeAxisEncoding b then x b else 0 := by
  by_cases h : primeAxisEncoding u ∣ primeAxisEncoding b
  · rw [if_pos h]
    change forwardTranslationCLM u (backwardShiftCLM u x) b = x b
    rw [forward_translation_apply_of_dvd u b _ h, backwardShiftCLM_apply]
    change x (normalizedTableAdd (normalizedTableSub b u) u) = x b
    rw [normalizedTableSub_add_cancel h]
  · rw [if_neg h]
    exact forward_translation_apply_of_not_dvd u b _ h

/-- The divisibility filter is idempotent. -/
theorem shift_range_projection_idempotent (u : PrimeAxisTable) :
    IsIdempotentElem (shiftRangeProjection u) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext b
  change shiftRangeProjection u (shiftRangeProjection u x) b =
    shiftRangeProjection u x b
  rw [shiftRangeProjection_apply, shiftRangeProjection_apply]
  by_cases h : primeAxisEncoding u ∣ primeAxisEncoding b <;> simp [h]

private theorem sourcePairing_conj (x y : ZetaHilbertSpace) :
    sourcePairing x y = conj (sourcePairing y x) := by
  simp [sourcePairing, inner_conj_symm]

/-- The zero-extension pairs against the backward shift on the other side. -/
theorem forward_translation_sourcePairing_adjoint (u : PrimeAxisTable)
    (x y : ZetaHilbertSpace) :
    sourcePairing (forwardTranslationCLM u x) y =
      sourcePairing x (backwardShiftCLM u y) := by
  rw [sourcePairing_conj (forwardTranslationCLM u x) y,
    ← backward_shift_sourcePairing_adjoint,
    ← sourcePairing_conj]

/-- The defect projection is symmetric for the source pairing. -/
theorem shift_range_projection_sourcePairing_symm (u : PrimeAxisTable)
    (x y : ZetaHilbertSpace) :
    sourcePairing (shiftRangeProjection u x) y =
      sourcePairing x (shiftRangeProjection u y) := by
  change sourcePairing (forwardTranslationCLM u (backwardShiftCLM u x)) y =
    sourcePairing x (forwardTranslationCLM u (backwardShiftCLM u y))
  rw [forward_translation_sourcePairing_adjoint]
  exact backward_shift_sourcePairing_adjoint u x (backwardShiftCLM u y)

/-- The backward shift annihilates exactly the vectors the defect projection kills. -/
theorem backward_shift_apply_eq_zero_iff (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) :
    backwardShiftCLM u x = 0 ↔ shiftRangeProjection u x = 0 := by
  constructor
  · intro h
    change forwardTranslationCLM u (backwardShiftCLM u x) = 0
    rw [h, map_zero]
  · intro h
    have hx := congrArg (fun z : ZetaHilbertSpace => backwardShiftCLM u z) h
    simpa [shiftRangeProjection, backward_shift_comp_forward_translation] using hx

/-- The backward shift absorbs its own defect projection. -/
theorem backward_shift_comp_projection (u : PrimeAxisTable) :
    (backwardShiftCLM u).comp (shiftRangeProjection u) = backwardShiftCLM u := by
  apply ContinuousLinearMap.ext
  intro x
  change backwardShiftCLM u (forwardTranslationCLM u (backwardShiftCLM u x)) =
    backwardShiftCLM u x
  exact backward_shift_comp_forward_translation u (backwardShiftCLM u x)

/-- The defect projection fixes the range of the zero-extension. -/
theorem projection_comp_forward_translation (u : PrimeAxisTable) :
    (shiftRangeProjection u).comp (forwardTranslationCLM u) =
      forwardTranslationCLM u := by
  apply ContinuousLinearMap.ext
  intro x
  change forwardTranslationCLM u (backwardShiftCLM u (forwardTranslationCLM u x)) =
    forwardTranslationCLM u x
  rw [backward_shift_comp_forward_translation]

private theorem projection_single_self (u : PrimeAxisTable) :
    shiftRangeProjection u (lp.single 2 u (1 : ℂ)) = lp.single 2 u (1 : ℂ) := by
  apply lp.ext
  funext b
  rw [shiftRangeProjection_apply]
  by_cases h : primeAxisEncoding u ∣ primeAxisEncoding b
  · rw [if_pos h]
  · rw [if_neg h]
    have hb : b ≠ u := by
      rintro rfl
      exact h dvd_rfl
    exact (lp.single_apply_ne (E := fun _ : PrimeAxisTable => ℂ) 2 u (1 : ℂ) hb).symm

/-- The defect projection is a nonzero contraction, hence of operator norm one. -/
theorem shift_range_projection_norm_eq_one (u : PrimeAxisTable) :
    ‖shiftRangeProjection u‖ = 1 := by
  apply le_antisymm
  · refine (shiftRangeProjection u).opNorm_le_bound zero_le_one fun x => ?_
    have h : ‖shiftRangeProjection u x‖ = ‖backwardShiftCLM u x‖ := by
      change ‖forwardTranslationCLM u (backwardShiftCLM u x)‖ = _
      exact forward_translation_norm_eq u (backwardShiftCLM u x)
    rw [h, one_mul]
    change ‖backwardShiftLinearMap u x‖ ≤ ‖x‖
    exact backwardShiftLinearMap_norm_nonincreasing u x
  · let e : ZetaHilbertSpace := lp.single 2 u (1 : ℂ)
    have he : ‖e‖ = 1 := by simp [e]
    calc
      (1 : ℝ) = ‖shiftRangeProjection u e‖ := by
        rw [projection_single_self, he]
      _ ≤ ‖shiftRangeProjection u‖ :=
        (shiftRangeProjection u).unit_le_opNorm _ (le_of_eq he)

private theorem labeledZetaCoefficient_add (s w : ℂ) (a : PrimeAxisTable) :
    labeledZetaCoefficient (s + w) a =
      labeledZetaCoefficient s a * labeledZetaCoefficient w a := by
  have hn : ((((primeAxisEncoding a : ℕ+) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (PNat.pos (primeAxisEncoding a)))
  simp only [labeledZetaCoefficient]
  rw [Complex.cpow_add s w hn]
  simp only [one_div, mul_inv_rev]
  ring

private theorem labeledZetaCoefficient_conj (w : ℂ) (a : PrimeAxisTable) :
    conj (labeledZetaCoefficient w a) = labeledZetaCoefficient (conj w) a := by
  have hpos : (0 : ℝ) < ((primeAxisEncoding a : ℕ+) : ℕ) := by
    exact_mod_cast PNat.pos (primeAxisEncoding a)
  have harg : ((((primeAxisEncoding a : ℕ+) : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [show ((((primeAxisEncoding a : ℕ+) : ℕ) : ℂ)) =
        (((((primeAxisEncoding a : ℕ+) : ℕ) : ℝ)) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg hpos.le]
    exact ne_of_lt Real.pi_pos
  simp only [labeledZetaCoefficient, map_div₀, map_one]
  rw [Complex.cpow_conj _ _ harg]
  norm_num

/-- The backward shift scales the labeled zeta vector by its own coefficient. -/
theorem backward_shift_labeled_zeta (u : PrimeAxisTable) (s : ℂ)
    (hs : criticalAbscissa < s.re) :
    backwardShiftCLM u (labeledZetaVector s hs) =
      labeledZetaCoefficient s u • labeledZetaVector s hs := by
  apply lp.ext
  funext a
  simpa [backwardShiftCLM_apply] using
    labeled_zeta_vector_backward_shift_eigen s hs u a

/-- Filtering to the multiples of `u` scales the zeta reproducing kernel by the
`u`-th Euler-type factor. -/
theorem shift_range_projection_zeta_kernel (u : PrimeAxisTable) (s w : ℂ)
    (hs : criticalAbscissa < s.re) (hw : criticalAbscissa < w.re) :
    sourcePairing (shiftRangeProjection u (labeledZetaVector s hs))
        (labeledZetaVector w hw) =
      labeledZetaCoefficient (s + conj w) u * classicalZeta (s + conj w) := by
  change sourcePairing (forwardTranslationCLM u
      (backwardShiftCLM u (labeledZetaVector s hs))) (labeledZetaVector w hw) = _
  rw [forward_translation_sourcePairing_adjoint, backward_shift_labeled_zeta,
    backward_shift_labeled_zeta, sourcePairing, inner_smul_left, inner_smul_right,
    ← sourcePairing, labeled_zeta_inner, labeledZetaCoefficient_conj,
    labeledZetaCoefficient_add]
  ring

#print axioms shiftRangeProjection_apply
#print axioms shift_range_projection_idempotent
#print axioms shift_range_projection_sourcePairing_symm
#print axioms backward_shift_apply_eq_zero_iff
#print axioms shift_range_projection_norm_eq_one
#print axioms shift_range_projection_zeta_kernel

end D5.S3.Zeros.ShiftOperators.ShiftRangeProjection

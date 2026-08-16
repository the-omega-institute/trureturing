/- GID: D5/S1/Recurrence/Witt/WittRowLaws
   generality: G
   mirror-B: D5/B/S1/Recurrence/Witt/WittRowLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first two Witt rows terminate while the opposite row alternates forever. -/

import Mathlib.RingTheory.PowerSeries.Binomial

namespace D5.S1.Recurrence.Witt.WittRowLaws

open PowerSeries

/-- The formal inverse of `1 + X`, obtained from mathlib's inverse of `1 - X`
by the substitution `X -> -X`. -/
noncomputable def inverseOnePlusX : ℤ⟦X⟧ :=
  PowerSeries.rescale (-1) (PowerSeries.invOneSubPow ℤ 1).val

/-- The logarithmic quotient for the `a = 1` Witt row, with its leading `u`
factor omitted. -/
noncomputable def firstWittRow : ℤ⟦X⟧ :=
  (1 + X + X ^ 2 + X ^ 3) * inverseOnePlusX

/-- The logarithmic quotient for the `b = 1` Witt row, with its leading `v`
factor omitted. -/
noncomputable def secondWittRow : ℤ⟦X⟧ :=
  (1 + X + X ^ 2) * inverseOnePlusX

private theorem coeff_inverse_one_plus_X (k : ℕ) :
    coeff k inverseOnePlusX = (-1 : ℤ) ^ k := by
  rw [inverseOnePlusX, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose (S := ℤ) 0,
    PowerSeries.coeff_mk]
  norm_num

private theorem one_add_X_mul_inverse :
    (1 + X : ℤ⟦X⟧) * inverseOnePlusX = 1 := by
  rw [PowerSeries.ext_iff]
  intro k
  cases k with
  | zero =>
      rw [add_mul, one_mul, map_add, coeff_inverse_one_plus_X]
      simp
  | succ k =>
      rw [add_mul, one_mul, map_add, coeff_inverse_one_plus_X,
        PowerSeries.coeff_succ_X_mul, coeff_inverse_one_plus_X]
      simp [pow_succ]

private theorem firstWittRow_eq :
    firstWittRow = (1 + X ^ 2 : ℤ⟦X⟧) := by
  rw [firstWittRow]
  calc
    (1 + X + X ^ 2 + X ^ 3) * inverseOnePlusX =
        ((1 + X) * (1 + X ^ 2)) * inverseOnePlusX := by ring
    _ = (1 + X ^ 2) * ((1 + X) * inverseOnePlusX) := by ring
    _ = 1 + X ^ 2 := by rw [one_add_X_mul_inverse, mul_one]

private theorem secondWittRow_eq :
    secondWittRow = (1 + X ^ 2 * inverseOnePlusX : ℤ⟦X⟧) := by
  rw [secondWittRow]
  calc
    (1 + X + X ^ 2) * inverseOnePlusX =
        ((1 + X) + X ^ 2) * inverseOnePlusX := by ring
    _ = (1 + X) * inverseOnePlusX + X ^ 2 * inverseOnePlusX := by ring
    _ = 1 + X ^ 2 * inverseOnePlusX := by rw [one_add_X_mul_inverse]

/-- The three all-order Witt row laws.

The first equality is the pure-direction Euler factorization
`1 + X = (1 - X^2) / (1 - X)`. The second component says that the
`a = 1` logarithmic row has coefficients only in degrees zero and two.
The third says that the `b = 1` row has zero linear coefficient and
alternates in every other degree. -/
theorem witt_row_closed_laws :
    ((1 + X : ℤ⟦X⟧) * (1 - X) = 1 - X ^ 2) ∧
      (∀ k, coeff k firstWittRow = if k = 0 ∨ k = 2 then 1 else 0) ∧
      (∀ k, coeff k secondWittRow = if k = 1 then 0 else (-1 : ℤ) ^ k) := by
  refine ⟨by ring, ?_, ?_⟩
  · intro k
    rw [firstWittRow_eq]
    by_cases hk0 : k = 0
    · subst k
      simp
    by_cases hk2 : k = 2
    · subst k
      simp
    simp [PowerSeries.coeff_X_pow, hk0, hk2]
  · intro k
    rw [secondWittRow_eq]
    by_cases hk0 : k = 0
    · subst k
      simp
    by_cases hk1 : k = 1
    · subst k
      simp [PowerSeries.coeff_X_pow_mul']
    have hk2 : 2 ≤ k := by omega
    simp only [map_add, coeff_one, Int.reduceNeg]
    rw [if_neg hk0, zero_add, PowerSeries.coeff_X_pow_mul', if_pos hk2,
      coeff_inverse_one_plus_X, if_neg hk1]
    rw [← Nat.sub_add_cancel hk2, pow_add]
    norm_num

end D5.S1.Recurrence.Witt.WittRowLaws

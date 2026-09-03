/- GID: D5/S3/Analytic/ExactPoleLayerSelection
   generality: I
   mirror-B: D5/B/S3/Analytic/ExactPoleLayerSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourth-order pole layers select quotient and remainder, with nine exact row certificates. -/

/- Library-search audit (2026-09-04):
   * `Nat.mod_add_div` and `Nat.mod_lt` provide the exact quotient-remainder
     decomposition and the strict four-layer bound.
   * The adjacent frozen theorem `pole_layer_coefficient` supplies the exact
     power-series coefficient shift. No repository theorem combined that shift
     with `K = a / 4`, `j = a % 4`, or the nine stated rows.
   * The low-layer readings are checked from the rational regular-part head;
     the source atom's external tail-polynomial fits and numerical start points
     are deliberately not asserted here. -/

import D5.S3.Analytic.PoleLayerSelection

namespace D5.S3.Analytic.ExactPoleLayerSelection

open PowerSeries
open D5.S3.Analytic.PoleLayerSelection

noncomputable section

/-- The coefficients through degree three of the regular part used by the
source layer calculation. Higher coefficients do not affect the readings below. -/
def regularPartHead : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    match n with
    | 0 => 1
    | 1 => 2
    | 2 => -2
    | 3 => -2
    | _ => 0

/-- The nine rows listed in the source atom. -/
def certifiedRows : List ℕ := [4, 8, 9, 12, 13, 14, 15, 16, 17]

/-- Quotient and remainder give the selected pole order and layer. -/
theorem quotient_remainder_layer (a : ℕ) :
    a = 4 * (a / 4) + a % 4 ∧ a % 4 < 4 := by
  constructor
  · simpa [add_comm] using (Nat.mod_add_div a 4).symm
  · exact Nat.mod_lt a (by norm_num)

/-- For every row at least four, the selected order is positive and the
fourth-order pole shift reads exactly the remainder layer. -/
theorem selected_pole_layer_coefficient
    (regular : ℚ⟦X⟧) (residue : ℚ) (a : ℕ) (ha : 4 ≤ a) :
    0 < a / 4 ∧
      coeff a
          (C (((-1 : ℚ) ^ (a / 4 - 1) / ((a / 4 : ℕ) : ℚ)) * residue) *
            X ^ (4 * (a / 4)) * (regular⁻¹) ^ (a / 4)) =
        ((-1 : ℚ) ^ (a / 4 - 1) / ((a / 4 : ℕ) : ℚ)) *
          coeff (a % 4) ((regular⁻¹) ^ (a / 4)) * residue := by
  have hOrder : 0 < a / 4 := by omega
  have hShift : 4 * (a / 4) ≤ a := by omega
  constructor
  · exact hOrder
  · have h := pole_layer_coefficient regular residue a ⟨a / 4, hOrder⟩ hShift
    rw [show a - 4 * (a / 4) = a % 4 by omega] at h
    exact h

private theorem coeff_regularPartHead (n : ℕ) :
    coeff n regularPartHead =
      match n with
      | 0 => 1
      | 1 => 2
      | 2 => -2
      | 3 => -2
      | _ => 0 := by
  simp [regularPartHead]

private theorem constantCoeff_regularPartHead : constantCoeff regularPartHead = 1 := by
  simp [regularPartHead]

private theorem coeff_inverse_zero : coeff 0 regularPartHead⁻¹ = 1 := by
  simp [coeff_zero_eq_constantCoeff_apply, regularPartHead]

private theorem coeff_inverse_one : coeff 1 regularPartHead⁻¹ = -2 := by
  rw [coeff_inv]
  norm_num [Finset.Nat.sum_antidiagonal_succ, coeff_regularPartHead,
    coeff_inverse_zero, constantCoeff_regularPartHead]

private theorem coeff_inverse_two : coeff 2 regularPartHead⁻¹ = 6 := by
  rw [coeff_inv]
  norm_num [Finset.Nat.sum_antidiagonal_succ, coeff_regularPartHead,
    coeff_inverse_zero, coeff_inverse_one, constantCoeff_regularPartHead]

private theorem coeff_inverse_three : coeff 3 regularPartHead⁻¹ = -14 := by
  rw [coeff_inv]
  norm_num [Finset.Nat.sum_antidiagonal_succ, coeff_regularPartHead,
    coeff_inverse_zero, coeff_inverse_one, coeff_inverse_two,
    constantCoeff_regularPartHead]

/-- Direct normalization certifies all nine `(row, order, layer)` selections. -/
theorem nine_row_certificate :
    certifiedRows.map (fun a => (a, a / 4, a % 4)) =
      [(4, 1, 0), (8, 2, 0), (9, 2, 1), (12, 3, 0), (13, 3, 1),
        (14, 3, 2), (15, 3, 3), (16, 4, 0), (17, 4, 1)] := by
  norm_num [certifiedRows]

/-- The exact regular-part readings used by the nine-row table, including the
new depth-two and depth-three values `30`, `-122`, and `-8`. -/
theorem exact_low_layer_readings :
    coeff 0 ((regularPartHead⁻¹) ^ 1) = 1 ∧
      coeff 0 ((regularPartHead⁻¹) ^ 2) = 1 ∧
      coeff 1 ((regularPartHead⁻¹) ^ 2) = -4 ∧
      coeff 0 ((regularPartHead⁻¹) ^ 3) = 1 ∧
      coeff 1 ((regularPartHead⁻¹) ^ 3) = -6 ∧
      coeff 2 ((regularPartHead⁻¹) ^ 3) = 30 ∧
      coeff 3 ((regularPartHead⁻¹) ^ 3) = -122 ∧
      coeff 0 ((regularPartHead⁻¹) ^ 4) = 1 ∧
      coeff 1 ((regularPartHead⁻¹) ^ 4) = -8 := by
  norm_num [pow_succ, PowerSeries.coeff_mul, coeff_inverse_zero,
    coeff_inverse_one, coeff_inverse_two, coeff_inverse_three,
    Finset.Nat.sum_antidiagonal_succ]

/-- Exact fourth-order layer selection together with all nine row and reading
certificates from the source theorem. -/
theorem exact_pole_layer_selection :
    (∀ a : ℕ, a = 4 * (a / 4) + a % 4 ∧ a % 4 < 4) ∧
      certifiedRows.map (fun a => (a, a / 4, a % 4)) =
        [(4, 1, 0), (8, 2, 0), (9, 2, 1), (12, 3, 0), (13, 3, 1),
          (14, 3, 2), (15, 3, 3), (16, 4, 0), (17, 4, 1)] ∧
      coeff 2 ((regularPartHead⁻¹) ^ 3) = 30 ∧
      coeff 3 ((regularPartHead⁻¹) ^ 3) = -122 ∧
      coeff 1 ((regularPartHead⁻¹) ^ 4) = -8 := by
  refine ⟨quotient_remainder_layer, nine_row_certificate, ?_⟩
  rcases exact_low_layer_readings with
    ⟨_, _, _, _, _, hThirty, hNegOneTwentyTwo, _, hNegEight⟩
  exact ⟨hThirty, hNegOneTwentyTwo, hNegEight⟩

end

end D5.S3.Analytic.ExactPoleLayerSelection

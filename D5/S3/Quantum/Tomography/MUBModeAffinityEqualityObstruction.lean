/- GID: D5/S3/Quantum/Tomography/MUBModeAffinityEqualityObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeAffinityEqualityObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The symmetry-budget equality locus is empty once its projector saturation quadratic is imposed: each mode column has one of three quantized collisions, none compatible with six row collisions equal to two-thirds. -/

import D5.S3.Quantum.Tomography.MUBModeAffinityEquality

/- Library-search audit trail (2026-09-04):
   * Reuses `threeModeCollision` and the established affinity-equality chain.
   * Reuses Mathlib's `Fin.sum_univ_six`, `mul_eq_zero`, and nonlinear
     arithmetic. No second collision, affinity, or probability-table carrier
     is introduced.
   * The public theorem is deliberately stronger than its probability-table
     application: nonnegativity and row normalization are not needed after the
     column sums, row collisions, and saturation quadratic are available.
-/

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeAffinityEqualityObstruction

open D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

private def columnCollision
    (p : Fin 6 → Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  ∑ i, (p i k) ^ 2

/-- Six real values with total two and the pairwise saturation law

`(x_i - x_j)(x_i + x_j - 1) = 0`

have column collision exactly `2/3`, `7/8`, or `2`. These are respectively
the uniform, `3/4 + 5 × 1/4`, and `2 × 1 + 4 × 0` spectra, up to permutation.
The proof checks only the five binary choices relative to one reference value. -/
private theorem six_column_collision_quantized
    (x : Fin 6 → ℝ)
    (hsum : ∑ i, x i = 2)
    (hquadratic : ∀ i j,
      (x i - x j) * (x i + x j - 1) = 0) :
    (∑ i, (x i) ^ 2) = (2 / 3 : ℝ) ∨
      (∑ i, (x i) ^ 2) = (7 / 8 : ℝ) ∨
      (∑ i, (x i) ^ 2) = 2 := by
  have h1 := mul_eq_zero.mp (hquadratic 1 0)
  have h2 := mul_eq_zero.mp (hquadratic 2 0)
  have h3 := mul_eq_zero.mp (hquadratic 3 0)
  have h4 := mul_eq_zero.mp (hquadratic 4 0)
  have h5 := mul_eq_zero.mp (hquadratic 5 0)
  rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;>
    rcases h4 with h4 | h4 <;>
    rcases h5 with h5 | h5
  all_goals
    simp only [Fin.sum_univ_six] at hsum ⊢
    first
    | left; nlinarith
    | right; left; nlinarith
    | right; right; nlinarith

/-- There is no saturated six-by-three mode table with column mass two, row
collision `2/3`, and the projector saturation quadratic. The hypotheses are
exactly the nontrivial algebraic output needed after the MUB symmetry budget
has forced equality. -/
theorem no_saturated_mode_probability_table
    (p : Fin 6 → Fin 3 → ℝ)
    (hcolumn : ∀ k, ∑ i, p i k = 2)
    (hrowCollision : ∀ i,
      threeModeCollision (p i) = (2 / 3 : ℝ))
    (hquadratic : ∀ k i j,
      (p i k - p j k) * (p i k + p j k - 1) = 0) :
    False := by
  have hcol0 :
      columnCollision p 0 = (2 / 3 : ℝ) ∨
        columnCollision p 0 = (7 / 8 : ℝ) ∨
        columnCollision p 0 = 2 := by
    simpa [columnCollision] using
      six_column_collision_quantized
        (fun i ↦ p i 0) (hcolumn 0) (hquadratic 0)
  have hcol1 :
      columnCollision p 1 = (2 / 3 : ℝ) ∨
        columnCollision p 1 = (7 / 8 : ℝ) ∨
        columnCollision p 1 = 2 := by
    simpa [columnCollision] using
      six_column_collision_quantized
        (fun i ↦ p i 1) (hcolumn 1) (hquadratic 1)
  have hcol2 :
      columnCollision p 2 = (2 / 3 : ℝ) ∨
        columnCollision p 2 = (7 / 8 : ℝ) ∨
        columnCollision p 2 = 2 := by
    simpa [columnCollision] using
      six_column_collision_quantized
        (fun i ↦ p i 2) (hcolumn 2) (hquadratic 2)
  have htotal :
      columnCollision p 0 + columnCollision p 1 +
        columnCollision p 2 = 4 := by
    have h0 := hrowCollision 0
    have h1 := hrowCollision 1
    have h2 := hrowCollision 2
    have h3 := hrowCollision 3
    have h4 := hrowCollision 4
    have h5 := hrowCollision 5
    simp only [threeModeCollision] at h0 h1 h2 h3 h4 h5
    simp only [columnCollision, Fin.sum_univ_six]
    nlinarith
  rcases hcol0 with hcol0 | hcol0 | hcol0 <;>
    rcases hcol1 with hcol1 | hcol1 | hcol1 <;>
    rcases hcol2 with hcol2 | hcol2 | hcol2
  all_goals
    rw [hcol0, hcol1, hcol2] at htotal
    norm_num at htotal

#print axioms no_saturated_mode_probability_table

end D5.S3.Quantum.Tomography.MUBModeAffinityEqualityObstruction

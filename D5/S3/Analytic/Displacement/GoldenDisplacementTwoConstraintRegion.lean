/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementTwoConstraintRegion
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reduces golden displacement summability to its first two affine constraints. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementRedundantConstraint

/-! SEARCH RECEIPT

Repository prefix search:
* `grep -rnE "^(theorem|lemma) (goldenSubstStart|golden_subst_start)" D5`
  found the public upper bound `goldenSubstStart_le_two_mul`, the public linear
  lower bound `goldenSubstStart_linear_lower_bound`, and the finite value table
  `goldenSubstStart_one_through_eight`.
* Searches for bodies containing `3 * v <= 2 * goldenSubstStart v`, its Unicode
  form, and the pair `2 * s + w` / `3 * s + 2 * w` found no existing lower bound
  or two-constraint summability reduction.

Pinned Mathlib search:
* Found and reused `Real.goldenRatio_sq` and `Real.one_lt_goldenRatio`; they give
  the exact rational estimate `8 / 5 <= Real.goldenRatio` without decimals.
* `golden_window_true_discrepancy` was also found, but the merged linear lower
  bound is closer to the target inequality and gives the exact cutoff `v >= 4`.
-/

open D5.S1.Words
open GoldenDisplacementEulerProduct
open GoldenDisplacementSurfaceRegion
open GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

namespace GoldenDisplacementTwoConstraintRegion

noncomputable section

/-- Every nonzero substitution start lies above three halves of its index. -/
theorem three_mul_le_two_mul_goldenSubstStart (v : ℕ) (hv : 1 ≤ v) :
    3 * v ≤ 2 * goldenSubstStart v := by
  by_cases hvLarge : 4 ≤ v
  · have hphi : (8 : ℝ) / 5 ≤ Real.goldenRatio := by
      nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio]
    have hvReal : (4 : ℝ) ≤ (v : ℝ) := by
      exact_mod_cast hvLarge
    have hscaled := mul_le_mul_of_nonneg_right hphi (by positivity : (0 : ℝ) ≤ v)
    have hlinear := goldenSubstStart_linear_lower_bound v
    have hreal : 3 * (v : ℝ) ≤ 2 * (goldenSubstStart v : ℝ) := by
      nlinarith
    exact_mod_cast hreal
  · interval_cases v <;> decide

/-- A nonempty substitution prefix starts at least one place beyond its index. -/
theorem add_one_le_goldenSubstStart (v : ℕ) (hv : 1 ≤ v) :
    v + 1 ≤ goldenSubstStart v := by
  by_cases hvOne : v = 1
  · subst v
    decide
  · have hvTwo : 2 ≤ v := by omega
    have hlower := three_mul_le_two_mul_goldenSubstStart v hv
    omega

/-- The criterion at `v` is the indicated linear combination of its first two values. -/
theorem criterion_eq_first_two_combination (s w : ℝ) (v : ℕ) :
    s * (goldenSubstStart v : ℝ) + w * v =
      (2 * (goldenSubstStart v : ℝ) - 3 * v) * (2 * s + w) +
        (2 * v - (goldenSubstStart v : ℝ)) * (3 * s + 2 * w) := by
  ring

/-- The two combination coefficients are nonnegative and have sum at least one. -/
theorem golden_combination_coefficients (v : ℕ) (hv : 1 ≤ v) :
    0 ≤ 2 * (goldenSubstStart v : ℝ) - 3 * v ∧
      0 ≤ 2 * v - (goldenSubstStart v : ℝ) ∧
      (2 * (goldenSubstStart v : ℝ) - 3 * v) +
          (2 * v - (goldenSubstStart v : ℝ)) =
        (goldenSubstStart v : ℝ) - v ∧
      1 ≤ (2 * (goldenSubstStart v : ℝ) - 3 * v) +
        (2 * v - (goldenSubstStart v : ℝ)) := by
  have hlowerNat := three_mul_le_two_mul_goldenSubstStart v hv
  have hupperNat := goldenSubstStart_le_two_mul v
  have hgapNat := add_one_le_goldenSubstStart v hv
  have hlower : 3 * (v : ℝ) ≤ 2 * (goldenSubstStart v : ℝ) := by
    exact_mod_cast hlowerNat
  have hupper : (goldenSubstStart v : ℝ) ≤ 2 * (v : ℝ) := by
    exact_mod_cast hupperNat
  have hgap : (v : ℝ) + 1 ≤ (goldenSubstStart v : ℝ) := by
    exact_mod_cast hgapNat
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

/-- The first two strict constraints imply every actual-index constraint. -/
theorem criterion_of_first_two {s w : ℝ} (v : ℕ) (hv : 1 ≤ v)
    (hfirst : 1 < 2 * s + w) (hsecond : 1 < 3 * s + 2 * w) :
    1 < s * (goldenSubstStart v : ℝ) + w * v := by
  let a : ℝ := 2 * (goldenSubstStart v : ℝ) - 3 * v
  let b : ℝ := 2 * v - (goldenSubstStart v : ℝ)
  have hcoeff := golden_combination_coefficients v hv
  have ha : 0 ≤ a := by simpa [a] using hcoeff.1
  have hb : 0 ≤ b := by simpa [b] using hcoeff.2.1
  have hab : 1 ≤ a + b := by simpa [a, b] using hcoeff.2.2.2
  have hweighted : a + b < a * (2 * s + w) + b * (3 * s + 2 * w) := by
    by_cases haZero : a = 0
    · have hbPos : 0 < b := by linarith
      have hbGain : 0 < b * ((3 * s + 2 * w) - 1) :=
        mul_pos hbPos (by linarith)
      nlinarith
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm haZero)
      have haGain : 0 < a * ((2 * s + w) - 1) :=
        mul_pos haPos (by linarith)
      have hbGain : 0 ≤ b * ((3 * s + 2 * w) - 1) :=
        mul_nonneg hb (by linarith)
      nlinarith
  calc
    1 ≤ a + b := hab
    _ < a * (2 * s + w) + b * (3 * s + 2 * w) := hweighted
    _ = s * (goldenSubstStart v : ℝ) + w * v := by
      simpa [a, b] using (criterion_eq_first_two_combination s w v).symm

/-- Golden displacement summability is exactly the intersection of two open half-planes. -/
theorem dTerm_summable_iff_two_constraints (s w : ℝ) :
    Summable (dTerm s w) ↔
      1 < 2 * s + w ∧ 1 < 3 * s + 2 * w := by
  constructor
  · intro hsum
    have hfamily :=
      (GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff s w).mp hsum
    have hzero := hfamily 0
    have hone := hfamily 1
    have hgOne : goldenSubstStart 1 = 2 := by decide
    have hgTwo : goldenSubstStart 2 = 3 := by decide
    norm_num [hgOne] at hzero
    norm_num [hgTwo] at hone
    constructor <;> linarith
  · intro hlines
    rw [GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff]
    intro k
    have hv := criterion_of_first_two (k + 1) (by omega) hlines.1 hlines.2
    simpa only [Nat.cast_add, Nat.cast_one] using hv

/-- On the negative side, the second constraint follows algebraically from the first. -/
theorem two_constraints_iff_first_of_neg {s w : ℝ} (hs : s < 0) :
    (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔ 1 < 2 * s + w := by
  constructor
  · exact And.left
  · intro hfirst
    constructor
    · exact hfirst
    · nlinarith

/-- The positive witness satisfies the first constraint but fails the second at equality. -/
theorem first_constraint_not_sufficient :
    1 < 2 * (3 : ℝ) + (-4) ∧
      3 * (3 : ℝ) + 2 * (-4) = 1 ∧
      ¬Summable (dTerm 3 (-4)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro hsum
  have hlines := (dTerm_summable_iff_two_constraints 3 (-4)).mp hsum
  norm_num at hlines

/-- The second constraint alone does not imply the first or summability. -/
theorem second_constraint_not_sufficient :
    1 < 3 * (0 : ℝ) + 2 * (3 / 5) ∧
      ¬1 < 2 * (0 : ℝ) + 3 / 5 ∧
      ¬Summable (dTerm 0 (3 / 5)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro hsum
  have hlines := (dTerm_summable_iff_two_constraints 0 (3 / 5)).mp hsum
  norm_num at hlines

end

end GoldenDisplacementTwoConstraintRegion

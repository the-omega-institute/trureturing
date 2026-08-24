/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementBindingConstraint
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Gives the critical displacement boundary and identifies its binding constraint. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

open D5.S1.Words
open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion

namespace GoldenDisplacementBindingConstraint

noncomputable section

/-- The lower endpoint for `w` in the golden displacement convergence region. -/
def goldenDisplacementCriticalBoundary (s : ℝ) : ℝ :=
  max (1 - 2 * s) ((1 - 3 * s) / 2)

/-- At and below the crossing slope, the first constraint implies the second. -/
theorem two_constraints_iff_first_of_le_one {s w : ℝ} (hs : s ≤ 1) :
    (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔ 1 < 2 * s + w := by
  constructor
  · exact And.left
  · intro hfirst
    constructor
    · exact hfirst
    · linarith

/-- At and above the crossing slope, the second constraint implies the first. -/
theorem two_constraints_iff_second_of_one_le {s w : ℝ} (hs : 1 ≤ s) :
    (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔ 1 < 3 * s + 2 * w := by
  constructor
  · exact And.right
  · intro hsecond
    constructor
    · linarith
    · exact hsecond

/-- Below the crossing, the critical boundary is the first affine boundary. -/
theorem critical_boundary_eq_first_of_le_one {s : ℝ} (hs : s ≤ 1) :
    goldenDisplacementCriticalBoundary s = 1 - 2 * s := by
  apply max_eq_left
  linarith

/-- Above the crossing, the critical boundary is the second affine boundary. -/
theorem critical_boundary_eq_second_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    goldenDisplacementCriticalBoundary s = (1 - 3 * s) / 2 := by
  apply max_eq_right
  linarith

/-- The first affine expression is the critical boundary exactly below the crossing. -/
theorem critical_boundary_eq_first_iff_le_one (s : ℝ) :
    goldenDisplacementCriticalBoundary s = 1 - 2 * s ↔ s ≤ 1 := by
  constructor
  · intro hboundary
    have hle : (1 - 3 * s) / 2 ≤ 1 - 2 * s := by
      calc
        (1 - 3 * s) / 2 ≤
            max (1 - 2 * s) ((1 - 3 * s) / 2) := le_max_right _ _
        _ = 1 - 2 * s := hboundary
    linarith
  · exact critical_boundary_eq_first_of_le_one

/-- The second affine expression is the critical boundary exactly above the crossing. -/
theorem critical_boundary_eq_second_iff_one_le (s : ℝ) :
    goldenDisplacementCriticalBoundary s = (1 - 3 * s) / 2 ↔ 1 ≤ s := by
  constructor
  · intro hboundary
    have hle : 1 - 2 * s ≤ (1 - 3 * s) / 2 := by
      calc
        1 - 2 * s ≤ max (1 - 2 * s) ((1 - 3 * s) / 2) := le_max_left _ _
        _ = (1 - 3 * s) / 2 := hboundary
    linarith
  · exact critical_boundary_eq_second_of_one_le

/-- On the low-slope side, summability is exactly the first strict constraint. -/
theorem dTerm_summable_iff_first_of_le_one {s w : ℝ} (hs : s ≤ 1) :
    Summable (dTerm s w) ↔ 1 < 2 * s + w := by
  calc
    Summable (dTerm s w) ↔
        1 < 2 * s + w ∧ 1 < 3 * s + 2 * w :=
      dTerm_summable_iff_two_constraints s w
    _ ↔ 1 < 2 * s + w := two_constraints_iff_first_of_le_one hs

/-- On the high-slope side, summability is exactly the second strict constraint. -/
theorem dTerm_summable_iff_second_of_one_le {s w : ℝ} (hs : 1 ≤ s) :
    Summable (dTerm s w) ↔ 1 < 3 * s + 2 * w := by
  calc
    Summable (dTerm s w) ↔
        1 < 2 * s + w ∧ 1 < 3 * s + 2 * w :=
      dTerm_summable_iff_two_constraints s w
    _ ↔ 1 < 3 * s + 2 * w := two_constraints_iff_second_of_one_le hs

/-- The convergence region is the strict epigraph of one critical-boundary function. -/
theorem dTerm_summable_iff_critical_boundary (s w : ℝ) :
    Summable (dTerm s w) ↔ goldenDisplacementCriticalBoundary s < w := by
  rw [dTerm_summable_iff_two_constraints]
  change
    (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔
      max (1 - 2 * s) ((1 - 3 * s) / 2) < w
  rw [max_lt_iff]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    constructor <;> linarith
  · rintro ⟨hfirst, hsecond⟩
    constructor <;> linarith

/-- The two affine constraints are simultaneously tight only at their crossing point. -/
theorem both_constraints_tight_iff {s w : ℝ} :
    (2 * s + w = 1 ∧ 3 * s + 2 * w = 1) ↔ s = 1 ∧ w = -1 := by
  constructor
  · rintro ⟨hfirst, hsecond⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- The first constraint can hold alone exactly above the crossing slope. -/
theorem first_constraint_only_iff_one_lt (s : ℝ) :
    (∃ w : ℝ,
      1 < 2 * s + w ∧
        ¬1 < 3 * s + 2 * w ∧
        ¬Summable (dTerm s w)) ↔
      1 < s := by
  constructor
  · rintro ⟨w, hfirst, hsecond, _⟩
    have hsecond' : 3 * s + 2 * w ≤ 1 := le_of_not_gt hsecond
    linarith
  · intro hs
    let w := (1 - 3 * s) / 2
    have hfirst : 1 < 2 * s + w := by
      dsimp [w]
      linarith
    have hsecond : ¬1 < 3 * s + 2 * w := by
      dsimp [w]
      linarith
    refine ⟨w, hfirst, hsecond, ?_⟩
    intro hsum
    exact hsecond (dTerm_summable_iff_two_constraints s w |>.mp hsum).2

/-- The second constraint can hold alone exactly below the crossing slope. -/
theorem second_constraint_only_iff_lt_one (s : ℝ) :
    (∃ w : ℝ,
      1 < 3 * s + 2 * w ∧
        ¬1 < 2 * s + w ∧
        ¬Summable (dTerm s w)) ↔
      s < 1 := by
  constructor
  · rintro ⟨w, hsecond, hfirst, _⟩
    have hfirst' : 2 * s + w ≤ 1 := le_of_not_gt hfirst
    linarith
  · intro hs
    let w := 1 - 2 * s
    have hsecond : 1 < 3 * s + 2 * w := by
      dsimp [w]
      linarith
    have hfirst : ¬1 < 2 * s + w := by
      dsimp [w]
      linarith
    refine ⟨w, hsecond, hfirst, ?_⟩
    intro hsum
    exact hfirst (dTerm_summable_iff_two_constraints s w |>.mp hsum).1

/-- The first constraint is uniformly binding exactly at or below the crossing slope. -/
theorem two_constraints_iff_first_forall_iff_le_one (s : ℝ) :
    (∀ w : ℝ,
      (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔ 1 < 2 * s + w) ↔
      s ≤ 1 := by
  constructor
  · intro huniform
    by_contra hs
    obtain ⟨w, hfirst, hsecond, _⟩ :=
      (first_constraint_only_iff_one_lt s).2 (lt_of_not_ge hs)
    exact hsecond ((huniform w).2 hfirst).2
  · intro hs w
    exact two_constraints_iff_first_of_le_one hs

/-- The second constraint is uniformly binding exactly at or above the crossing slope. -/
theorem two_constraints_iff_second_forall_iff_one_le (s : ℝ) :
    (∀ w : ℝ,
      (1 < 2 * s + w ∧ 1 < 3 * s + 2 * w) ↔ 1 < 3 * s + 2 * w) ↔
      1 ≤ s := by
  constructor
  · intro huniform
    by_contra hs
    obtain ⟨w, hsecond, hfirst, _⟩ :=
      (second_constraint_only_iff_lt_one s).2 (lt_of_not_ge hs)
    exact hfirst ((huniform w).2 hsecond).1
  · intro hs w
    exact two_constraints_iff_second_of_one_le hs

/-- The three-halves lower bound also holds at the omitted degenerate index `v = 0`. -/
theorem three_mul_le_two_mul_goldenSubstStart (v : ℕ) :
    3 * v ≤ 2 * goldenSubstStart v := by
  by_cases hv : v = 0
  · subst v
    simpa only [mul_zero] using (Nat.zero_le (2 * goldenSubstStart 0))
  · exact
      GoldenDisplacementTwoConstraintRegion.three_mul_le_two_mul_goldenSubstStart
        v (Nat.one_le_iff_ne_zero.mpr hv)

end

end GoldenDisplacementBindingConstraint

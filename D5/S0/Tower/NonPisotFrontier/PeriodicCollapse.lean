/- GID: D5/S0/Tower/NonPisotFrontier/PeriodicCollapse
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/PeriodicCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A periodic digit block leaves exactly one bounded conjugate orbit. -/

import D5.S0.Tower.NonPisotFrontier.BetaThirteen

/- Library-search audit trail (2026-08-18):
   * Repository search found the frontier base and its conjugate modulus;
     nothing states what a periodic digit block does to a conjugate orbit.
   * Pinned Mathlib supplies `one_lt_pow₀`, `abs_pow` and
     `pow_unbounded_of_one_lt`; the collapse itself is elementary once the
     period-`p` step is read as an affine map with an expanding multiplier. -/

namespace D5.S0.Tower.NonPisotFrontier.PeriodicCollapse

open D5.S0.Tower.NonPisotFrontier.BetaThirteen

local notation "β'" => betaThirteenConjugate

/-- Raising the conjugate modulus to a nonzero period keeps it above one. -/
theorem one_lt_abs_pow {p : ℕ} (hp : p ≠ 0) : 1 < |β'| ^ p :=
  one_lt_pow₀ one_lt_abs_betaThirteenConjugate hp

/-- Hence no nonzero power of the conjugate is the identity multiplier. -/
theorem conjugate_pow_ne_one {p : ℕ} (hp : p ≠ 0) : β' ^ p ≠ 1 := by
  intro h
  have habs : |β' ^ p| = 1 := by rw [h]; exact abs_one
  rw [abs_pow] at habs
  exact absurd habs (ne_of_gt (one_lt_abs_pow hp))

/-- The one point a period-`p` block with accumulated digit `c` leaves fixed. -/
noncomputable def collapseCentre (p : ℕ) (c : Real) : Real := c / (β' ^ p - 1)

/-- It is fixed: the block sends the centre to itself. -/
theorem collapseCentre_spec {p : ℕ} (hp : p ≠ 0) (c : Real) :
    β' ^ p * collapseCentre p c - c = collapseCentre p c := by
  have hne : β' ^ p - 1 ≠ 0 := sub_ne_zero.mpr (conjugate_pow_ne_one hp)
  simp only [collapseCentre]
  field_simp
  ring

/-- One block multiplies the distance to the centre by the modulus to the period. -/
theorem collapse_step_distance {p : ℕ} (hp : p ≠ 0) (c y : Real) :
    |(β' ^ p * y - c) - collapseCentre p c| = |β'| ^ p * |y - collapseCentre p c| := by
  have hne : β' ^ p - 1 ≠ 0 := sub_ne_zero.mpr (conjugate_pow_ne_one hp)
  have key : (β' ^ p * y - c) - collapseCentre p c
      = β' ^ p * (y - collapseCentre p c) := by
    simp only [collapseCentre]
    field_simp
    ring
  rw [key, abs_mul, abs_pow]

/-- Iterating the period-`p` block. -/
noncomputable def collapseIterate (p : ℕ) (c : Real) : ℕ → Real → Real
  | 0, y => y
  | (k + 1), y => β' ^ p * collapseIterate p c k y - c

/-- After `k` blocks the distance to the centre has been multiplied `k` times. -/
theorem collapseIterate_distance {p : ℕ} (hp : p ≠ 0) (c y : Real) (k : ℕ) :
    |collapseIterate p c k y - collapseCentre p c|
      = (|β'| ^ p) ^ k * |y - collapseCentre p c| := by
  induction k with
  | zero => simp [collapseIterate]
  | succ k ih =>
      rw [collapseIterate, collapse_step_distance hp, ih, pow_succ]
      ring

/-- Starting at the centre, every iterate stays there. -/
theorem collapse_centre_is_stationary {p : ℕ} (hp : p ≠ 0) (c : Real) (k : ℕ) :
    collapseIterate p c k (collapseCentre p c) = collapseCentre p c := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [collapseIterate, ih]
      exact collapseCentre_spec hp c

/-- Starting anywhere else, the iterates pass every bound. -/
theorem collapse_escapes_off_centre {p : ℕ} (hp : p ≠ 0) (c y : Real)
    (hy : y ≠ collapseCentre p c) (bound : Real) :
    ∃ k : ℕ, bound < |collapseIterate p c k y - collapseCentre p c| := by
  have hpos : 0 < |y - collapseCentre p c| := abs_pos.mpr (sub_ne_zero.mpr hy)
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (bound / |y - collapseCentre p c|) (one_lt_abs_pow hp)
  refine ⟨k, ?_⟩
  rw [collapseIterate_distance hp]
  have hsplit : bound
      = bound / |y - collapseCentre p c| * |y - collapseCentre p c| := by
    field_simp
  rw [hsplit]
  exact mul_lt_mul_of_pos_right hk hpos

/-- A periodic digit block admits exactly one bounded conjugate orbit. -/
theorem periodic_block_collapses_to_one_orbit {p : ℕ} (hp : p ≠ 0) (c y : Real) :
    (y = collapseCentre p c → ∀ k : ℕ, collapseIterate p c k y = y) ∧
      (y ≠ collapseCentre p c →
        ∀ bound : Real, ∃ k : ℕ, bound < |collapseIterate p c k y - collapseCentre p c|) := by
  constructor
  · intro hy k
    rw [hy]
    exact collapse_centre_is_stationary hp c k
  · intro hy bound
    exact collapse_escapes_off_centre hp c y hy bound

end D5.S0.Tower.NonPisotFrontier.PeriodicCollapse

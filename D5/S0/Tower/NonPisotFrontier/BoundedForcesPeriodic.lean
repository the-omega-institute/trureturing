/- GID: D5/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic
   generality: G
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/BoundedForcesPeriodic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Under an expanding multiplier a bounded orbit is zero, so periodic digits repeat. -/

import Mathlib.Analysis.Real.Sqrt

/- Library-search audit trail (2026-08-18):
   * Searched on the shape rather than on a name: an orbit of `w ↦ c * w` that
     stays bounded when `1 < |c|`.  The repository has expanding-step lemmas for
     the frontier conjugate specifically, none stated for an arbitrary
     multiplier, and none about what periodic digits do to the remainders.
   * This module is general, so by SL-010 it may not import the instance-level
     frontier artifacts.  Everything tying it to that base lives one tier down,
     in `CollapseIsExpanding`.
   * Pinned Mathlib supplies `pow_unbounded_of_one_lt`, `abs_pow` and `abs_le`;
     the argument uses nothing else. -/

namespace D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic


/-- Along an expanding linear step the distance from the origin is exact. -/
theorem abs_orbit_eq {c : Real} {w : Nat → Real}
    (hstep : ∀ k, w (k + 1) = c * w k) (k : Nat) : |w k| = |c| ^ k * |w 0| := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [hstep, abs_mul, ih, pow_succ]
      ring

/-- A bounded orbit of an expanding linear map is the zero orbit. -/
theorem bounded_expanding_orbit_is_zero {c M : Real} {w : Nat → Real}
    (hc : 1 < |c|) (hstep : ∀ k, w (k + 1) = c * w k)
    (hbound : ∀ k, |w k| ≤ M) : ∀ k, w k = 0 := by
  have hzero : w 0 = 0 := by
    by_contra hne
    have hpos : 0 < |w 0| := abs_pos.mpr hne
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (M / |w 0|) hc
    have hsplit : M = M / |w 0| * |w 0| := by field_simp
    have hgt : M < |c| ^ k * |w 0| := by
      rw [hsplit]
      exact mul_lt_mul_of_pos_right hk hpos
    have := hbound k
    rw [abs_orbit_eq hstep k] at this
    linarith
  intro k
  have habs : |w k| = 0 := by rw [abs_orbit_eq hstep k, hzero]; simp
  exact abs_eq_zero.mp habs

/-- Eventually periodic digits force a bounded orbit to repeat with the same period. -/
theorem periodic_digits_force_periodic_orbit {c M : Real} {p N : Nat} {r d : Nat → Real}
    (hc : 1 < |c|) (hrec : ∀ n, r (n + 1) = c * r n - d n)
    (hbound : ∀ n, |r n| ≤ M) (hper : ∀ n, N ≤ n → d (n + p) = d n) :
    ∀ n, N ≤ n → r (n + p) = r n := by
  have key : ∀ k : Nat, r (N + k + p) - r (N + k) = 0 := by
    refine bounded_expanding_orbit_is_zero (c := c) (M := 2 * M)
      (w := fun j => r (N + j + p) - r (N + j)) hc ?_ ?_
    · intro k
      show r (N + (k + 1) + p) - r (N + (k + 1))
        = c * (r (N + k + p) - r (N + k))
      have h1 : N + (k + 1) + p = (N + k + p) + 1 := by omega
      have h2 : N + (k + 1) = (N + k) + 1 := by omega
      rw [h1, h2, hrec, hrec, hper (N + k) (Nat.le_add_right N k)]
      ring
    · intro k
      show |r (N + k + p) - r (N + k)| ≤ 2 * M
      have h1 := abs_le.mp (hbound (N + k + p))
      have h2 := abs_le.mp (hbound (N + k))
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  intro n hn
  have h3 : N + (n - N) = n := by omega
  have hk := key (n - N)
  rw [h3] at hk
  linarith


end D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic

/- GID: D5/S0/Tower/NonPisotVerdict/ConjugateUnbounded
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotVerdict/ConjugateUnbounded
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The conjugate orbit of one passes every bound, so it is not bounded. -/

import D5.S0.Tower.NonPisotFrontier.ConjugateValuation
import D5.S0.Tower.NonPisotFrontier.EscapeIteration
import D5.S0.Tower.NonPisotFrontier.OrbitWitness

/- Library-search audit trail (2026-08-18):
   * Every ingredient is already in the tree and none is restated: the witness
     at the fourth step, the digit range, the one-step escape estimate and the
     multiplicative growth of the excess.  This module only composes them.
   * A separate directory: `NonPisotFrontier` holds nine modules, the two in
     flight bring it to eleven, and the conclusions need two more, which would
     exceed the twelve-entry limit.  The machinery stays there; verdicts live
     here.
   * Pinned Mathlib supplies `pow_unbounded_of_one_lt`; nothing else is used. -/

namespace D5.S0.Tower.NonPisotVerdict.ConjugateUnbounded

open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisotFrontier.EscapeThreshold
open D5.S0.Tower.NonPisotFrontier.EscapeIteration
open D5.S0.Tower.NonPisotFrontier.OrbitWitness
open D5.S0.Tower.NonPisotFrontier.ConjugateValuation
open D5.S0.Tower.NonPisot.Beta13Infinite

local notation "β'" => betaThirteenConjugate
local notation "K" => escapeThreshold

/-- The digits of the greedy expansion, as reals, lie where the escape estimate
requires them. -/
theorem digit_bounds (n : Nat) :
    (0 : Real) ≤ (beta13GreedyDigit n : Real) ∧ ((beta13GreedyDigit n : Real)) ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := greedyDigit_mem_alphabet n
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- The fourth step of the conjugate orbit is already past the threshold. -/
theorem four_past_threshold : K < |conjugateRemainder 4| := by
  have hwit := conjugate_step4_passes_threshold
  have heq : conjugateRemainder 4 = conjugateStep4 := by
    rw [conjugateRemainder_four, conjugateStep4]
  rw [heq, escapeThreshold]
  exact hwit

/-- And it never comes back. -/
theorem past_threshold_from_four : ∀ k : Nat, K < |conjugateRemainder (4 + k)| := by
  intro k
  induction k with
  | zero => simpa using four_past_threshold
  | succ k ih =>
      have hd := digit_bounds (4 + k)
      have hstep : conjugateRemainder (4 + k + 1)
          = β' * conjugateRemainder (4 + k) - (beta13GreedyDigit (4 + k) : Real) :=
        conjugateRemainder_succ (4 + k)
      have h : K < |β' * conjugateRemainder (4 + k)
          - (beta13GreedyDigit (4 + k) : Real)| := stays_past ih hd.1 hd.2
      have hidx : 4 + (k + 1) = 4 + k + 1 := by omega
      rw [hidx, hstep]
      exact h

/-- The excess above the threshold is multiplied by the conjugate modulus at every
step, so after `k` steps it is at least the modulus to the `k`. -/
theorem excess_lower_bound : ∀ k : Nat,
    K + |β'| ^ k * (|conjugateRemainder 4| - K) ≤ |conjugateRemainder (4 + k)| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hd := digit_bounds (4 + k)
      have hstep : conjugateRemainder (4 + k + 1)
          = β' * conjugateRemainder (4 + k) - (beta13GreedyDigit (4 + k) : Real) :=
        conjugateRemainder_succ (4 + k)
      have hmul := excess_multiplies (past_threshold_from_four k) hd.1 hd.2
      have habs : (0 : Real) ≤ |β'| := abs_nonneg _
      have hidx : 4 + (k + 1) = 4 + k + 1 := by omega
      rw [hidx, hstep]
      have hgrow : |β'| * (|β'| ^ k * (|conjugateRemainder 4| - K))
          ≤ |β'| * (|conjugateRemainder (4 + k)| - K) := by
        have : |β'| ^ k * (|conjugateRemainder 4| - K)
            ≤ |conjugateRemainder (4 + k)| - K := by linarith [ih]
        exact mul_le_mul_of_nonneg_left this habs
      calc K + |β'| ^ (k + 1) * (|conjugateRemainder 4| - K)
          = K + |β'| * (|β'| ^ k * (|conjugateRemainder 4| - K)) := by ring
        _ ≤ K + |β'| * (|conjugateRemainder (4 + k)| - K) := by linarith [hgrow]
        _ ≤ |β' * conjugateRemainder (4 + k)
              - (beta13GreedyDigit (4 + k) : Real)| := hmul

/-- Hence the conjugate orbit of one passes every bound. -/
theorem conjugate_orbit_unbounded (bound : Real) :
    ∃ n : Nat, bound < |conjugateRemainder n| := by
  have hexc : 0 < |conjugateRemainder 4| - K := by
    have := four_past_threshold
    linarith
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt (bound / (|conjugateRemainder 4| - K))
      one_lt_abs_betaThirteenConjugate
  refine ⟨4 + k, ?_⟩
  have hlow := excess_lower_bound k
  have hsplit : bound = bound / (|conjugateRemainder 4| - K) * (|conjugateRemainder 4| - K) := by
    field_simp
  have hgt : bound < |β'| ^ k * (|conjugateRemainder 4| - K) := by
    rw [hsplit]
    exact mul_lt_mul_of_pos_right hk hexc
  have hKpos : 0 < K := escapeThreshold_pos
  linarith

/-- The conjugate reading of the greedy expansion of one is unbounded. -/
theorem the_conjugate_orbit_is_unbounded :
    (∀ k : Nat, K < |conjugateRemainder (4 + k)|) ∧
      ∀ bound : Real, ∃ n : Nat, bound < |conjugateRemainder n| :=
  ⟨past_threshold_from_four, conjugate_orbit_unbounded⟩

end D5.S0.Tower.NonPisotVerdict.ConjugateUnbounded

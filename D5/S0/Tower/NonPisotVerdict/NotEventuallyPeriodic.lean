/- GID: D5/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotVerdict/NotEventuallyPeriodic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The greedy expansion of one at the frontier base is not eventually periodic. -/

import D5.S0.Tower.NonPisotVerdict.ConjugateUnbounded
import D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic
import D5.S0.Tower.NonPisotFrontier.CollapseIsExpanding

/- Library-search audit trail (2026-08-18):
   * Nothing new is proved here either.  The two sides were built separately and
     this is where they meet: an eventual period would bound the conjugate orbit,
     and the escape estimate says it is unbounded.
   * The exact remainder stream, its confinement to the unit interval and the
     injectivity of the code reading all come from `Beta13Infinite`; the rigidity
     of a bounded orbit under an expanding multiplier from `BoundedForcesPeriodic`;
     the base's expansion from `CollapseIsExpanding`; the conjugate reading from
     `ConjugateValuation`; the unboundedness from `ConjugateUnbounded`.
   * Pinned Mathlib supplies `Finset.exists_max_image` and `Finset.nonempty_range_iff`. -/

namespace D5.S0.Tower.NonPisotVerdict.NotEventuallyPeriodic

open D5.S0.Tower.NonPisot.Beta13Infinite
open D5.S0.Tower.NonPisotFrontier.BetaThirteen
open D5.S0.Tower.NonPisotFrontier.BoundedForcesPeriodic
open D5.S0.Tower.NonPisotFrontier.CollapseIsExpanding
open D5.S0.Tower.NonPisotFrontier.ConjugateValuation
open D5.S0.Tower.NonPisotVerdict.ConjugateUnbounded

/-- Periodic digits make the greedy remainders periodic: the remainders are
confined to the unit interval, and the base is expanding. -/
theorem remainder_values_periodic {p N : Nat}
    (hper : ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n) :
    ∀ n, N ≤ n → beta13RemainderValue (n + p) = beta13RemainderValue n := by
  refine periodic_digits_force_periodic_orbit (c := betaThirteen) (M := 1)
    (r := beta13RemainderValue) (d := fun n => (beta13GreedyDigit n : Real))
    frontier_base_is_expanding (fun n => beta13_remainder_value_succ n) ?_ ?_
  · intro n
    obtain ⟨h0, h1⟩ := beta13_remainder_value_in_unit_interval n
    rw [abs_of_nonneg h0]
    exact h1
  · intro n hn
    exact_mod_cast congrArg (fun z : Int => (z : Real)) (hper n hn)

/-- And the codes with them, since the reading at the base is injective. -/
theorem remainder_codes_periodic {p N : Nat}
    (hper : ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n) :
    ∀ n, N ≤ n → beta13RemainderCode (n + p) = beta13RemainderCode n := by
  intro n hn
  exact beta13_code_value_injective (remainder_values_periodic hper n hn)

/-- Periodic codes leave the conjugate orbit only the values it took before the
period closed, and there are finitely many of those. -/
theorem conjugate_bounded_of_periodic {p N : Nat} (hp : 0 < p)
    (hper : ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n) :
    ∃ M : Real, ∀ n : Nat, |conjugateRemainder n| ≤ M := by
  have hfin := conjugateRemainder_eq_early hp (remainder_codes_periodic hper)
  obtain ⟨b, _, hmax⟩ := Finset.exists_max_image (Finset.range (N + p))
    (fun k => |conjugateRemainder k|)
    (Finset.nonempty_range_iff.mpr (by omega))
  refine ⟨|conjugateRemainder b|, fun n => ?_⟩
  obtain ⟨k, hk, hval⟩ := hfin n
  rw [hval]
  exact hmax k (Finset.mem_range.mpr hk)

/-- The greedy expansion of one at the frontier base is not eventually periodic. -/
theorem digits_not_eventually_periodic :
    ¬ ∃ p N : Nat, 0 < p ∧
      ∀ n, N ≤ n → beta13GreedyDigit (n + p) = beta13GreedyDigit n := by
  rintro ⟨p, N, hp, hper⟩
  obtain ⟨M, hM⟩ := conjugate_bounded_of_periodic hp hper
  obtain ⟨n, hn⟩ := conjugate_orbit_unbounded M
  exact absurd (hM n) (not_le.mpr hn)

end D5.S0.Tower.NonPisotVerdict.NotEventuallyPeriodic

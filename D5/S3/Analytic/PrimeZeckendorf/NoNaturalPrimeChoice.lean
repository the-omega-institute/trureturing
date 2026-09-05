/- GID: D5/S3/Analytic/PrimeZeckendorf/NoNaturalPrimeChoice
   generality: I
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every prime is moved by an explicit permutation, so none is globally distinguished. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Equiv.Basic

/- Library-search audit trail (2026-09-05):
   * Statement-shape searches over `D5/` and `Golden/Frozen/accepted/` found no
     theorem moving every `Nat.Primes` value by a permutation.
   * `PrimeRelabelingUnderdetermination` assumes a nonidentity relabeling;
     `SingletonAxisSelectionObstruction` assumes that every axis can be moved;
     neither constructs the prime permutations required here.
   * Pinned Mathlib supplies `Nat.prime_two`, `Nat.prime_three`, `Equiv.swap`,
     and `Equiv.swap_apply_left`, which are reused directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PrimeZeckendorf.NoNaturalPrimeChoice

/-- No natural prime is fixed by every permutation of the prime type: for
each prime, swapping it with either two or three explicitly moves it. -/
theorem no_prime_is_fixed_by_every_permutation :
    ∀ p : Nat.Primes,
      ∃ relabel : Equiv.Perm Nat.Primes, relabel p ≠ p := by
  intro p
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  let three : Nat.Primes := ⟨3, Nat.prime_three⟩
  have htwo_ne_three : two ≠ three := by
    intro h
    have hvalue := congrArg Subtype.val h
    simp [two, three] at hvalue
  by_cases hp : p = two
  · subst p
    refine ⟨Equiv.swap two three, ?_⟩
    have hthree_ne_two : three ≠ two := fun h => htwo_ne_three h.symm
    simpa only [Equiv.swap_apply_left] using hthree_ne_two
  · refine ⟨Equiv.swap p two, ?_⟩
    have htwo_ne_p : two ≠ p := fun h => hp h.symm
    simpa only [Equiv.swap_apply_left] using htwo_ne_p

example : Nat.Primes := ⟨2, Nat.prime_two⟩

#print axioms no_prime_is_fixed_by_every_permutation

end D5.S3.Analytic.PrimeZeckendorf.NoNaturalPrimeChoice

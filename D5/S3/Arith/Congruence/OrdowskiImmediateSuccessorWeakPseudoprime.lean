/- GID: D5/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/OrdowskiImmediateSuccessorWeakPseudoprime
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Ordowski's immediate-successor weak-pseudoprime conjecture is equivalent to odd compositeness. -/

import Mathlib.Data.ZMod.Basic

namespace D5.S3.Arith.Congruence.OrdowskiImmediateSuccessorWeakPseudoprime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- At the immediate successor `n + 1`, the weak-pseudoprime congruence holds for a
composite modulus exactly when that modulus is odd. This does not assert that the
least qualifying composite above `n` exists for every `n`. -/
theorem result : ∀ n : ℕ, 1 ≤ n →
    ((1 < n + 1 ∧ ¬ Nat.Prime (n + 1) ∧ n ^ (n + 1) % (n + 1) = n % (n + 1)) ↔
      (¬ Nat.Prime (n + 1) ∧ Odd (n + 1) ∧ 1 < n + 1)) := by
  intro n _
  have hnneg : (n : ZMod (n + 1)) = -1 := by
    apply (add_eq_zero_iff_eq_neg).mp
    simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self' n
  constructor
  · rintro ⟨hgt, hnotprime, hmod⟩
    refine ⟨hnotprime, ?_, hgt⟩
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hpow : (n : ZMod (n + 1)) ^ (n + 1) = n := by
      rw [← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff' (n ^ (n + 1)) n (n + 1)).2 hmod
    rw [hnneg, heven.neg_one_pow] at hpow
    have hne_two : n + 1 ≠ 2 := by
      intro h
      apply hnotprime
      simpa only [h] using Nat.prime_two
    have htwo_lt : 2 < n + 1 := lt_of_le_of_ne hgt hne_two.symm
    let _ : Fact (2 < n + 1) := ⟨htwo_lt⟩
    exact ZMod.neg_one_ne_one hpow.symm
  · rintro ⟨hnotprime, hodd, hgt⟩
    refine ⟨hgt, hnotprime, ?_⟩
    apply (ZMod.natCast_eq_natCast_iff' (n ^ (n + 1)) n (n + 1)).1
    rw [Nat.cast_pow, hnneg, hodd.neg_one_pow]

#print axioms result

end D5.S3.Arith.Congruence.OrdowskiImmediateSuccessorWeakPseudoprime

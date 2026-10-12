/- GID: D5/S3/Arith/Robin/GoldenCell5040ResidualSupport
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/GoldenCell5040ResidualSupport
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Robin/GoldenCell5040ResidualSupport.robin_of_modEq_2241_residual_card_le_four
   digest: In the 5040 congruence cell, a residual with at most four prime factors cannot produce a Robin counterexample.
-/

import D5.S3.Arith.GoldenResource.GoldenCell5040Shape
import D5.S3.Arith.Robin.FewDistinctPrimes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.GoldenCell5040ResidualSupport

open D5.S3.Arith.Robin.FewDistinctPrimes

private theorem support_card_le_eight {a b r : Nat}
    (ha : 0 < a) (hb : 0 < b) (hr : r ≠ 0)
    (hcard : r.primeFactors.card ≤ 4) :
    (2 ^ a * 3 ^ b * 5 * 7 * r).primeFactors.card ≤ 8 := by
  have hsub : (2 ^ a * 3 ^ b * 5 * 7 * r).primeFactors ⊆
      ({2, 3, 5, 7} : Finset Nat) ∪ r.primeFactors := by
    rw [Nat.primeFactors_mul (by positivity) hr]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_mul (by positivity) (by norm_num)]
    rw [Nat.primeFactors_prime_pow ha.ne' Nat.prime_two]
    rw [Nat.primeFactors_prime_pow hb.ne' Nat.prime_three]
    rw [(by decide : Nat.Prime 5).primeFactors]
    rw [(by decide : Nat.Prime 7).primeFactors]
    simp
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le ({2, 3, 5, 7} : Finset Nat) r.primeFactors
  calc
    _ ≤ ({2, 3, 5, 7} : Finset Nat).card + r.primeFactors.card := hc.trans hu
    _ ≤ 8 := by simp; omega

/-- A 5040-cell shape with a four-prime residual has at most eight distinct primes. -/
theorem modEq_2241_card_le_eight_of_residual_card_le_four {n : Nat}
    (hshape : ∃ a b r : Nat, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧ r.primeFactors.card ≤ 4) :
    n.primeFactors.card ≤ 8 := by
  obtain ⟨a, b, r, hn, ha, _, hb, _, _, hcard⟩ := hshape
  subst n
  by_cases hr : r = 0
  · subst r
    norm_num
  · exact support_card_le_eight (by omega) (by omega) hr hcard

/-- The residual four-prime branch of the 5040 congruence cell satisfies Robin's inequality. -/
theorem robin_of_modEq_2241_residual_card_le_four {n : Nat}
    (hn : 5040 < n)
    (hshape : ∃ a b r : Nat, n = 2 ^ a * 3 ^ b * 5 * 7 * r ∧
      4 ≤ a ∧ a ≤ 6 ∧ 2 ≤ b ∧ b ≤ 3 ∧
      Nat.Coprime r (2 * 3 * 5 * 7 * 83) ∧ r.primeFactors.card ≤ 4) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  exact robin_of_card_primeFactors_le_eight hn
    (modEq_2241_card_le_eight_of_residual_card_le_four hshape)

theorem modEq_2241_shape_residual_branch {n : Nat}
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hcard : ∀ a b r : Nat, n = 2 ^ a * 3 ^ b * 5 * 7 * r →
      r.primeFactors.card ≤ 4) :
    n.primeFactors.card ≤ 8 := by
  obtain ⟨a, b, r, hn, ha, hahi, hb, hbhi, hcop⟩ :=
    D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_shape h5040 hmod
  exact modEq_2241_card_le_eight_of_residual_card_le_four
    ⟨a, b, r, hn, ha, hahi, hb, hbhi, hcop, hcard a b r hn⟩

/-- Applying the 5040 shape theorem isolates the four-prime residual branch. -/
theorem robin_of_modEq_2241_and_residual_card_le_four {n : Nat}
    (hn : 5040 < n) (h5040 : 5040 ∣ n)
    (hmod : Nat.ModEq n (3 ^ n) 2241)
    (hcard : ∀ a b r : Nat, n = 2 ^ a * 3 ^ b * 5 * 7 * r →
      r.primeFactors.card ≤ 4) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
  obtain ⟨a, b, r, hshape, ha, hahi, hb, hbhi, hcop⟩ :=
    D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_shape h5040 hmod
  exact robin_of_modEq_2241_residual_card_le_four hn
    ⟨a, b, r, hshape, ha, hahi, hb, hbhi, hcop, hcard a b r hshape⟩

#print axioms modEq_2241_card_le_eight_of_residual_card_le_four
#print axioms robin_of_modEq_2241_residual_card_le_four
#print axioms robin_of_modEq_2241_and_residual_card_le_four

end D5.S3.Arith.Robin.GoldenCell5040ResidualSupport

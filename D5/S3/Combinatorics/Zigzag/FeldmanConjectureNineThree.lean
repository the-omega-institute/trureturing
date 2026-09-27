/- GID: D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Basic]
   utility: none
   digest: Literal balance-only proof of Feldman Conjecture 9.3. -/

import D5.S3.Combinatorics.Zigzag.EvenPaths
import D5.S3.Combinatorics.Zigzag.OddPaths
import D5.S3.Combinatorics.Zigzag.LaurentCoefficients
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Zigzag

/-- Exact literal balanced-choice count at every positive even parameter. -/
theorem balancedCount_even_closed (r : Nat) (hr : 1 ≤ r) :
    balancedCount (2 * r) =
      4 * 6 ^ (r - 1) * Nat.choose (2 * r - 2) (r - 1) := by
  classical
  rw [show balancedCount (2 * r) =
      Fintype.card {c : Choices (2 * r) // Balanced c} by
    rw [balancedCount, Fintype.card_subtype]]
  have he := Fintype.card_congr (evenBalancedChoicesEquiv r hr)
  rw [he, Fintype.card_sum]
  have href := Fintype.card_congr (evenZeroChargeReflection (3 * r - 3))
  rw [← href, evenPath_zero_charge_card]
  rw [show 3 * r - 3 = 3 * (r - 1) by omega,
    pathPolynomial_coeff_three_mul]
  rw [show 2 * (r - 1) = 2 * r - 2 by omega]
  ring

/-- Exact literal balanced-choice count at every positive odd parameter. -/
theorem balancedCount_odd_closed (r : Nat) (hr : 1 ≤ r) :
    balancedCount (2 * r + 1) =
      2 * 6 ^ r * Nat.choose (2 * r - 1) r := by
  classical
  rw [show balancedCount (2 * r + 1) =
      Fintype.card {c : Choices (2 * r + 1) // Balanced c} by
    rw [balancedCount, Fintype.card_subtype]]
  have he := Fintype.card_congr (oddBalancedChoicesEquiv r hr)
  rw [he, Fintype.card_sum]
  have href := Fintype.card_congr (oddZeroChargeReflection (3 * r - 1))
  rw [← href, oddPath_zero_charge_card]
  rw [show 3 * r - 1 = 3 * (r - 1) + 2 by omega,
    pathPolynomial_coeff_three_mul_add_two]
  rw [show r - 1 + 1 = r by omega,
    show 2 * (r - 1) + 1 = 2 * r - 1 by omega]
  ring

/-- All three clauses of Conjecture 9.3 for the literal balance-only count. -/
theorem feldman_conjecture_nine_three :
    balancedCount 2 = 4 ∧
      (∀ r, 2 ≤ r -> balancedCount (2 * r) = 4 * balancedCount (2 * r - 1)) ∧
      (∀ r, 1 ≤ r -> (2 * r) * balancedCount (2 * r + 1) =
        6 * (2 * r - 1) * balancedCount (2 * r)) := by
  constructor
  · simpa using balancedCount_even_closed 1 (by omega)
  constructor
  · intro r hr
    rw [balancedCount_even_closed r (by omega)]
    rw [show 2 * r - 1 = 2 * (r - 1) + 1 by omega,
      balancedCount_odd_closed (r - 1) (by omega)]
    rw [show 2 * r - 2 = 2 * (r - 1) by omega]
    have hcentral :
        Nat.choose (2 * (r - 1)) (r - 1) =
          2 * Nat.choose (2 * (r - 1) - 1) (r - 1) := by
      have hpascal := Nat.choose_succ_succ' (2 * (r - 1) - 1) (r - 1 - 1)
      rw [show 2 * (r - 1) - 1 + 1 = 2 * (r - 1) by omega,
        show r - 1 - 1 + 1 = r - 1 by omega] at hpascal
      have hsym := Nat.choose_symm_half (r - 1 - 1)
      rw [show 2 * (r - 1 - 1) + 1 = 2 * (r - 1) - 1 by omega,
        show r - 1 - 1 + 1 = r - 1 by omega] at hsym
      rw [hpascal, hsym]
      ring
    rw [hcentral]
    ring
  · intro r hr
    rw [balancedCount_odd_closed r hr, balancedCount_even_closed r hr]
    rw [show 6 ^ r = 6 ^ (r - 1) * 6 by
      rw [← pow_succ]; congr 1; omega]
    have hc : (2 * r - 1) * Nat.choose (2 * r - 2) (r - 1) =
        Nat.choose (2 * r - 1) r * r := by
      have hc' := Nat.add_one_mul_choose_eq (2 * r - 2) (r - 1)
      rw [show 2 * r - 2 + 1 = 2 * r - 1 by omega,
        show r - 1 + 1 = r by omega] at hc'
      exact hc'
    calc
      (2 * r) * (2 * (6 ^ (r - 1) * 6) * Nat.choose (2 * r - 1) r) =
          24 * 6 ^ (r - 1) * (Nat.choose (2 * r - 1) r * r) := by ring
      _ = 24 * 6 ^ (r - 1) *
          ((2 * r - 1) * Nat.choose (2 * r - 2) (r - 1)) := by rw [hc]
      _ = 6 * (2 * r - 1) *
          (4 * 6 ^ (r - 1) * Nat.choose (2 * r - 2) (r - 1)) := by ring

end D5.S3.Combinatorics.Zigzag

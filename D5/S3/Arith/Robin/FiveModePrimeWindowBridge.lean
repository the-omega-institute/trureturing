/- GID: D5/S3/Arith/Robin/FiveModePrimeWindowBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/FiveModePrimeWindowBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Arith/GoldenResource/GoldenCell5040Shape,
     D5/S1/Words/AdmissibleWords/FiveModeMixedCoordinates]
   utility: none
   digest: A normalized five-prime exponent window lands in the five-mode chart at the 5040 congruence boundary. -/

import D5.S3.Arith.GoldenResource.GoldenCell5040Shape
import D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.FiveModePrimeWindowBridge

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

noncomputable section

/-- The five prime labels used by the five-mode chart: the 5040 support and its
    congruence-excluded prime. -/
def modePrimes : Fin 5 → ℕ := ![2, 3, 5, 7, 83]

/-- The total mass used to normalize the five prime-exponent coordinates. -/
def windowDenom (n : ℕ) : ℝ :=
  ∑ i : Fin 5, ((n.factorization (modePrimes i) : ℝ) + 1)

/-- A positive probability vector obtained from the five selected prime exponents. -/
def primeWindow (n : ℕ) : Fin 5 → ℝ :=
  fun i => ((n.factorization (modePrimes i) : ℝ) + 1) / windowDenom n

/-- The 5040 congruence forces the selected five-prime window into the five-mode
    simplex.  Its visible occupancies therefore lie in the open pyramid chart. -/
theorem modEq_prime_window_bridge {n : ℕ}
    (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241) :
    primeWindow n ∈ openSimplex ∧
      visible (primeWindow n) ∈ openPyramid ∧
      4 ≤ n.factorization 2 ∧ n.factorization 2 ≤ 6 ∧
      2 ≤ n.factorization 3 ∧ n.factorization 3 ≤ 3 ∧
      visible (primeWindow n) =
        (((n.factorization 3 : ℝ) + 2) / windowDenom n,
          (3 / windowDenom n, 2 / windowDenom n)) ∧
      windowDenom n =
        ((n.factorization 2 : ℝ) + 1) +
          ((n.factorization 3 : ℝ) + 1) + 2 + 2 + 1 := by
  obtain ⟨hn, h2lo, h2hi, h3lo, h3hi, h5, h7, h83⟩ :=
    D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_factorization
      h5040 hmod
  have hden : 0 < windowDenom n := by
    unfold windowDenom
    rw [Fin.sum_univ_five]
    simp [modePrimes]
    positivity
  have hshape : windowDenom n =
      ((n.factorization 2 : ℝ) + 1) +
        ((n.factorization 3 : ℝ) + 1) + 2 + 2 + 1 := by
    have hm0 : modePrimes (0 : Fin 5) = 2 := by decide
    have hm1 : modePrimes (1 : Fin 5) = 3 := by decide
    have hm2 : modePrimes (2 : Fin 5) = 5 := by decide
    have hm3 : modePrimes (3 : Fin 5) = 7 := by decide
    have hm4 : modePrimes (4 : Fin 5) = 83 := by decide
    unfold windowDenom
    rw [Fin.sum_univ_five]
    rw [hm0, hm1, hm2, hm3, hm4, h5, h7, h83]
    norm_num
  have hsimplex : primeWindow n ∈ openSimplex := by
    refine ⟨?_, ?_⟩
    · intro i
      exact div_pos (by positivity) hden
    · unfold primeWindow
      rw [← Finset.sum_div Finset.univ
        (fun i : Fin 5 => (n.factorization (modePrimes i) : ℝ) + 1)
        (windowDenom n)]
      exact div_self hden.ne'
  have hvisible : visible (primeWindow n) =
      (((n.factorization 3 : ℝ) + 2) / windowDenom n,
        (3 / windowDenom n, 2 / windowDenom n)) := by
    change
      (((n.factorization 3 : ℝ) + 1) / windowDenom n +
          ((n.factorization 83 : ℝ) + 1) / windowDenom n,
        (((n.factorization 7 : ℝ) + 1) / windowDenom n +
          ((n.factorization 83 : ℝ) + 1) / windowDenom n,
          ((n.factorization 5 : ℝ) + 1) / windowDenom n)) = _
    rw [h5, h7, h83]
    norm_num [div_eq_mul_inv]
    constructor <;> ring
  refine ⟨hsimplex, mixed_coordinates_global_chart.1 _ hsimplex,
    h2lo, h2hi, h3lo, h3hi, hvisible, hshape⟩

#print axioms modEq_prime_window_bridge

end

end D5.S3.Arith.Robin.FiveModePrimeWindowBridge

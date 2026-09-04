/- GID: D5/S3/PrimeForms/PrimaryPseudoperfectPorts
   generality: G
   mirror-B: D5/B/S3/PrimeForms/PrimaryPseudoperfectPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Primary pseudoperfect numbers admit an exact reciprocal-sum characterization. -/

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches for `IsPPN`, `squarefreeDeriv`, primary pseudoperfect numbers,
     Egyptian-fraction characterizations, and the corresponding prime-factor sums found no
     existing D5 declaration.
   * Pinned Mathlib has no primary-pseudoperfect predicate or reciprocal-sum theorem. Its exact
     supporting lemmas `Nat.cast_div`, `Nat.dvd_of_mem_primeFactors`, and
     `Nat.prime_of_mem_primeFactors` are used below instead of reproving cast or divisor facts.
   * The nonzero hypothesis on the reciprocal theorem excludes Lean's totalized `1 / 0 = 0`.
-/

namespace D5.S3.PrimeForms.PrimaryPseudoperfectPorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The sum of `n / p` over the distinct prime divisors of `n`. -/
def squarefreeDeriv (n : Nat) : Nat :=
  ∑ p ∈ n.primeFactors, n / p

/-- A primary pseudoperfect number is a nontrivial squarefree natural whose prime-factor
quotients sum to one less than the number. -/
def IsPPN (n : Nat) : Prop :=
  Squarefree n ∧ 1 < n ∧ n = 1 + squarefreeDeriv n

/-- Casting the quotient sum to the rationals turns it into `n` times the reciprocal-prime sum.
This is the arithmetic bridge used by both directions of the characterization. -/
theorem squarefreeDeriv_cast (n : Nat) :
    (squarefreeDeriv n : Rat) =
      (n : Rat) * ∑ p ∈ n.primeFactors, 1 / (p : Rat) := by
  classical
  rw [squarefreeDeriv, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp)]
  · ring
  · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- For a nonzero natural, the Egyptian-fraction identity is equivalent to the integral
quotient-sum identity. -/
theorem reciprocal_sum_eq_one_iff (n : Nat) (hn : n ≠ 0) :
    1 / (n : Rat) + ∑ p ∈ n.primeFactors, 1 / (p : Rat) = 1 ↔
      n = 1 + squarefreeDeriv n := by
  let reciprocalSum : Rat := ∑ p ∈ n.primeFactors, 1 / (p : Rat)
  have hnRat : (n : Rat) ≠ 0 := by exact_mod_cast hn
  have hcast : (squarefreeDeriv n : Rat) = (n : Rat) * reciprocalSum := by
    simpa [reciprocalSum] using squarefreeDeriv_cast n
  change 1 / (n : Rat) + reciprocalSum = 1 ↔ n = 1 + squarefreeDeriv n
  constructor
  · intro hreciprocal
    have hRat : (n : Rat) = 1 + (squarefreeDeriv n : Rat) := by
      calc
        (n : Rat) = (n : Rat) * 1 := by ring
        _ = (n : Rat) * (1 / (n : Rat) + reciprocalSum) := by rw [hreciprocal]
        _ = 1 + (n : Rat) * reciprocalSum := by field_simp [hnRat]
        _ = 1 + (squarefreeDeriv n : Rat) := by rw [← hcast]
    exact_mod_cast hRat
  · intro hintegral
    have hRat : (n : Rat) = 1 + (squarefreeDeriv n : Rat) := by
      exact_mod_cast hintegral
    calc
      1 / (n : Rat) + reciprocalSum =
          (1 + (n : Rat) * reciprocalSum) / (n : Rat) := by
            field_simp [hnRat]
      _ = (n : Rat) / (n : Rat) := by rw [← hcast, ← hRat]
      _ = 1 := div_self hnRat

/-- Primary pseudoperfectness is exactly squarefreeness, nontriviality, and the reciprocal-sum
identity over the distinct prime factors. -/
theorem isPPN_iff_reciprocal_sum (n : Nat) :
    IsPPN n ↔
      Squarefree n ∧ 1 < n ∧
        1 / (n : Rat) + ∑ p ∈ n.primeFactors, 1 / (p : Rat) = 1 := by
  constructor
  · rintro ⟨hsquarefree, hn, hderiv⟩
    exact ⟨hsquarefree, hn, (reciprocal_sum_eq_one_iff n (by omega)).2 hderiv⟩
  · rintro ⟨hsquarefree, hn, hreciprocal⟩
    exact ⟨hsquarefree, hn, (reciprocal_sum_eq_one_iff n (by omega)).1 hreciprocal⟩

#print axioms squarefreeDeriv_cast
#print axioms reciprocal_sum_eq_one_iff
#print axioms isPPN_iff_reciprocal_sum

end D5.S3.PrimeForms.PrimaryPseudoperfectPorts

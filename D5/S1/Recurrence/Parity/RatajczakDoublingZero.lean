/- GID: D5/S1/Recurrence/Parity/RatajczakDoublingZero
   generality: G
   mirror-B: D5/B/S1/Recurrence/Parity/RatajczakDoublingZero
   mirror-E: none(waiver:symbolic-arithmetic-no-numerical-evidence)
   anchors: []
   utility: none
   digest: The running-sum residue recurrence vanishes exactly when the modulus is a power of two. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
Fix a modulus and a start value coprime to it, and read the residue of the
running sum: the next term is the start value plus every earlier term, taken
modulo the modulus. The recurrence looks like it accumulates history, but it
does not. Adding the previous residue back to the previous partial sum doubles
that residue, so the term at each stage is the start value scaled by a power
of two.

Once that is available the vanishing question becomes a divisibility question
about a power of two times a coprime number, and coprimality moves the whole
burden onto the modulus.

The start value is not required to exceed the modulus; the source's range
restriction is needed for neither direction.
-/

namespace D5.S1.Recurrence.Parity.RatajczakDoublingZero

/-- The running-sum residue sequence: each term is the start value plus every
earlier term, reduced modulo `j`. -/
def IsRunningSumResidue (i j : ℕ) (b : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, b (n + 1) = (i + ∑ k ∈ Finset.range n, b (k + 1)) % j

/-- The escape content: the accumulated recurrence is a doubling in disguise.
Each term is the start value scaled by a power of two, reduced modulo `j`.
The step reduces the partial sum before adding the residue back, which turns
the sum of a partial sum and its own residue into twice that residue. -/
theorem residue_eq_two_pow_mul (i j : ℕ) (b : ℕ → ℕ)
    (hb : IsRunningSumResidue i j b) (n : ℕ) :
    b (n + 1) = 2 ^ n * i % j := by
  induction n with
  | zero => simpa [IsRunningSumResidue] using hb 0
  | succ n ih =>
      have hsum : i + ∑ k ∈ Finset.range (n + 1), b (k + 1)
          = (i + ∑ k ∈ Finset.range n, b (k + 1)) + b (n + 1) := by
        rw [Finset.sum_range_succ, Nat.add_assoc]
      have hstep : b (n + 2)
          = ((i + ∑ k ∈ Finset.range n, b (k + 1)) + b (n + 1)) % j := by
        rw [hb (n + 1), hsum]
      have hfold : ((i + ∑ k ∈ Finset.range n, b (k + 1)) + b (n + 1)) % j
          = (b (n + 1) + b (n + 1)) % j := by
        rw [hb n]
        simp [Nat.add_mod]
      have hdouble : (b (n + 1) + b (n + 1)) % j = 2 ^ (n + 1) * i % j := by
        rw [ih, ← Nat.add_mod]
        have : 2 ^ n * i + 2 ^ n * i = 2 ^ (n + 1) * i := by ring
        rw [this]
      rw [hstep, hfold, hdouble]

/-- The vanishing criterion. Some term is zero exactly when the modulus is a
power of two. Coprimality is what forces the modulus itself to absorb the
whole power of two; without it the start value could supply the factors. -/
theorem exists_zero_iff_modulus_pow_two (i j : ℕ)
    (hcop : Nat.Coprime i j) (b : ℕ → ℕ) (hb : IsRunningSumResidue i j b) :
    (∃ t : ℕ, b (t + 1) = 0) ↔ ∃ m : ℕ, j = 2 ^ m := by
  constructor
  · rintro ⟨t, ht⟩
    rw [residue_eq_two_pow_mul i j b hb t] at ht
    have hdvd : j ∣ 2 ^ t * i := Nat.dvd_of_mod_eq_zero ht
    have hji : Nat.Coprime j i := hcop.symm
    have hpow : j ∣ 2 ^ t := hji.dvd_of_dvd_mul_right hdvd
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
    exact ⟨m, hm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [residue_eq_two_pow_mul i (2 ^ m) b hb m]
    exact Nat.mul_mod_right _ _

#print axioms residue_eq_two_pow_mul
#print axioms exists_zero_iff_modulus_pow_two

end D5.S1.Recurrence.Parity.RatajczakDoublingZero

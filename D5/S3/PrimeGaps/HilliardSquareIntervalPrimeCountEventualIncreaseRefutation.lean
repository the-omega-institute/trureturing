/- GID: D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation
   mirror-E: none(waiver:symbolic-refutation-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Order.Interval.Finset.Nat]
   utility: none
   digest: Odd-prime counting refutes eventual increase in Hilliard square intervals. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace D5.S3.PrimeGaps.HilliardSquareIntervalPrimeCountEventualIncreaseRefutation

/-- The number of primes in the half-open square interval `(n^2, n^2 + n]`,
as in OEIS A089610. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioc (n * n) (n * n + n)).filter Nat.Prime).card

/-- Hilliard's conjecture that the interval counts eventually increase at
every successive index. -/
def claim : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a n < a (n + 1)

/-- The eventual strict-increase conjecture in OEIS A089610 is false. The
refutation does not address positivity of these interval counts. -/
theorem result : ¬ claim := by
  have even_index_bound (k : ℕ) : a (2 * k) ≤ k := by
    by_cases hk : k = 0
    · subst k
      simp [a]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have htwo_k : 2 ≤ 2 * k := by omega
    have hbase : 4 ≤ (2 * k) * (2 * k) := by
      simpa only [Nat.reduceMul] using Nat.mul_le_mul htwo_k htwo_k
    change
      ((Finset.Ioc ((2 * k) * (2 * k)) ((2 * k) * (2 * k) + 2 * k)).filter
        Nat.Prime).card ≤ k
    calc
      ((Finset.Ioc ((2 * k) * (2 * k)) ((2 * k) * (2 * k) + 2 * k)).filter
          Nat.Prime).card ≤
          (Finset.Ico (((2 * k) * (2 * k)) / 2)
            (((2 * k) * (2 * k)) / 2 + k)).card := by
        apply Finset.card_le_card_of_injOn
          (fun p : ℕ ↦ p / 2)
        · intro p hp
          change p ∈ (Finset.Ioc ((2 * k) * (2 * k))
            ((2 * k) * (2 * k) + 2 * k)).filter Nat.Prime at hp
          change p / 2 ∈ Finset.Ico (((2 * k) * (2 * k)) / 2)
            (((2 * k) * (2 * k)) / 2 + k)
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
          rw [Finset.mem_Ico]
          have hp_ne_two : p ≠ 2 := by omega
          have hp_odd : p % 2 = 1 := hp.2.eq_two_or_odd.resolve_left hp_ne_two
          have hp_decomp := Nat.mod_add_div p 2
          have hbase_decomp := Nat.mod_add_div ((2 * k) * (2 * k)) 2
          have hbase_even : ((2 * k) * (2 * k)) % 2 = 0 := by
            apply Nat.dvd_iff_mod_eq_zero.mp
            exact ⟨k * (2 * k), by simp only [Nat.mul_assoc]⟩
          omega
        · intro p hp q hq hpq
          change p / 2 = q / 2 at hpq
          change p ∈ (Finset.Ioc ((2 * k) * (2 * k))
            ((2 * k) * (2 * k) + 2 * k)).filter Nat.Prime at hp
          change q ∈ (Finset.Ioc ((2 * k) * (2 * k))
            ((2 * k) * (2 * k) + 2 * k)).filter Nat.Prime at hq
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hp hq
          have hp_ne_two : p ≠ 2 := by omega
          have hq_ne_two : q ≠ 2 := by omega
          have hp_odd : p % 2 = 1 := hp.2.eq_two_or_odd.resolve_left hp_ne_two
          have hq_odd : q % 2 = 1 := hq.2.eq_two_or_odd.resolve_left hq_ne_two
          have hp_decomp := Nat.mod_add_div p 2
          have hq_decomp := Nat.mod_add_div q 2
          omega
      _ = k := by simp
  rintro ⟨N, hstrict⟩
  let shifted : ℕ → ℕ := fun t ↦ a (N + t)
  have shifted_strict : StrictMono shifted := by
    apply strictMono_nat_of_lt_succ
    intro t
    dsimp only [shifted]
    simpa only [Nat.add_assoc] using hstrict (N + t) (by omega)
  have hgrowth := shifted_strict.add_le_nat (N + 2) 0
  simp only [shifted, Nat.add_zero] at hgrowth
  have hindex : N + (N + 2) = 2 * (N + 1) := by omega
  rw [hindex] at hgrowth
  have hupper := even_index_bound (N + 1)
  omega

#print axioms result

end D5.S3.PrimeGaps.HilliardSquareIntervalPrimeCountEventualIncreaseRefutation

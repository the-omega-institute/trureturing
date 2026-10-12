/- GID: D5/S3/Arith/Primes/FibonacciRankParentHeight
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRankParentHeight
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every prime reaches 2, 3 or 5 via Fibonacci-rank parents in at most log2(p-1) steps. -/

import D5.S3.Arith.Primes.FiniteFibonacciRankClosure

/-! A rank-parent edge leads from a prime `p > 5` to a prime factor of its Fibonacci entry rank
`z(p)`. The rank divides the even number `p - (5 / p)`, so each parent `q` satisfies
`2q ≤ p + 1`. Following parents therefore reaches one of the roots `2, 3, 5`, and every path
from `p` has at most `log₂ (p - 1)` edges. -/

namespace D5.S3.Arith.Primes.FibonacciRankParentHeight

open D5.S3.Arith.FibonacciRank
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure

/-- `RankDescent p r k`: `k` rank-parent edges lead from the prime `p` to the prime `r`. Each edge
leaves a prime above `5` and enters a prime factor of its Fibonacci entry rank. -/
inductive RankDescent : ℕ → ℕ → ℕ → Prop
  | refl {p : ℕ} (hp : p.Prime) : RankDescent p p 0
  | step {p q r k : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hq : q.Prime)
      (hqp : q ∣ fibonacciRank p) (h : RankDescent q r k) : RankDescent p r (k + 1)

private theorem rank_spec {p : ℕ} (hp : p.Prime) :
    0 < fibonacciRank p ∧ p ∣ Nat.fib (fibonacciRank p) ∧
      ∀ n, 0 < n → p ∣ Nat.fib n → fibonacciRank p ≤ n := by
  unfold fibonacciRank
  rw [dif_pos hp]
  exact (rankWitness p hp).2

/-- A rank parent of a prime `p > 5` is at most `(p + 1) / 2`: the rank divides `p - 1` or
`p + 1`, both even, and an odd prime factor of an even number is at most half of it. -/
theorem two_mul_le_of_dvd_fibonacciRank {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hq : q.Prime) (hqp : q ∣ fibonacciRank p) : 2 * q ≤ p + 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hpos, hzero, hmin⟩ := rank_spec hp
  have hdvd := fibonacci_rank_dvd_prime_bound hp (by omega) hpos hzero hmin
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqm : q ∣ if legendreSym 5 p = 1 then p - 1 else p + 1 := hqp.trans hdvd
  have hm : ∃ m, (m = p - 1 ∨ m = p + 1) ∧ q ∣ m := by
    by_cases h : legendreSym 5 p = 1
    · exact ⟨p - 1, Or.inl rfl, by simpa [h] using hqm⟩
    · exact ⟨p + 1, Or.inr rfl, by simpa [h] using hqm⟩
  obtain ⟨m, hmval, hqm'⟩ := hm
  have h2m : 2 ∣ m := by rcases hmval with rfl | rfl <;> omega
  have hmpos : 0 < m := by rcases hmval with rfl | rfl <;> omega
  have hmle : m ≤ p + 1 := by rcases hmval with rfl | rfl <;> omega
  rcases hq.eq_two_or_odd' with rfl | hqodd
  · omega
  · have hcop : Nat.Coprime 2 q := Nat.coprime_two_left.mpr hqodd
    have h2q : 2 * q ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h2m hqm'
    exact (Nat.le_of_dvd hmpos h2q).trans hmle

/-- Every prime descends through Fibonacci-rank parents to a prime at most `5`, that is to `2`,
`3` or `5`; and every descent from `p`, along any choice of parents, has at most
`log₂ (p - 1)` edges. -/
theorem rankDescent_to_root_and_height {p : ℕ} (hp : p.Prime) :
    (∃ r k, r ≤ 5 ∧ RankDescent p r k) ∧
      ∀ r k, RankDescent p r k → 2 ^ k ≤ p - 1 := by
  refine ⟨?_, fun r k h => ?_⟩
  · revert hp
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      intro hp
      by_cases hp5 : p ≤ 5
      · exact ⟨p, 0, hp5, RankDescent.refl hp⟩
      · replace hp5 : 5 < p := Nat.lt_of_not_le hp5
        obtain ⟨_, hzero, _⟩ := rank_spec hp
        have hz1 : fibonacciRank p ≠ 1 := by
          intro h1
          rw [h1, Nat.fib_one, Nat.dvd_one] at hzero
          exact hp.one_lt.ne' hzero
        have hq : (fibonacciRank p).minFac.Prime := Nat.minFac_prime hz1
        have hqp : (fibonacciRank p).minFac ∣ fibonacciRank p := Nat.minFac_dvd _
        have hle := two_mul_le_of_dvd_fibonacciRank hp hp5 hq hqp
        obtain ⟨r, k, hr, hd⟩ := ih _ (by omega) hq
        exact ⟨r, k + 1, hr, RankDescent.step hp hp5 hq hqp hd⟩
  · clear hp
    induction h with
    | @refl p hp' =>
      have := hp'.two_le
      simp only [pow_zero]
      omega
    | @step p q r k hp' hp5 hq hqp _ ih =>
      have hle := two_mul_le_of_dvd_fibonacciRank hp' hp5 hq hqp
      have hq2 := hq.two_le
      rw [pow_succ]
      generalize 2 ^ k = t at ih ⊢
      omega

end D5.S3.Arith.Primes.FibonacciRankParentHeight

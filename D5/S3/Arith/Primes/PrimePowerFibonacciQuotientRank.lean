/- GID: D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/PrimePowerFibonacciQuotientRank
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime-power Fibonacci quotients contain only first-entry prime factors. -/

import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

namespace D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private theorem prime_not_dvd_fib_prime_pow (p k : ℕ) (hp : p.Prime)
    (hpFive : 5 < p) : ¬ p ∣ Nat.fib (p ^ k) := by
  let r := rankWitness p hp
  have hrpos : 0 < r.val := r.property.1
  have hrzero : p ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ n, 0 < n → p ∣ Nat.fib n → r.val ≤ n := r.property.2.2
  have hrne : r.val ≠ 1 := by
    intro heq
    have h : p ∣ 1 := by simpa [heq] using hrzero
    exact hp.ne_one (Nat.dvd_one.mp h)
  have hrbound := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
    hp (by omega : p ≠ 5) hrpos hrzero hrmin
  have hpNotRank : ¬ p ∣ r.val := by
    intro hpr
    by_cases heps : legendreSym 5 p = 1
    · have hbad : p ∣ p - 1 := hpr.trans (by simpa [heps] using hrbound)
      have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hbad
      omega
    · have hbad : p ∣ p + 1 := hpr.trans (by simpa [heps] using hrbound)
      have hone : p ∣ 1 := (Nat.dvd_add_self_left).mp hbad
      exact hp.ne_one (Nat.dvd_one.mp hone)
  intro hpFib
  have hrdiv : r.val ∣ p ^ k :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      hrpos hrzero hrmin).mp hpFib
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hp).mp hrdiv
  cases j with
  | zero => exact hrne (by simpa using hj)
  | succ j =>
      apply hpNotRank
      rw [hj]
      exact dvd_pow_self p (by omega)

/-- Every prime factor of the quotient between consecutive prime-power
Fibonacci indices first appears at the larger index. -/
theorem prime_power_fibonacci_quotient_rank (p k : ℕ) (hp : p.Prime)
    (hpFive : 5 < p) :
    let R := Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)
    1 < R ∧
      ∀ q : ℕ, q.Prime → q ∣ R → fibonacciRank q = p ^ (k + 1) := by
  dsimp only
  let M := p ^ k
  let N := p ^ (k + 1)
  let FM := Nat.fib M
  let FN := Nat.fib N
  let R := FN / FM
  have hMpos : 0 < M := pow_pos hp.pos k
  have hNpow : N = M * p := by simp [N, M, pow_succ]
  have hMltN : M < N := by rw [hNpow]; nlinarith
  have hNge : 5 ≤ N := by rw [hNpow]; nlinarith
  have hFMpos : 0 < FM := Nat.fib_pos.mpr hMpos
  have hFNpos : 0 < FN := Nat.fib_pos.mpr (by omega)
  have hFMltFN : FM < FN := by
    by_cases hM2 : 2 ≤ M
    · exact (Nat.fib_lt_fib hM2).2 hMltN
    · have hMone : M = 1 := by omega
      have hFNfive : 5 ≤ FN := by
        calc
          5 = Nat.fib 5 := by decide
          _ ≤ Nat.fib N := Nat.fib_mono hNge
      have hFMone : FM = 1 := by simp [FM, hMone]
      omega
  have hMdvdN : M ∣ N := by
    dsimp [M, N]
    exact pow_dvd_pow p (by omega)
  have hFMdvdFN : FM ∣ FN := Nat.fib_dvd M N hMdvdN
  have hMul : FM * R = FN := Nat.mul_div_cancel' hFMdvdFN
  have hRpos : 0 < R := Nat.div_pos (Nat.le_of_dvd hFNpos hFMdvdFN) hFMpos
  have hRgt : 1 < R := by
    by_contra hnot
    have hRone : R = 1 := by omega
    rw [hRone, mul_one] at hMul
    omega
  refine ⟨hRgt, ?_⟩
  intro q hq hqR
  have hqFN : q ∣ FN := by
    rw [← hMul]
    exact dvd_mul_of_dvd_right hqR FM
  have hqNotP : q ≠ p := by
    intro heq
    subst q
    exact prime_not_dvd_fib_prime_pow p (k + 1) hp hpFive hqFN
  have hqNotPow (j : ℕ) : ¬ q ∣ p ^ j := by
    intro hqpow
    have hqp : q ∣ p := hq.dvd_of_dvd_pow hqpow
    exact hqNotP ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp)
  let r := rankWitness q hq
  have hrpos : 0 < r.val := r.property.1
  have hrzero : q ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ n, 0 < n → q ∣ Nat.fib n → r.val ≤ n := r.property.2.2
  have hrdiv : r.val ∣ N :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      hrpos hrzero hrmin).mp hqFN
  obtain ⟨j, hjle, hjrank⟩ := (Nat.dvd_prime_pow hp).mp hrdiv
  have hj : j = k + 1 := by
    by_contra hneq
    have hjk : j ≤ k := by omega
    have hrdivM : r.val ∣ M := by
      rw [hjrank]
      exact pow_dvd_pow p hjk
    have hqFM : q ∣ FM :=
      (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        hrpos hrzero hrmin).mpr hrdivM
    have hqFact : Fact q.Prime := ⟨hq⟩
    letI : Fact q.Prime := hqFact
    have hvalN := fibonacci_original_rank_valuation q N hq hqFN (by
      simpa [N] using hqNotPow (k + 1))
    have hvalM := fibonacci_original_rank_valuation q M hq hqFM (by
      simpa [M] using hqNotPow k)
    have hvalSame : padicValNat q FN = padicValNat q FM := by
      exact hvalN.trans hvalM.symm
    have hvalR : 0 < padicValNat q R :=
      one_le_padicValNat_of_dvd (by omega) hqR
    have hvalMul : padicValNat q FN =
        padicValNat q FM + padicValNat q R := by
      rw [← hMul]
      exact padicValNat.mul (by omega : FM ≠ 0) (by omega : R ≠ 0)
    rw [hvalSame] at hvalMul
    omega
  have hrN : r.val = N := by rw [hjrank, hj]
  simpa only [fibonacciRank, hq, dite_true, N] using hrN

#print axioms prime_power_fibonacci_quotient_rank

end D5.S3.Arith.Primes.PrimePowerFibonacciQuotientRank

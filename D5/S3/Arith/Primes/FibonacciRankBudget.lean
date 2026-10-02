/- GID: D5/S3/Arith/Primes/FibonacciRankBudget
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciRankBudget
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd Fibonacci valuation support in a finite rank-closed set bounds the entire index. -/

import D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
import D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
import D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
import D5.S3.Arith.Primes.FibonacciDyadicRankBudget
import D5.S3.Arith.Primes.FibonacciTernaryRankBudget
import D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
import D5.S3.Arith.Primes.OriginalOddDepthSupport

namespace D5.S3.Arith.Primes.FibonacciRankBudget

open D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
open D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
open D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Primes.FibonacciDyadicRankBudget
open D5.S3.Arith.Primes.FibonacciTernaryRankBudget
open D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
open D5.S3.Arith.Primes.OriginalOddDepthSupport

set_option maxHeartbeats 1800000 in
/-- Odd valuation support in a finite rank-closed prime set bounds every
prime depth of the index, allowing one additional factor of five. -/
theorem fibonacci_rank_budget (H : Finset ℕ) (n : ℕ) (hH : ∀ p ∈ H, p.Prime)
    (hTwo : 2 ∈ H) (hThree : 3 ∈ H) (hFive : 5 ∈ H)
    (hClosed : rankClosureStep H = H) (hn : 0 < n)
    (hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H) :
    n ∣ 5 * H.lcm fibonacciRank ∧
      (∀ q : ℕ, q.Prime → q ≠ 5 →
        padicValNat q n ≤ padicValNat q (H.lcm fibonacciRank)) ∧
      padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hOddFactor (a : ℕ) (ha : 0 < a) (hns : ¬ IsSquare a) :
      ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ Odd (padicValNat p a) := by
    by_contra hNone
    have hEven (p : ℕ) (hp : p ∈ a.primeFactors) :
        Even (a.factorization p) := by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDiv := Nat.dvd_of_mem_primeFactors hp
      have hpNotOdd : ¬ Odd (padicValNat p a) := by
        intro hpOdd
        exact hNone ⟨p, hpPrime, hpDiv, hpOdd⟩
      rw [Nat.factorization_def a hpPrime]
      exact Nat.not_odd_iff_even.mp hpNotOdd
    let s := ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
    have hSquare : a = s ^ 2 := by
      rw [Nat.prod_primeFactors_pow_factorization ha.ne']
      dsimp only [s]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      obtain ⟨j, hj⟩ := hEven p hp
      omega
    apply hns
    exact ⟨s, by simpa [pow_two] using hSquare⟩
  have hLayers (q k : ℕ) (hq : q.Prime) (hge : 7 ≤ q) :
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) := by
    by_cases hsmall : k = 0
    · subst k
      simp only [zero_add, pow_one, pow_zero, Nat.fib_one, Nat.div_one]
      exact ⟨Nat.fib_pos.mpr (by omega),
        fibonacci_odd_index_nonsquare q (by omega) (hq.odd_iff.mpr (by omega))⟩
    by_cases h31 : q % 120 = 49 ∨ q % 120 = 71
    · have h := fibonacci_prime_power_mod31_nonsquare q k hq hge h31
      exact ⟨h.1, h.2.2⟩
    by_cases hremaining : q % 120 = 1 ∨ q % 120 = 119
    · have hlarge : 239 ≤ q := by
        have hn119 : q ≠ 119 := by intro he; subst q; norm_num at hq
        have hn121 : q ≠ 121 := by intro he; subst q; norm_num at hq
        omega
      exact fibonacci_recurrence_polynomial_nonsquare.2.2 q k hq hlarge (by omega)
    · exact fibonacci_prime_power_modular_nonsquare q k hq hge
        (by omega) (by omega) (by omega) (by omega)
  let S := H.filter (fun p => 5 < p)
  have hS : ∀ p ∈ S, p.Prime ∧ 5 < p := by
    intro p hp
    exact ⟨hH p (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
  have hSeed : rankClosureSeed S ⊆ H := by
    intro p hp
    have hc : p = 2 ∨ p = 3 ∨ p = 5 ∨ p ∈ S := by
      simpa only [rankClosureSeed, Finset.mem_insert] using hp
    rcases hc with rfl | rfl | rfl | hp
    · exact hTwo
    · exact hThree
    · exact hFive
    · exact (Finset.mem_filter.mp hp).1
  have hClosure : fibonacciRankClosure S ⊆ H :=
    (finite_fibonacci_rank_closure S hS).2.2.2.2 H hSeed (by rw [hClosed])
  have hBlock : PrimeIndexOddFactor n := by
    intro ell hell hlarge _
    exact hOddFactor (Nat.fib ell) (Nat.fib_pos.mpr hell.pos)
      (fibonacci_odd_index_nonsquare ell (by omega) (hell.odd_iff.mpr (by omega)))
  have hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S := by
    intro p hp hlarge hpFib hpNot ho
    apply Finset.mem_filter.mpr
    refine ⟨hOdd p hp hpFib ?_, hlarge⟩
    rw [fibonacci_original_rank_valuation p n hp hpFib hpNot]
    exact ho
  have hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H := by
    intro p hp hpn
    exact hClosure ((original_odd_depth_support S hS n hn hBlock hExternal).1 p hp hpn)
  let R := H.lcm fibonacciRank
  have hRpos : 0 < R := by
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hH p hp, dite_true]
    exact (rankWitness p (hH p hp)).property.1.ne'
  have hLargeBudget (q : ℕ) (hq : q.Prime) (hqge : 7 ≤ q) :
      padicValNat q n ≤ padicValNat q R := by
    letI : Fact q.Prime := ⟨hq⟩
    let e := padicValNat q n
    by_contra hBound
    change ¬ e ≤ padicValNat q R at hBound
    have heLarge : 1 ≤ e := by omega
    have heIndex : q ^ e ∣ n := pow_padicValNat_dvd
    let M := q ^ (e - 1)
    let N := q ^ e
    let FM := Nat.fib M
    let FN := Nat.fib N
    let C := FN / FM
    have hEeq : e - 1 + 1 = e := by omega
    have hMpos : 0 < M := pow_pos hq.pos _
    have hNpos : 0 < N := pow_pos hq.pos _
    have hFMpos : 0 < FM := Nat.fib_pos.mpr hMpos
    have hFNpos : 0 < FN := Nat.fib_pos.mpr hNpos
    have hMN : M ∣ N := by
      dsimp [M, N]
      exact pow_dvd_pow q (by omega)
    have hFMFN : FM ∣ FN := Nat.fib_dvd M N hMN
    have hMul : FM * C = FN := Nat.mul_div_cancel' hFMFN
    have hCpos : 0 < C := Nat.div_pos (Nat.le_of_dvd hFNpos hFMFN) hFMpos
    have hCnotSquare : ¬ IsSquare C := by
      simpa only [C, FN, FM, N, M, hEeq] using (hLayers q (e - 1) hq hqge).2
    have hOddPrime := hOddFactor C hCpos hCnotSquare
    obtain ⟨p, hpPrime, hpC, hpOddC⟩ := hOddPrime
    letI : Fact p.Prime := ⟨hpPrime⟩
    have hpFN : p ∣ FN := by
      rw [← hMul]
      exact dvd_mul_of_dvd_right hpC FM
    have hrEqN : fibonacciRank p = N := by
      have hpC' : p ∣ Nat.fib (q ^ (e - 1 + 1)) / Nat.fib (q ^ (e - 1)) := by
        simpa only [C, FN, FM, N, M, hEeq] using hpC
      have hLargeRank (p k : ℕ) (hp : p.Prime)
          (hpFive : 5 < p) :
          let R := Nat.fib (p ^ (k + 1)) / Nat.fib (p ^ k)
          1 < R ∧
            ∀ q : ℕ, q.Prime → q ∣ R → fibonacciRank q = p ^ (k + 1) := by
        have prime_not_dvd_fib_prime_pow (p k : ℕ) (hp : p.Prime)
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
      simpa only [N, hEeq] using
        (hLargeRank q (e - 1) hq (by omega)).2 p hpPrime hpC'
    let r := rankWitness p hpPrime
    have hpNotQ : p ≠ q := by
      intro heq
      subst p
      have hRankBound := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
        hq (by omega : q ≠ 5) r.property.1 r.property.2.1 r.property.2.2
      have hreq : r.val = N := by
        simpa only [fibonacciRank, hq, dite_true, r] using hrEqN
      rw [hreq] at hRankBound
      have hd : q ∣ N := by simpa only [N, pow_one] using pow_dvd_pow q heLarge
      have hb := hd.trans hRankBound
      by_cases heps : legendreSym 5 q = 1
      · have hpred : q ∣ q - 1 := by simpa [heps] using hb
        have hsum : q ∣ (q - 1) + 1 := by
          simpa only [Nat.sub_add_cancel hq.one_le] using (dvd_refl q)
        have hone : q ∣ 1 :=
          (Nat.dvd_add_iff_right (m := q - 1) (n := 1) hpred).mpr hsum
        exact hq.ne_one (Nat.dvd_one.mp hone)
      · have hp : q ∣ q + 1 := by simpa [heps] using hb
        exact hq.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_self_left).mp hp))
    have hpNotPow (k : ℕ) : ¬ p ∣ q ^ k := by
      intro hpPow
      have hpQ : p ∣ q := hpPrime.dvd_of_dvd_pow hpPow
      exact hpNotQ ((Nat.prime_dvd_prime_iff_eq hpPrime hq).mp hpQ)
    have hpNotFM : ¬ p ∣ FM := by
      intro hpFM
      have hrDivM : r.val ∣ M :=
        (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          r.property.1 r.property.2.1 r.property.2.2).mp hpFM
      have hrEqN' : r.val = N := by
        simpa only [fibonacciRank, hpPrime, dite_true, r] using hrEqN
      have hNM : N ∣ M := hrEqN' ▸ hrDivM
      have hVal : e ≤ e - 1 := by
        have hPow : q ^ e ∣ q ^ (e - 1) := hNM
        exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hPow
      omega
    have hValFM : padicValNat p FM = 0 := padicValNat.eq_zero_of_not_dvd hpNotFM
    have hValFN : padicValNat p FN = padicValNat p C := by
      have hValMul : padicValNat p FN =
          padicValNat p FM + padicValNat p C := by
        rw [← hMul]
        exact padicValNat.mul hFMpos.ne' hCpos.ne'
      simpa only [hValFM, zero_add] using hValMul
    have hpNotH : p ∉ H := by
      intro hpH
      have hrR : fibonacciRank p ∣ R := Finset.dvd_lcm hpH
      have hNR : N ∣ R := hrEqN ▸ hrR
      have heLe : e ≤ padicValNat q R :=
        (padicValNat_dvd_iff_le (p := q) hRpos.ne').mp hNR
      exact hBound (by simpa only [e, R] using heLe)
    have hpFibN : p ∣ Nat.fib n :=
      hpFN.trans (Nat.fib_dvd N n (by simpa only [N] using heIndex))
    have hpNotIndex : ¬ p ∣ n := by
      intro hpIndex
      exact hpNotH (hIndex p hpPrime hpIndex)
    have hValIndex := fibonacci_original_rank_valuation p n hpPrime hpFibN hpNotIndex
    have hValN := fibonacci_original_rank_valuation p N hpPrime hpFN (hpNotPow e)
    have hOddIndex : Odd (padicValNat p (Nat.fib n)) := by
      rw [hValIndex, ← hValN, hValFN]
      exact hpOddC
    exact hpNotH (hOdd p hpPrime hpFibN hOddIndex)
  have hNonFive (q : ℕ) (hq : q.Prime) (hq5 : q ≠ 5) :
      padicValNat q n ≤ padicValNat q R := by
    by_cases hq2 : q = 2
    · subst q
      exact fibonacci_dyadic_rank_budget H n hH hThree hn hIndex hOdd
    by_cases hq3 : q = 3
    · subst q
      exact fibonacci_ternary_rank_budget H n hH hTwo hn hIndex hOdd
    have hqge : 7 ≤ q := by
      have ho := hq.odd_of_ne_two hq2
      obtain ⟨a, ha⟩ := ho
      have ht := hq.two_le
      omega
    exact hLargeBudget q hq hqge
  have hFiveBudget := fibonacci_five_adic_rank_budget H n hH hIndex hOdd
  refine ⟨?_, hNonFive, hFiveBudget⟩
  apply (Nat.factorization_le_iff_dvd hn.ne' (mul_ne_zero (by decide : (5 : ℕ) ≠ 0)
    hRpos.ne')).mp
  intro q
  by_cases hq : q.Prime
  · letI : Fact q.Prime := ⟨hq⟩
    rw [Nat.factorization_def n hq, Nat.factorization_def (5 * R) hq,
      padicValNat.mul (by decide : (5 : ℕ) ≠ 0) hRpos.ne']
    by_cases hq5 : q = 5
    · subst q
      simpa [padicValNat_self, add_comm] using hFiveBudget
    · have hz : padicValNat q 5 = 0 := padicValNat.eq_zero_of_not_dvd (by
        intro hd
        exact hq5 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp hd))
      rw [hz, zero_add]
      exact hNonFive q hq hq5
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

end D5.S3.Arith.Primes.FibonacciRankBudget

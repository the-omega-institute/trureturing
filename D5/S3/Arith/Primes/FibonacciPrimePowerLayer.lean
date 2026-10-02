/- GID: D5/S3/Arith/Primes/FibonacciPrimePowerLayer
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciPrimePowerLayer
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every unramified nontrivial prime-power Fibonacci layer has exact fresh ranks and odd depth. -/

import D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
import D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
import D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
import D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
import D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
import D5.S3.Arith.Primes.GoldenCubicBlockRanks

namespace D5.S3.Arith.Primes.FibonacciPrimePowerLayer

open D5.S1.Scale
open D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
open D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
open D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
open D5.S3.Arith.Primes.FibonacciRecurrencePolynomialNonsquare
open D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Primes.GoldenCubicBlockRanks

-- The all-prime layer combines valuation cancellation with nonsquare quotient estimates.
set_option maxHeartbeats 1800000 in
/-- Every nontrivial unramified prime-power layer has fresh prime factors of
exact entry rank, with unchanged original depths and an odd-depth witness. -/
theorem fibonacci_prime_power_layer (q s : ℕ) (hq : q.Prime) (hq5 : q ≠ 5) (hs : 1 ≤ s)
    (hexclude : ¬ (q = 2 ∧ s = 1)) :
    let C := Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))
    1 < C ∧ Nat.Coprime C (Nat.fib (q ^ (s - 1))) ∧ ¬ IsSquare C ∧
      (∀ p : ℕ, p.Prime → p ∣ C →
        fibonacciRank p = q ^ s ∧ p ≠ q ∧
          padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p))) ∧
      (∃ p : ℕ, p.Prime ∧ p ∣ C ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p)))) := by
  classical
  dsimp only
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let M := q ^ (s - 1)
  let N := q ^ s
  let FM := Nat.fib M
  let FN := Nat.fib N
  let C := FN / FM
  have heq : s - 1 + 1 = s := by omega
  have hMpos : 0 < M := pow_pos hq.pos _
  have hNpos : 0 < N := pow_pos hq.pos _
  have hNmul : N = M * q := by
    dsimp [N, M]
    nth_rw 1 [← heq]
    exact pow_succ _ _
  have hMltN : M < N := by rw [hNmul]; nlinarith [hq.two_le]
  have hNthree : 3 ≤ N := by
    by_cases hq2 : q = 2
    · have hs2 : 2 ≤ s := by omega
      have hb := Nat.pow_le_pow_right (by decide : 0 < 2) hs2
      change 3 ≤ q ^ s
      rw [hq2]
      exact le_trans (by decide : 3 ≤ 2 ^ 2) hb
    · have hq3 : 3 ≤ q := by have ht := hq.two_le; omega
      have hb := Nat.pow_le_pow_right hq.pos hs
      exact le_trans hq3 (by simpa only [pow_one] using hb)
  have hFMpos : 0 < FM := Nat.fib_pos.mpr hMpos
  have hFNpos : 0 < FN := Nat.fib_pos.mpr hNpos
  have hFMltFN : FM < FN := by
    by_cases hM2 : 2 ≤ M
    · exact (Nat.fib_lt_fib hM2).2 hMltN
    · have hMone : M = 1 := by omega
      have hFtwo : 2 ≤ FN := by
        calc
          2 = Nat.fib 3 := by decide
          _ ≤ Nat.fib N := Nat.fib_mono hNthree
      have hFMone : FM = 1 := by simp [FM, hMone]
      omega
  have hMN : M ∣ N := by
    dsimp [M, N]
    exact pow_dvd_pow q (by omega)
  have hFMFN : FM ∣ FN := Nat.fib_dvd M N hMN
  have hMul : FM * C = FN := Nat.mul_div_cancel' hFMFN
  have hCpos : 0 < C := Nat.div_pos (Nat.le_of_dvd hFNpos hFMFN) hFMpos
  have hCgt : 1 < C := by
    by_contra hn
    have hone : C = 1 := by omega
    rw [hone, mul_one] at hMul
    omega
  have hThreeQuotient (h3 : q = 3) (hs2 : 2 ≤ s) :
      (C : ℤ) = goldenLucas (3 ^ (s - 1)) ^ 2 + 1 := by
    have ht := (golden_cubic_fibonacci_block (s - 1) (by omega)).2.2
    rw [heq] at ht
    have hm : (FM : ℤ) * (C : ℤ) = (FN : ℤ) := by exact_mod_cast hMul
    have hf : (0 : ℤ) < FM := by exact_mod_cast hFMpos
    have ht' : (FN : ℤ) = (FM : ℤ) *
        (goldenLucas (3 ^ (s - 1)) ^ 2 + 1) := by
      simpa only [FN, FM, M, N, h3] using ht
    nlinarith
  have hRank (p : ℕ) (hp : p.Prime) (hpC : p ∣ C) :
      fibonacciRank p = N := by
    have hpFN : p ∣ FN := by
      rw [← hMul]
      exact dvd_mul_of_dvd_right hpC FM
    by_cases hq2 : q = 2
    · have hTwoEntry (m : ℕ) : 2 ∣ Nat.fib m ↔ 3 ∣ m := by
        apply D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          (by decide : 0 < 3) (by decide : 2 ∣ Nat.fib 3)
        intro j hj hFib
        by_contra hle
        have hjSmall : j = 1 ∨ j = 2 := by omega
        rcases hjSmall with rfl | rfl <;> norm_num at hFib
      have hpNotTwo : p ≠ 2 := by
        intro he
        subst p
        have hthree : 3 ∣ 2 ^ s := by
          simpa only [FN, N, hq2] using (hTwoEntry N).mp hpFN
        have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
        norm_num at hbad
      have hpNotPow (k : ℕ) : ¬ p ∣ q ^ k := by
        intro hpow
        have hpq : p ∣ q := hp.dvd_of_dvd_pow hpow
        have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
        exact hpNotTwo (he.trans hq2)
      let r := rankWitness p hp
      have hrN : r.val ∣ N :=
        (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          r.property.1 r.property.2.1 r.property.2.2).mp hpFN
      obtain ⟨j, hjLe, hjEq⟩ := (Nat.dvd_prime_pow hq).mp hrN
      have hjTop : j = s := by
        by_contra hne
        have hjLow : j ≤ s - 1 := by omega
        have hrM : r.val ∣ M := by
          rw [hjEq]
          exact pow_dvd_pow q hjLow
        have hpFM : p ∣ FM :=
          (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
            r.property.1 r.property.2.1 r.property.2.2).mpr hrM
        letI : Fact p.Prime := ⟨hp⟩
        have hvalN := fibonacci_original_rank_valuation p N hp hpFN (hpNotPow s)
        have hvalM := fibonacci_original_rank_valuation p M hp hpFM (hpNotPow (s - 1))
        have hvalSame : padicValNat p FN = padicValNat p FM := hvalN.trans hvalM.symm
        have hvalC : 0 < padicValNat p C :=
          one_le_padicValNat_of_dvd hCpos.ne' hpC
        have hvalMul : padicValNat p FN =
            padicValNat p FM + padicValNat p C := by
          rw [← hMul]
          exact padicValNat.mul hFMpos.ne' hCpos.ne'
        rw [hvalSame] at hvalMul
        omega
      simpa only [fibonacciRank, hp, dite_true, N] using
        (hjEq.trans (by rw [hjTop]))
    by_cases hq3 : q = 3
    · by_cases hs1 : s = 1
      · have hCtwo : C = 2 := by norm_num [C, FN, FM, N, M, hq3, hs1]
        have hpTwo : p = 2 :=
          (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hCtwo ▸ hpC)
        subst p
        let r := rankWitness 2 Nat.prime_two
        have hrGe : 3 ≤ r.val := by
          by_contra hn
          have hrSmall : r.val = 1 ∨ r.val = 2 := by have ht := r.property.1; omega
          rcases hrSmall with h | h <;>
            have hz := r.property.2.1 <;> rw [h] at hz <;> norm_num at hz
        have hrLe : r.val ≤ 3 := r.property.2.2 3 (by decide) (by decide)
        have hre : r.val = 3 := by omega
        simpa only [fibonacciRank, Nat.prime_two, dite_true, r, N, hq3, hs1, pow_one]
          using hre
      · have hc := hThreeQuotient hq3 (by omega)
        have hpInt : (p : ℤ) ∣ goldenLucas (3 ^ (s - 1)) ^ 2 + 1 := by
          rw [← hc]
          exact_mod_cast hpC
        simpa only [heq, N, hq3] using
          (cubic_block_c_prime_rank (s - 1) p (by omega) hp hpInt).1
    have hqLarge : 5 < q := by
      have ho := hq.odd_of_ne_two hq2
      obtain ⟨a, ha⟩ := ho
      have ht := hq.two_le
      omega
    have hpC' : p ∣ Nat.fib (q ^ (s - 1 + 1)) / Nat.fib (q ^ (s - 1)) := by
      simpa only [C, FN, FM, N, M, heq] using hpC
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
    simpa only [heq, N] using
      (hLargeRank q (s - 1) hq hqLarge).2 p hp hpC'
  have hFacts (p : ℕ) (hp : p.Prime) (hpC : p ∣ C) :
      fibonacciRank p = N ∧ p ≠ q ∧
        padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p)) ∧ ¬ p ∣ FM := by
    letI : Fact p.Prime := ⟨hp⟩
    have hr := hRank p hp hpC
    let r := rankWitness p hp
    have hrN : r.val = N := by
      simpa only [fibonacciRank, hp, dite_true, r] using hr
    have hpFN : p ∣ FN := by
      rw [← hMul]
      exact dvd_mul_of_dvd_right hpC FM
    have hpNotQ : p ≠ q := by
      intro he
      subst p
      have hb := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
        hq hq5 r.property.1 r.property.2.1 r.property.2.2
      rw [hrN] at hb
      have hqN : q ∣ N := by
        simpa only [N, pow_one] using pow_dvd_pow q hs
      have hd := hqN.trans hb
      by_cases heps : legendreSym 5 q = 1
      · have hpred : q ∣ q - 1 := by simpa [heps] using hd
        have hsum : q ∣ (q - 1) + 1 := by
          simpa only [Nat.sub_add_cancel hq.one_le] using dvd_refl q
        exact hq.ne_one (Nat.dvd_one.mp
          ((Nat.dvd_add_iff_right (m := q - 1) (n := 1) hpred).mpr hsum))
      · have hsucc : q ∣ q + 1 := by simpa [heps] using hd
        exact hq.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_self_left).mp hsucc))
    have hpNotN : ¬ p ∣ N := by
      intro hpn
      exact hpNotQ ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpn))
    have hpNotFM : ¬ p ∣ FM := by
      intro hpFM
      have hrM : r.val ∣ M :=
        (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          r.property.1 r.property.2.1 r.property.2.2).mp hpFM
      rw [hrN] at hrM
      have hle : s ≤ s - 1 :=
        (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hrM
      omega
    have hvalMul : padicValNat p FN =
        padicValNat p FM + padicValNat p C := by
      rw [← hMul]
      exact padicValNat.mul hFMpos.ne' hCpos.ne'
    have hvalZero : padicValNat p FM = 0 := padicValNat.eq_zero_of_not_dvd hpNotFM
    have hvalN := fibonacci_original_rank_valuation p N hp hpFN hpNotN
    refine ⟨hr, hpNotQ, ?_, hpNotFM⟩
    simpa only [hvalZero, zero_add] using hvalMul.symm.trans hvalN
  have hCoprime : Nat.Coprime C FM := by
    by_contra hn
    obtain ⟨p, hp, hpC, hpFM⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact (hFacts p hp hpC).2.2.2 hpFM
  have hNS : ¬ IsSquare C := by
    by_cases hq2 : q = 2
    · have hs2 : 2 ≤ s := by omega
      simpa only [C, FN, FM, N, M, hq2, heq] using
        (fibonacci_dyadic_quotient_nonsquare (s - 1) (by omega)).2.2
    by_cases hq3 : q = 3
    · by_cases hs1 : s = 1
      · have hCtwo : C = 2 := by norm_num [C, FN, FM, N, M, hq3, hs1]
        rw [hCtwo]
        exact Nat.prime_two.not_isSquare
      · have hc := hThreeQuotient hq3 (by omega)
        have hx := (golden_cubic_lucas_block (s - 1) (by omega)).2.2.2.1
        have hCmod : (C : ZMod 5) = 2 := by
          have ht := congrArg (fun z : ℤ => (z : ZMod 5)) hc
          push_cast at ht hx
          rw [hx] at ht
          simpa only [show (1 : ZMod 5) + 1 = 2 by decide] using ht
        intro hSquare
        have hm := hSquare.map (Nat.castRingHom (ZMod 5))
        change IsSquare (C : ZMod 5) at hm
        rw [hCmod] at hm
        exact (by decide : ¬ IsSquare (2 : ZMod 5)) hm
    have hqge : 7 ≤ q := by
      have ho := hq.odd_of_ne_two hq2
      obtain ⟨a, ha⟩ := ho
      have ht := hq.two_le
      omega
    have hLayers (k : ℕ) :
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) := by
      by_cases hk0 : k = 0
      · subst k
        simp only [zero_add, pow_one, pow_zero, Nat.fib_one, Nat.div_one]
        exact fibonacci_odd_index_nonsquare q (by omega)
          (hq.odd_iff.mpr (by omega))
      by_cases h31 : q % 120 = 49 ∨ q % 120 = 71
      · exact (fibonacci_prime_power_mod31_nonsquare q k hq hqge h31).2.2
      by_cases hremaining : q % 120 = 1 ∨ q % 120 = 119
      · have hlarge : 239 ≤ q := by
          have hn119 : q ≠ 119 := by intro he; subst q; norm_num at hq
          have hn121 : q ≠ 121 := by intro he; subst q; norm_num at hq
          omega
        exact (fibonacci_recurrence_polynomial_nonsquare.2.2 q k hq hlarge (by omega)).2
      · exact (fibonacci_prime_power_modular_nonsquare q k hq hqge
          (by omega) (by omega) (by omega) (by omega)).2
    simpa only [C, FN, FM, N, M, heq] using hLayers (s - 1)
  have hOddFactor : ∃ p : ℕ, p.Prime ∧ p ∣ C ∧ Odd (padicValNat p C) := by
    by_contra hNone
    have hEven (p : ℕ) (hp : p ∈ C.primeFactors) : Even (C.factorization p) := by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDiv := Nat.dvd_of_mem_primeFactors hp
      have hpNotOdd : ¬ Odd (padicValNat p C) := by
        intro hpOdd
        exact hNone ⟨p, hpPrime, hpDiv, hpOdd⟩
      rw [Nat.factorization_def C hpPrime]
      exact Nat.not_odd_iff_even.mp hpNotOdd
    let a := ∏ p ∈ C.primeFactors, p ^ (C.factorization p / 2)
    have hSquare : C = a ^ 2 := by
      rw [Nat.prod_primeFactors_pow_factorization hCpos.ne']
      dsimp only [a]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      obtain ⟨j, hj⟩ := hEven p hp
      omega
    exact hNS ⟨a, by simpa [pow_two] using hSquare⟩
  refine ⟨hCgt, hCoprime, hNS, ?_, ?_⟩
  · intro p hp hpC
    have hf := hFacts p hp hpC
    exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  · obtain ⟨p, hp, hpC, hOdd⟩ := hOddFactor
    exact ⟨p, hp, hpC, (hFacts p hp hpC).2.2.1 ▸ hOdd⟩

end D5.S3.Arith.Primes.FibonacciPrimePowerLayer

/- GID: D5/S3/Arith/Primes/PowerfulFibonacciSupportBound
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/PowerfulFibonacciSupportBound
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Original odd-depth support bounds powerful Fibonacci indices. -/

import D5.S3.Arith.Primes.OriginalOddDepthSupport
import D5.S3.Arith.Primes.FibSquareclassRigidity
import D5.S3.Arith.Primes.FibonacciFiveAdicDepth
import D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
import D5.S3.Arith.Powerful.PowerfulNumber
import Mathlib

namespace D5.S3.Arith.Primes.PowerfulFibonacciSupportBound

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.OriginalOddDepthSupport
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Primes.FibSquareclassRigidity
open D5.S3.Arith.Primes.FibonacciFiveAdicDepth
open D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
open D5.S3.Arith.Powerful.PowerfulNumber

/-- Prime support occurring to odd multiplicity in the original Fibonacci value. -/
def oddPrimeSupport (n : ℕ) : Finset ℕ :=
  (Nat.fib n).primeFactors.filter
    (fun p => Odd (padicValNat p (Nat.fib n)))

/-- Positive powerful Fibonacci indices whose odd original depths above two lie in `S`. -/
def supportedPowerfulIndex (S : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ Powerful (Nat.fib n) ∧
    ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) →
      3 ≤ padicValNat p (Nat.fib (fibonacciRank p)) → p ∈ S

/-- Supported powerful Fibonacci indices form a set of at most
`2 ^ |H(S)| - 4` elements. -/
theorem powerful_fibonacci_support_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 < p) :
    ∃ A : Finset ℕ,
      (∀ n, n ∈ A ↔ supportedPowerfulIndex S n) ∧
      A.card ≤ 2 ^ (fibonacciRankClosure S).card - 4 := by
  classical
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
    exact hns ⟨s, by simpa [pow_two] using hSquare⟩
  have hBlock : ∀ n, PrimeIndexOddFactor n := by
    intro n ell hell hlarge _
    exact hOddFactor (Nat.fib ell) (Nat.fib_pos.mpr hell.pos)
      (fibonacci_odd_index_nonsquare ell (by omega)
        (hell.odd_iff.mpr (by omega)))
  have hFiveSmooth : ∀ n, 0 < n → Powerful (Nat.fib n) →
      (∀ p, p.Prime → p ∣ n → p ≤ 5) →
      n ∈ ({1, 2, 6, 12} : Finset ℕ) := by
    intro n hn hpower hIndexSmall
    have hn0 : n ≠ 0 := hn.ne'
    have hFn0 : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr hn).ne'
    have hNoDeep (p d : ℕ) (hp : p.Prime) (hpd : p ∣ Nat.fib d)
        (hp2 : ¬ p ^ 2 ∣ Nat.fib d) (hpn : ¬ p ∣ n) : ¬ d ∣ n := by
      intro hd
      letI : Fact p.Prime := ⟨hp⟩
      have hpFn : p ∣ Nat.fib n := hpd.trans (Nat.fib_dvd d n hd)
      have hrDiv : fibonacciRank p ∣ d := by
        let r := rankWitness p hp
        have hr := (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          r.property.1 r.property.2.1 r.property.2.2).mp hpd
        simpa [fibonacciRank, hp, r] using hr
      have hrPos : 0 < fibonacciRank p := by
        simpa [fibonacciRank, hp] using (rankWitness p hp).property.1
      have hFrr0 : Nat.fib (fibonacciRank p) ≠ 0 :=
        (Nat.fib_pos.mpr hrPos).ne'
      have hrSqNo : ¬ p ^ 2 ∣ Nat.fib (fibonacciRank p) := by
        intro h
        exact hp2 (h.trans (Nat.fib_dvd _ _ hrDiv))
      have hvFn : 2 ≤ padicValNat p (Nat.fib n) :=
        (padicValNat_dvd_iff_le (p := p) (n := 2) hFn0).mp
          (hpower.2 p hp hpFn)
      have hvRank : padicValNat p (Nat.fib (fibonacciRank p)) < 2 := by
        by_contra h
        have hge : 2 ≤ padicValNat p (Nat.fib (fibonacciRank p)) := by omega
        exact hrSqNo ((padicValNat_dvd_iff_le (p := p) (n := 2) hFrr0).mpr hge)
      rw [fibonacci_original_rank_valuation p n hp hpFn hpn] at hvFn
      omega
    have hNo8 : ¬ 8 ∣ n := hNoDeep 7 8 (by decide) (by decide)
      (by decide) (by
        intro h
        have := hIndexSmall 7 (by decide) h
        omega)
    have hNo9 : ¬ 9 ∣ n := hNoDeep 17 9 (by decide) (by decide)
      (by decide) (by
        intro h
        have := hIndexSmall 17 (by decide) h
        omega)
    have hp3001 : Nat.Prime 3001 := by norm_num
    have hFib25 : Nat.fib 25 = 75025 := by norm_num
    have hNo25 : ¬ 25 ∣ n := hNoDeep 3001 25 hp3001
      (by rw [hFib25]; norm_num) (by rw [hFib25]; norm_num) (by
        intro h
        have := hIndexSmall 3001 hp3001 h
        omega)
    have hNo5 : ¬ 5 ∣ n := by
      intro h5
      letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have h5Fib : 5 ∣ Nat.fib n :=
        (by decide : 5 ∣ Nat.fib 5).trans (Nat.fib_dvd 5 n h5)
      have hvFn : 2 ≤ padicValNat 5 (Nat.fib n) :=
        (padicValNat_dvd_iff_le (p := 5) (n := 2) hFn0).mp
          (hpower.2 5 Nat.prime_five h5Fib)
      rw [fibonacci_five_adic_depth n hn] at hvFn
      exact hNo25 ((padicValNat_dvd_iff_le (p := 5) (n := 2) hn0).mpr hvFn)
    have h12Factorization : (12 : ℕ).factorization =
        Finsupp.single 2 2 + Finsupp.single 3 1 := by
      rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.Prime.factorization_pow Nat.prime_two,
        Nat.Prime.factorization Nat.prime_three]
    have hfac : n.factorization ≤ (12 : ℕ).factorization := by
      intro p
      by_cases hp : p.Prime
      · by_cases hp2 : p = 2
        · subst p
          have hv : n.factorization 2 < 3 := by
            by_contra h
            exact hNo8 ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr
              (by omega : 3 ≤ n.factorization 2))
          have h12 : (12 : ℕ).factorization 2 = 2 := by
            simp [h12Factorization]
          omega
        by_cases hp3 : p = 3
        · subst p
          have hv : n.factorization 3 < 2 := by
            by_contra h
            exact hNo9 ((Nat.prime_three.pow_dvd_iff_le_factorization hn0).mpr
              (by omega : 2 ≤ n.factorization 3))
          have h12 : (12 : ℕ).factorization 3 = 1 := by
            simp [h12Factorization]
          omega
        have hpn : ¬ p ∣ n := by
          intro h
          have hp5 := hIndexSmall p hp h
          have hp2le := hp.two_le
          have hp4 : p ≠ 4 := by intro h4; subst p; norm_num at hp
          have hp5eq : p = 5 := by omega
          exact hNo5 (hp5eq ▸ h)
        rw [Nat.factorization_eq_zero_of_not_dvd hpn]
        exact Nat.zero_le _
      · rw [Nat.factorization_eq_zero_of_not_prime n hp]
        exact Nat.zero_le _
    have hnDiv12 : n ∣ 12 :=
      (Nat.factorization_le_iff_dvd hn0 (by decide : (12 : ℕ) ≠ 0)).mp hfac
    have hnLe : n ≤ 12 := Nat.le_of_dvd (by decide) hnDiv12
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 12 := by
      interval_cases n <;> (norm_num at hnDiv12 <;> norm_num)
    rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
    · simp [h1]
    · simp [h2]
    · subst n
      have hsq : 2 ^ 2 ∣ Nat.fib 3 := hpower.2 2 (by decide) (by decide)
      norm_num at hsq
    · subst n
      have hsq : 3 ^ 2 ∣ Nat.fib 4 := hpower.2 3 (by decide) (by decide)
      norm_num at hsq
    · simp [h6]
    · simp [h12]
  have hSquareUnique : ∀ n m, 0 < n → 0 < m →
      ¬ oddPrimeSupport n ⊆ ({2, 3, 5} : Finset ℕ) →
      oddPrimeSupport n = oddPrimeSupport m → n = m := by
    intro n m hn hm hlarge hsame
    have hFn0 : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr hn).ne'
    have hFm0 : Nat.fib m ≠ 0 := (Nat.fib_pos.mpr hm).ne'
    have hOddIff (p : ℕ) (hp : p.Prime) :
        Odd (padicValNat p (Nat.fib n)) ↔
          Odd (padicValNat p (Nat.fib m)) := by
      letI : Fact p.Prime := ⟨hp⟩
      have hMem (k : ℕ) (hk : 0 < k) :
          Odd (padicValNat p (Nat.fib k)) ↔ p ∈ oddPrimeSupport k := by
        constructor
        · intro ho
          have hv : 0 < padicValNat p (Nat.fib k) := by
            rcases ho with ⟨v, hv⟩
            omega
          have hf0 : Nat.fib k ≠ 0 := (Nat.fib_pos.mpr hk).ne'
          have hpFib : p ∣ Nat.fib k := by
            simpa only [pow_one] using
              (padicValNat_dvd_iff_le (p := p) (n := 1) hf0).mpr (by omega)
          exact Finset.mem_filter.mpr
            ⟨Nat.mem_primeFactors.mpr ⟨hp, hpFib, hf0⟩, ho⟩
        · exact fun h => (Finset.mem_filter.mp h).2
      calc
        Odd (padicValNat p (Nat.fib n)) ↔ p ∈ oddPrimeSupport n := hMem n hn
        _ ↔ p ∈ oddPrimeSupport m := by rw [hsame]
        _ ↔ Odd (padicValNat p (Nat.fib m)) := (hMem m hm).symm
    have hSquareOfEven (a : ℕ) (ha : 0 < a)
        (he : ∀ p : ℕ, p.Prime → Even (padicValNat p a)) : IsSquare a := by
      have hEven (p : ℕ) (hp : p ∈ a.primeFactors) :
          Even (a.factorization p) := by
        rw [Nat.factorization_def a (Nat.prime_of_mem_primeFactors hp)]
        exact he p (Nat.prime_of_mem_primeFactors hp)
      let s := ∏ p ∈ a.primeFactors, p ^ (a.factorization p / 2)
      have hSq : a = s ^ 2 := by
        rw [Nat.prod_primeFactors_pow_factorization ha.ne']
        dsimp only [s]
        rw [← Finset.prod_pow]
        apply Finset.prod_congr rfl
        intro p hp
        rw [← pow_mul]
        congr 1
        obtain ⟨v, hv⟩ := hEven p hp
        omega
      exact ⟨s, by simpa [pow_two] using hSq⟩
    have hSquare : IsSquare (Nat.fib n * Nat.fib m) := by
      apply hSquareOfEven _ (mul_pos (Nat.fib_pos.mpr hn) (Nat.fib_pos.mpr hm))
      intro p hp
      letI : Fact p.Prime := ⟨hp⟩
      rw [padicValNat.mul hFn0 hFm0]
      have hParity := hOddIff p hp
      by_cases h : Odd (padicValNat p (Nat.fib n))
      · have hmOdd := hParity.mp h
        obtain ⟨r, hr⟩ := h
        obtain ⟨s, hs⟩ := hmOdd
        refine ⟨r + s + 1, ?_⟩
        omega
      · exact (Nat.not_odd_iff_even.mp h).add
          (Nat.not_odd_iff_even.mp (fun hmOdd => h (hParity.mpr hmOdd)))
    have hSmallK (k : ℕ)
        (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 ∨ k = 12) :
        oddPrimeSupport k ⊆ ({2, 3, 5} : Finset ℕ) := by
      have hFromFactors (j v : ℕ) (hj : Nat.fib j = v)
          (hv : v.primeFactors ⊆ ({2, 3, 5} : Finset ℕ)) :
          oddPrimeSupport j ⊆ ({2, 3, 5} : Finset ℕ) := by
        unfold oddPrimeSupport
        rw [hj]
        exact (Finset.filter_subset _ _).trans hv
      rcases hk with h1 | h2 | h3 | h6 | h12
      · subst k; exact hFromFactors 1 1 (by norm_num) (by simp)
      · subst k; exact hFromFactors 2 1 (by norm_num) (by simp)
      · subst k; exact hFromFactors 3 2 (by norm_num) (by simp [Nat.prime_two])
      · subst k; exact hFromFactors 6 8 (by norm_num) (by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.primeFactors_pow 2 (by decide)]; simp [Nat.prime_two])
      · subst k; exact hFromFactors 12 144 (by norm_num) (by rw [show (144 : ℕ) = 2 ^ 4 * 3 ^ 2 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 2 (by decide), Nat.primeFactors_pow 3 (by decide)]; simp [Nat.prime_two, Nat.prime_three])
    rcases (fibonacci_squareclass_pairs n m hn hm).mp hSquare with heq | h123 | h36
    · exact heq
    · rcases h123.1 with h1 | h2 | h12
      · exact (hlarge (hSmallK n (Or.inl h1))).elim
      · exact (hlarge (hSmallK n (Or.inr (Or.inl h2)))).elim
      · exact (hlarge (hSmallK n (Or.inr (Or.inr (Or.inr (Or.inr h12)))))).elim
    · rcases h36.1 with h3 | h6
      · exact (hlarge (hSmallK n (Or.inr (Or.inr (Or.inl h3))))).elim
      · exact (hlarge (hSmallK n (Or.inr (Or.inr (Or.inr (Or.inl h6)))))).elim
  let B : Finset ℕ := {2, 3, 5}
  let E : Finset ℕ := {1, 2, 6, 12}
  let H := fibonacciRankClosure S
  have hBH : B ⊆ H := by
    intro p hp
    have hSeed := (finite_fibonacci_rank_closure S hS).1
    have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
      simpa [B] using hp
    rcases hpCases with h2 | h3 | h5
    · exact hSeed (by simp [rankClosureSeed, h2])
    · exact hSeed (by simp [rankClosureSeed, h3])
    · exact hSeed (by simp [rankClosureSeed, h5])
  have hHPrime : ∀ p ∈ H, p.Prime :=
    (finite_fibonacci_rank_closure S hS).2.1
  have hSupport : ∀ n, supportedPowerfulIndex S n → oddPrimeSupport n ⊆ H := by
    intro n hn p hpK
    rcases hn with ⟨hnpos, hpower, hT⟩
    have hExternal : ∀ q : ℕ, q.Prime → 5 < q → q ∣ Nat.fib n → ¬ q ∣ n →
        Odd (padicValNat q (Nat.fib (fibonacciRank q))) → q ∈ S := by
      intro q hq hq5 hqFib hqN hqOdd
      have : Fact q.Prime := ⟨hq⟩
      have hFib0 : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr hnpos).ne'
      have hDepthTwo : 2 ≤ padicValNat q (Nat.fib n) :=
        (padicValNat_dvd_iff_le (p := q) (n := 2) hFib0).mp
          (hpower.2 q hq hqFib)
      have hDepthThree : 3 ≤ padicValNat q (Nat.fib (fibonacciRank q)) := by
        have hOddN : Odd (padicValNat q (Nat.fib n)) := by
          rw [fibonacci_original_rank_valuation q n hq hqFib hqN]
          exact hqOdd
        rw [← fibonacci_original_rank_valuation q n hq hqFib hqN]
        rcases hOddN with ⟨k, hk⟩
        omega
      exact hT q hq hq5 hqFib hqOdd hDepthThree
    have hKernel := (original_odd_depth_support S hS n hnpos
      (hBlock n) hExternal).2
    have hpDvdK : p ∣ oddDepthKernel n := by
      change p ∣ (oddPrimeSupport n).prod id
      exact Finset.dvd_prod_of_mem id hpK
    have hpPrime : p.Prime :=
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpK).1).1
    obtain ⟨q, hqH, hpDvdQ⟩ :=
      (hpPrime.prime.dvd_finsetProd_iff id).mp (hpDvdK.trans hKernel)
    have hpEqQ := (Nat.prime_dvd_prime_iff_eq hpPrime (hHPrime q hqH)).mp hpDvdQ
    simpa [hpEqQ] using hqH
  have hSmall : ∀ n, supportedPowerfulIndex S n → oddPrimeSupport n ⊆ B → n ∈ E := by
    intro n hn hKSmall
    rcases hn with ⟨hnpos, hpower, _⟩
    have hExternalEmpty : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ (∅ : Finset ℕ) := by
      intro p hp hp5 hpFib hpN hpOdd
      have hOddN : Odd (padicValNat p (Nat.fib n)) := by
        rw [fibonacci_original_rank_valuation p n hp hpFib hpN]
        exact hpOdd
      have hpK : p ∈ oddPrimeSupport n := by
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hp, hpFib, (Nat.fib_pos.mpr hnpos).ne'⟩, hOddN⟩
      have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
        simpa [B] using hKSmall hpK
      omega
    have hIndexSupport :=
      (original_odd_depth_support ∅ (by simp) n hnpos
        (hBlock n) hExternalEmpty).1
    have hIndexSmall : ∀ p, p.Prime → p ∣ n → p ≤ 5 := by
      intro p hp hpN
      have hpH := hIndexSupport p hp hpN
      have hpBound := (finite_fibonacci_rank_closure ∅ (by simp)).2.2.1 p hpH
      simpa using hpBound
    exact hFiveSmooth n hnpos hpower hIndexSmall
  let K := oddPrimeSupport
  let Good := supportedPowerfulIndex S
  have hBcard : B.card = 3 := by decide
  have hEcard : E.card = 4 := by decide
  have hUnique : ∀ n m, Good n → Good m → ¬ K n ⊆ B →
      K n = K m → n = m := by
    intro n m hn hm hlarge hsame
    exact hSquareUnique n m hn.1 hm.1 hlarge hsame
  let G : Set ℕ := {n | Good n}
  let Gsmall : Set ℕ := {n | Good n ∧ K n ⊆ B}
  let Glarge : Set ℕ := {n | Good n ∧ ¬ K n ⊆ B}
  have hSmallFinite : Gsmall.Finite :=
    E.finite_toSet.subset (by
      intro n hn
      exact hSmall n hn.1 hn.2)
  have hLargeImage : (K '' Glarge).Finite :=
    (H.powerset).finite_toSet.subset (by
      rintro k ⟨n, hn, rfl⟩
      exact Finset.mem_powerset.mpr (hSupport n hn.1))
  have hLargeInj : Set.InjOn K Glarge := by
    intro n hn m hm hnm
    exact hUnique n m hn.1 hm.1 hn.2 hnm
  have hLargeFinite : Glarge.Finite :=
    Set.Finite.of_finite_image hLargeImage hLargeInj
  have hGFinite : G.Finite :=
    (hSmallFinite.union hLargeFinite).subset (by
      intro n hn
      by_cases h : K n ⊆ B
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩)
  let A := hGFinite.toFinset
  have hA (n : ℕ) : n ∈ A ↔ Good n := by
    simp [A, G]
  let As := A.filter (fun n => K n ⊆ B)
  let Al := A.filter (fun n => ¬ K n ⊆ B)
  have hAsSubset : As ⊆ E := by
    intro n hn
    have hnf := Finset.mem_filter.mp hn
    exact hSmall n ((hA n).mp hnf.1) hnf.2
  have hAsCard : As.card ≤ 4 := by
    rw [← hEcard]
    exact Finset.card_le_card hAsSubset
  have hAlMaps : Set.MapsTo K (Al : Set ℕ)
      ((H.powerset \ B.powerset : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro n hn
    have hnf := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_powerset.mpr (hSupport n ((hA n).mp hnf.1)),
        fun hsmall => hnf.2 (Finset.mem_powerset.mp hsmall)⟩
  have hAlInj : Set.InjOn K (Al : Set ℕ) := by
    intro n hn m hm hnm
    have hnn := Finset.mem_filter.mp hn
    have hmn := Finset.mem_filter.mp hm
    exact hUnique n m ((hA n).mp hnn.1) ((hA m).mp hmn.1) hnn.2 hnm
  have hAlCard : Al.card ≤ (H.powerset \ B.powerset).card :=
    Finset.card_le_card_of_injOn K hAlMaps hAlInj
  have hPowerSubset : B.powerset ⊆ H.powerset :=
    Finset.powerset_mono.mpr hBH
  have hPowerB : B.powerset.card = 8 := by
    rw [Finset.card_powerset, hBcard]
    decide
  have hPowerH : H.powerset.card = 2 ^ H.card := Finset.card_powerset H
  have hEight : 8 ≤ 2 ^ H.card := by
    rw [← hPowerB, ← hPowerH]
    exact Finset.card_le_card hPowerSubset
  have hSlots : (H.powerset \ B.powerset).card = 2 ^ H.card - 8 := by
    rw [Finset.card_sdiff_of_subset hPowerSubset, hPowerH, hPowerB]
  have hPartition : As.card + Al.card = A.card := by
    exact Finset.card_filter_add_card_filter_not (fun n => K n ⊆ B)
  refine ⟨A, hA, ?_⟩
  rw [← hPartition]
  change As.card + Al.card ≤ 2 ^ H.card - 4
  rw [hSlots] at hAlCard
  omega

end D5.S3.Arith.Primes.PowerfulFibonacciSupportBound

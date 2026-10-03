/- GID: D5/S3/Arith/Primes/FibonacciExternalWitnessGrowth
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciExternalWitnessGrowth
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Actual external odd-depth Fibonacci prime witnesses grow at least logarithmically. -/

import D5.S3.Arith.Primes.FibonacciRankBudget
import D5.S3.Arith.Powerful.PowerfulNumber
import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Real


namespace D5.S3.Arith.Primes.FibonacciExternalWitnessGrowth

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciOddIndexNonsquare
open D5.S3.Arith.Primes.FibonacciRankBudget
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Primes.OriginalOddDepthSupport
open D5.S3.Arith.Powerful.PowerfulNumber
open Filter
open scoped Topology ENNReal
open scoped Chebyshev

/-- The actual largest external odd-depth prime has a logarithmic lower growth bound.
For powerful Fibonacci values it is eventually an original odd-super-depth WSS prime. -/
theorem fibonacci_external_witness_growth :
    let P : ℕ → ℕ := fun n =>
      max 5 (((Nat.fib n).primeFactors.filter (fun p =>
        5 < p ∧ ¬ p ∣ n ∧
          Odd (padicValNat p (Nat.fib (fibonacciRank p))))).sup id)
    (∀ n : ℕ, 0 < n →
      Real.log (n : ℝ) ≤
        Real.log 10 + Chebyshev.psi ((max 5 ((P n + 1) / 2) : ℕ) : ℝ)) ∧
    Tendsto P atTop atTop ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (2 - ε) * Real.log (n : ℝ) ≤ (P n : ℝ)) ∧
    ((2 : ℝ≥0∞) ≤ Filter.liminf
      (fun n : ℕ => ENNReal.ofReal ((P n : ℝ) / Real.log (n : ℝ))) atTop) ∧
    (∀ᶠ n : ℕ in atTop, Powerful (Nat.fib n) →
      ∃ p : ℕ, p = P n ∧ p.Prime ∧ 5 < p ∧ p ∣ Nat.fib n ∧ ¬ p ∣ n ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) ∧
        3 ≤ padicValNat p (Nat.fib (fibonacciRank p)) ∧
        p ^ 2 ∣ Nat.fib (fibonacciRank p)) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let U : ℕ → Finset ℕ := fun n =>
    (Nat.fib n).primeFactors.filter (fun p =>
      5 < p ∧ ¬ p ∣ n ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p))))
  let P : ℕ → ℕ := fun n => max 5 ((U n).sup id)
  let Y : ℕ → ℕ := fun Q => max 5 ((Q + 1) / 2)
  change
    (∀ n : ℕ, 0 < n →
      Real.log (n : ℝ) ≤ Real.log 10 + Chebyshev.psi (Y (P n) : ℝ)) ∧
    Tendsto P atTop atTop ∧
    (∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (2 - ε) * Real.log (n : ℝ) ≤ (P n : ℝ)) ∧
    ((2 : ℝ≥0∞) ≤ Filter.liminf
      (fun n : ℕ => ENNReal.ofReal ((P n : ℝ) / Real.log (n : ℝ))) atTop) ∧
    (∀ᶠ n : ℕ in atTop, Powerful (Nat.fib n) →
      ∃ p : ℕ, p = P n ∧ p.Prime ∧ 5 < p ∧ p ∣ Nat.fib n ∧ ¬ p ∣ n ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) ∧
        3 ≤ padicValNat p (Nat.fib (fibonacciRank p)) ∧
        p ^ 2 ∣ Nat.fib (fibonacciRank p))
  have hUniform (Q n : ℕ) (hQ : 5 ≤ Q) (hn : 0 < n)
      (hU : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ≤ Q) :
      n ∣ 10 * Nat.lcmUpto (Y Q) := by
    change n ∣ 10 * Nat.lcmUpto (max 5 ((Q + 1) / 2))
    classical
    let S : Finset ℕ := (Finset.range (Q + 1)).filter (fun p => p.Prime ∧ 5 < p)
    let H := fibonacciRankClosure S
    let Y := max 5 ((Q + 1) / 2)
    have hS : ∀ p ∈ S, p.Prime ∧ 5 < p := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hSsup : S.sup id ≤ Q := by
      apply Finset.sup_le
      intro p hp
      have hpRange := (Finset.mem_filter.mp hp).1
      simp only [Finset.mem_range] at hpRange
      simpa only [id_eq] using (show p ≤ Q by omega)
    have hHprime : ∀ p ∈ H, p.Prime :=
      (finite_fibonacci_rank_closure S hS).2.1
    have hHbound : ∀ p ∈ H, p ≤ Q := by
      intro p hp
      have hb := (finite_fibonacci_rank_closure S hS).2.2.1 p hp
      have hmax : max 5 (S.sup id) ≤ Q := max_le hQ hSsup
      exact hb.trans hmax
    have hSeed : rankClosureSeed S ⊆ H :=
      (finite_fibonacci_rank_closure S hS).1
    have hClosed : rankClosureStep H = H :=
      (finite_fibonacci_rank_closure S hS).2.2.2.1
    have hSmall (p : ℕ) (hp : p.Prime) (hp5 : p ≤ 5) : p ∈ H := by
      have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
        have hpTwo := hp.two_le
        have hpNeFour : p ≠ 4 := by
          intro heq
          rw [heq] at hp
          norm_num at hp
        omega
      rcases hpCases with h2 | h3 | h5
      · exact hSeed (by simp [rankClosureSeed, h2])
      · exact hSeed (by simp [rankClosureSeed, h3])
      · exact hSeed (by simp [rankClosureSeed, h5])
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
    have hBlock : PrimeIndexOddFactor n := by
      intro ell hell hlarge _
      exact hOddFactor (Nat.fib ell) (Nat.fib_pos.mpr hell.pos)
        (fibonacci_odd_index_nonsquare ell (by omega)
          (hell.odd_iff.mpr (by omega)))
    have hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S := by
      intro p hp hpLarge hpFib hpIndex hpOdd
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by have := hU p hp hpLarge hpFib hpIndex hpOdd; omega),
          ⟨hp, hpLarge⟩⟩
    have hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H :=
      (original_odd_depth_support S hS n hn hBlock hExternal).1
    have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H := by
      intro p hp hpFib hpOdd
      by_cases hpIndex : p ∣ n
      · exact hIndex p hp hpIndex
      by_cases hpLarge : 5 < p
      · have hpOriginal : Odd (padicValNat p (Nat.fib (fibonacciRank p))) := by
          rw [← fibonacci_original_rank_valuation p n hp hpFib hpIndex]
          exact hpOdd
        exact hSeed (by simp [rankClosureSeed,
          hExternal p hp hpLarge hpFib hpIndex hpOriginal])
      · exact hSmall p hp (by omega)
    have hBudget : n ∣ 5 * H.lcm fibonacciRank :=
      (fibonacci_rank_budget H n hHprime
        (hSeed (by simp [rankClosureSeed]))
        (hSeed (by simp [rankClosureSeed]))
        (hSeed (by simp [rankClosureSeed]))
        hClosed hn hOdd).1
    have hY5 : 5 ≤ Y := le_max_left _ _
    have hYhalf : (Q + 1) / 2 ≤ Y := le_max_right _ _
    have hRankL (p : ℕ) (hpH : p ∈ H) :
        fibonacciRank p ∣ 2 * Nat.lcmUpto Y := by
      have hp : p.Prime := hHprime p hpH
      let r := rankWitness p hp
      have hEntry (k : ℕ) (hpk : p ∣ Nat.fib k) : fibonacciRank p ∣ k := by
        have hr := (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
          r.property.1 r.property.2.1 r.property.2.2).mp hpk
        simpa only [fibonacciRank, hp, dite_true, r] using hr
      have hDivL (k : ℕ) (hk1 : 1 ≤ k) (hkY : k ≤ Y) :
          k ∣ Nat.lcmUpto Y := by
        unfold Nat.lcmUpto
        exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk1, hkY⟩)
      by_cases hpLarge : 5 < p
      · have hpBound : p ≤ Q := hHbound p hpH
        have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
        obtain ⟨j, hj⟩ := hpOdd
        have hrBound := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
          hp (by omega : p ≠ 5) r.property.1 r.property.2.1 r.property.2.2
        have hrBound' : fibonacciRank p ∣
            if legendreSym 5 p = 1 then p - 1 else p + 1 := by
          simpa only [fibonacciRank, hp, dite_true, r] using hrBound
        by_cases heps : legendreSym 5 p = 1
        · have hr : fibonacciRank p ∣ p - 1 := by simpa [heps] using hrBound'
          let k := (p - 1) / 2
          have hk1 : 1 ≤ k := by dsimp [k]; omega
          have hkY : k ≤ Y := by dsimp [k, Y]; omega
          have hpEq : p - 1 = 2 * k := by dsimp [k]; omega
          have hkL : k ∣ Nat.lcmUpto Y := hDivL k hk1 hkY
          rw [hpEq] at hr
          exact hr.trans (mul_dvd_mul_left 2 hkL)
        · have hr : fibonacciRank p ∣ p + 1 := by simpa [heps] using hrBound'
          let k := (p + 1) / 2
          have hk1 : 1 ≤ k := by dsimp [k]; omega
          have hkY : k ≤ Y := by dsimp [k, Y]; omega
          have hpEq : p + 1 = 2 * k := by dsimp [k]; omega
          have hkL : k ∣ Nat.lcmUpto Y := hDivL k hk1 hkY
          rw [hpEq] at hr
          exact hr.trans (mul_dvd_mul_left 2 hkL)
      · have hpSmall : p ≤ 5 := by omega
        have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
          have hpTwo := hp.two_le
          have hpNeFour : p ≠ 4 := by
            intro heq
            rw [heq] at hp
            norm_num at hp
          omega
        obtain ⟨k, hk1, hkY, hpFib⟩ :
            ∃ k : ℕ, 1 ≤ k ∧ k ≤ Y ∧ p ∣ Nat.fib k := by
          rcases hpCases with h2 | h3 | h5
          · exact ⟨3, by omega, by omega, by simpa [h2] using
              (show 2 ∣ Nat.fib 3 by decide)⟩
          · exact ⟨4, by omega, by omega, by simpa [h3] using
              (show 3 ∣ Nat.fib 4 by decide)⟩
          · exact ⟨5, by omega, by omega, by simpa [h5] using
              (show 5 ∣ Nat.fib 5 by decide)⟩
        have hkL : k ∣ Nat.lcmUpto Y := hDivL k hk1 hkY
        exact (hEntry k hpFib).trans
          (by simpa [mul_comm] using (dvd_mul_of_dvd_right hkL 2))
    have hRL : H.lcm fibonacciRank ∣ 2 * Nat.lcmUpto Y :=
      Finset.lcm_dvd hRankL
    have hFinal : n ∣ 5 * (2 * Nat.lcmUpto Y) :=
      hBudget.trans (mul_dvd_mul_left 5 hRL)
    simpa only [Y, ← mul_assoc, show 5 * 2 = 10 by decide] using hFinal
  have hUbound (n : ℕ) (hn : 0 < n) (p : ℕ)
      (hp : p.Prime) (hpLarge : 5 < p) (hpFib : p ∣ Nat.fib n)
      (hpIndex : ¬ p ∣ n)
      (hpOdd : Odd (padicValNat p (Nat.fib (fibonacciRank p)))) :
      p ≤ P n := by
    have hpMem : p ∈ U n := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hpLarge, hpIndex, hpOdd⟩
      exact Nat.mem_primeFactors.mpr
        ⟨hp, hpFib, (Nat.fib_pos.mpr hn).ne'⟩
    have hsup : p ≤ (U n).sup id := by
      simpa using (Finset.le_sup (f := id) hpMem)
    exact hsup.trans (le_max_right _ _)
  have hDiv (n : ℕ) (hn : 0 < n) :
      n ∣ 10 * Nat.lcmUpto (Y (P n)) :=
    hUniform (P n) n (le_max_left _ _) hn (hUbound n hn)
  have hLog (n : ℕ) (hn : 0 < n) :
      Real.log (n : ℝ) ≤ Real.log 10 + Chebyshev.psi (Y (P n) : ℝ) := by
    have hpos : 0 < 10 * Nat.lcmUpto (Y (P n)) := by
      exact Nat.mul_pos (by decide) (Nat.lcmUpto_pos _)
    have hle : n ≤ 10 * Nat.lcmUpto (Y (P n)) :=
      Nat.le_of_dvd hpos (hDiv n hn)
    have hleReal : (n : ℝ) ≤
        ((10 * Nat.lcmUpto (Y (P n)) : ℕ) : ℝ) := by exact_mod_cast hle
    calc
      Real.log (n : ℝ) ≤
          Real.log (((10 * Nat.lcmUpto (Y (P n)) : ℕ) : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hn) hleReal
      _ = Real.log 10 + Real.log (Nat.lcmUpto (Y (P n)) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat,
          Real.log_mul (by norm_num : (10 : ℝ) ≠ 0)
            (by exact_mod_cast Nat.lcmUpto_ne_zero (Y (P n)))]
      _ = Real.log 10 + Chebyshev.psi (Y (P n) : ℝ) := by
        rw [Chebyshev.psi_eq_log_lcmUpto]
  have hPTop : Tendsto P atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    let Q := max 5 B
    let M := 10 * Nat.lcmUpto (Y Q)
    filter_upwards [eventually_gt_atTop M] with n hnLarge
    by_contra hnot
    have hPsmall : P n ≤ Q := by
      have : P n < B := by omega
      exact this.le.trans (le_max_right _ _)
    have hn : 0 < n := by omega
    have hndiv : n ∣ M := by
      exact hUniform Q n (le_max_left _ _) hn
        (fun p hp hpLarge hpFib hpIndex hpOdd =>
          (hUbound n hn p hp hpLarge hpFib hpIndex hpOdd).trans hPsmall)
    have hnle : n ≤ M := Nat.le_of_dvd
      (Nat.mul_pos (by decide) (Nat.lcmUpto_pos _)) hndiv
    omega
  have hYTop : Tendsto (fun n : ℕ => Y (P n)) atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [hPTop.eventually_ge_atTop (2 * B)] with n hnP
    have hhalf : B ≤ (P n + 1) / 2 := by omega
    exact hhalf.trans (le_max_right _ _)
  obtain ⟨c, hc, hBig⟩ := MediumPNT
  have hExpZero :
      Tendsto (fun x : ℝ =>
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hNeg : (fun x : ℝ => -c * (Real.log x) ^ ((1 : ℝ) / 10)) =
        (fun x : ℝ => -(c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      funext x
      ring
    rw [hNeg]
    rw [tendsto_neg_atBot_iff]
    exact ((tendsto_rpow_atTop
      (by norm_num : 0 < (1 : ℝ) / 10)).comp
        Real.tendsto_log_atTop).const_mul_atTop hc
  obtain ⟨C, hCpos, hCbound⟩ :=
    (Asymptotics.isBigO_iff').mp hBig
  have hPsiUpper (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + δ) * x := by
    have hExpSmall :
        ∀ᶠ x : ℝ in atTop,
          Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < δ / C :=
      hExpZero.eventually_lt tendsto_const_nhds (div_pos hδ hCpos)
    filter_upwards [hCbound, hExpSmall, eventually_gt_atTop (0 : ℝ)]
      with x hb he hx
    have hExpPos :
        0 < Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) :=
      Real.exp_pos _
    have hDiff :
        Chebyshev.psi x - x ≤
          C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
      have hb' : |Chebyshev.psi x - x| ≤
          C * |x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))| := by
        simpa [Pi.sub_apply, id_eq, Real.norm_eq_abs] using hb
      rw [abs_of_pos (mul_pos hx hExpPos)] at hb'
      exact (le_abs_self _).trans hb'
    have hExpBound :
        C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤ δ := by
      have hh := mul_le_mul_of_nonneg_left (le_of_lt he) hCpos.le
      have hCancel : C * (δ / C) = δ := by
        field_simp [hCpos.ne'] <;> ring
      simpa only [hCancel] using hh
    have hErrBound :
        C * (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) ≤ δ * x := by
      have hh := mul_le_mul_of_nonneg_right hExpBound hx.le
      nlinarith
    nlinarith [hDiff, hErrBound]
  have hGrowth : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, (2 - ε) * Real.log (n : ℝ) ≤ (P n : ℝ) := by
    intro ε hε
    by_cases hε2 : 2 ≤ ε
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      have hPnonneg : 0 ≤ (P n : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : 2 - ε ≤ 0) hlog]
    · have hε2' : ε < 2 := by linarith
      let δ : ℝ := ε / 4
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hPRealTop : Tendsto (fun n : ℕ => (P n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hPTop
      have hYRealTop :
          Tendsto (fun n : ℕ => (Y (P n) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hYTop
      have hPsiEventually :
          ∀ᶠ n : ℕ in atTop,
            Chebyshev.psi (Y (P n) : ℝ) ≤
              (1 + δ) * (Y (P n) : ℝ) :=
        hYRealTop.eventually (hPsiUpper δ hδ)
      let A : ℝ := Real.log 10 + (1 + δ) / 2
      have hεDiv : 0 < ε / 8 := by positivity
      have hPLarge :
          ∀ᶠ n : ℕ in atTop, A / (ε / 8) ≤ (P n : ℝ) :=
        hPRealTop.eventually_ge_atTop _
      filter_upwards [eventually_ge_atTop (1 : ℕ),
        hPTop.eventually_ge_atTop 9, hPsiEventually, hPLarge]
        with n hn hPn hPsi hPLargeN
      have hYeq : Y (P n) = (P n + 1) / 2 := by
        dsimp [Y]
        have : 5 ≤ (P n + 1) / 2 := by omega
        exact max_eq_right this
      have hYle :
          (Y (P n) : ℝ) ≤ ((P n : ℝ) + 1) / 2 := by
        rw [hYeq]
        have hNat : 2 * ((P n + 1) / 2) ≤ P n + 1 := by omega
        have hReal :
            (2 : ℝ) * (((P n + 1) / 2 : ℕ) : ℝ) ≤ (P n : ℝ) + 1 := by
          exact_mod_cast hNat
        nlinarith
      have hAbsorb : A ≤ (ε / 8) * (P n : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hεDiv).mp hPLargeN
      have hLogBound := hLog n (by omega : 0 < n)
      have hCoeff :
          Real.log (n : ℝ) ≤ (1 / 2 + ε / 4) * (P n : ℝ) := by
        have hYmult :
            (1 + δ) * (Y (P n) : ℝ) ≤
              (1 + δ) * (((P n : ℝ) + 1) / 2) :=
          mul_le_mul_of_nonneg_left hYle (by dsimp [δ]; positivity)
        dsimp [A, δ] at hAbsorb ⊢
        dsimp [δ] at hPsi hYmult
        nlinarith [hLogBound, hPsi, hYmult, hAbsorb]
      have hCoeffLE : (2 - ε) * (1 / 2 + ε / 4) ≤ (1 : ℝ) := by
        nlinarith [sq_nonneg ε]
      calc
        (2 - ε) * Real.log (n : ℝ) ≤
            (2 - ε) * ((1 / 2 + ε / 4) * (P n : ℝ)) :=
          mul_le_mul_of_nonneg_left hCoeff (by linarith)
        _ = ((2 - ε) * (1 / 2 + ε / 4)) * (P n : ℝ) := by ring
        _ ≤ (1 : ℝ) * (P n : ℝ) :=
          mul_le_mul_of_nonneg_right hCoeffLE (Nat.cast_nonneg _)
        _ = (P n : ℝ) := one_mul _
  have hLiminf : (2 : ℝ≥0∞) ≤ Filter.liminf
      (fun n : ℕ => ENNReal.ofReal ((P n : ℝ) / Real.log (n : ℝ))) atTop := by
    refine (le_liminf_iff').2 ?_
    intro b hb
    have hbTop : b ≠ ⊤ := ne_of_lt (hb.trans (by norm_num : (2 : ℝ≥0∞) < ⊤))
    have hbReal : b.toReal < 2 := by
      simpa using (ENNReal.toReal_lt_toReal hbTop (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr hb
    have hε : 0 < (2 : ℝ) - b.toReal := sub_pos.mpr hbReal
    filter_upwards [hGrowth (2 - b.toReal) hε,
      eventually_ge_atTop (2 : ℕ)] with n hg hn
    have hnReal : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hLog : 0 < Real.log (n : ℝ) := Real.log_pos hnReal
    have hRatio : b.toReal ≤ (P n : ℝ) / Real.log (n : ℝ) := by
      apply (le_div_iff₀ hLog).mpr
      simpa using hg
    have h := ENNReal.ofReal_le_ofReal hRatio
    simpa [ENNReal.ofReal_toReal hbTop] using h
  refine ⟨hLog, hPTop, hGrowth, hLiminf, ?_⟩
  filter_upwards [hPTop.eventually_ge_atTop 6,
    eventually_ge_atTop (1 : ℕ)] with n hPn hn
  intro hPower
  have hUsup : 5 < (U n).sup id := by
    dsimp [P] at hPn
    omega
  have hUNonempty : (U n).Nonempty := by
    by_contra hEmpty
    have hEmpty' : U n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEmpty
    simp [hEmpty'] at hUsup
  obtain ⟨p, hpU, hpSup⟩ := Finset.exists_mem_eq_sup (U n) hUNonempty id
  simp only [id_eq] at hpSup
  have hpMax : p = P n := by
    dsimp [P]
    rw [max_eq_right hUsup.le]
    exact hpSup.symm
  have hpFilter := Finset.mem_filter.mp hpU
  have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hpFilter.1).1
  have hpFib : p ∣ Nat.fib n := (Nat.mem_primeFactors.mp hpFilter.1).2.1
  have hpLarge : 5 < p := hpFilter.2.1
  have hpIndex : ¬ p ∣ n := hpFilter.2.2.1
  have hpOdd : Odd (padicValNat p (Nat.fib (fibonacciRank p))) :=
    hpFilter.2.2.2
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hFib0 : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr (by omega : 0 < n)).ne'
  have hDepthTwo : 2 ≤ padicValNat p (Nat.fib n) :=
    (padicValNat_dvd_iff_le (p := p) (n := 2) hFib0).mp
      (hPower.2 p hpPrime hpFib)
  have hValEq : padicValNat p (Nat.fib n) =
      padicValNat p (Nat.fib (fibonacciRank p)) :=
    fibonacci_original_rank_valuation p n hpPrime hpFib hpIndex
  have hOddN : Odd (padicValNat p (Nat.fib n)) := by
    rw [hValEq]
    exact hpOdd
  have hDepthThree : 3 ≤ padicValNat p (Nat.fib (fibonacciRank p)) := by
    rw [← hValEq]
    rcases hOddN with ⟨k, hk⟩
    omega
  have hRankPos : 0 < fibonacciRank p := by
    simpa only [fibonacciRank, hpPrime, dite_true] using
      (rankWitness p hpPrime).property.1
  have hWSS : p ^ 2 ∣ Nat.fib (fibonacciRank p) :=
    (padicValNat_dvd_iff_le (p := p) (n := 2)
      (Nat.fib_pos.mpr hRankPos).ne').mpr (by omega)
  exact ⟨p, hpMax, hpPrime, hpLarge, hpFib, hpIndex, hpOdd,
    hDepthThree, hWSS⟩


end D5.S3.Arith.Primes.FibonacciExternalWitnessGrowth

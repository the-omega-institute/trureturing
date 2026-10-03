/- GID: D5/S3/Arith/Primes/GoldenLargestPrimePeriodIteration
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenLargestPrimePeriodIteration
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Largest-prime depth decreases exactly under arbitrary positive-modulus period iteration. -/

import D5.S3.Arith.GoldenPrimePowerOrder
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition
open D5.S3.Arith.GoldenFibonacciModulusPeriod
open D5.S3.Arith.GoldenPrimePowerOrder

namespace D5.S3.Arith.Primes.GoldenLargestPrimePeriodIteration

/-- Exact loss of the largest prime's original Fibonacci depth along every period iterate. -/
theorem golden_largest_prime_period_iteration :
    let period := fun m : ℕ =>
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    let depth := fun P : ℕ =>
      padicValNat P (Nat.fib
        (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank P))
    (∀ (m P : ℕ), 0 < m → P.Prime → 5 < P → P ∈ m.primeFactors →
      (∀ q ∈ m.primeFactors, q ≤ P) →
      let a := m.factorization P
      (∀ n : ℕ, (period^[n] m).factorization P = a - n * depth P) ∧
      (∀ n : ℕ, P ∣ period^[n] m ↔ n < (a + depth P - 1) / depth P)) ∧
    (∀ m : ℕ, 0 < m → period m = m →
      ∀ P ∈ m.primeFactors, P ≤ 5) ∧
    (∀ (m P : ℕ), 0 < m → P.Prime → 5 < P → P ∈ m.primeFactors →
      (∀ q ∈ m.primeFactors, q ≤ P) →
      period (m ^ 2) = period m →
      2 * m.factorization P ≤ depth P) := by
  have hMatrixOrder (m : ℕ) :
      orderOf (GoldenMod.phi : GoldenMod m) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) := by
    have hinj : Function.Injective (goldenMatrixHom m) := by
      intro x y h
      apply GoldenMod.ext
      · have h11 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 1 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h11
      · have h01 := congrArg
          (fun M : Matrix (Fin 2) (Fin 2) (ZMod m) => M 0 1) h
        simpa [goldenMatrixHom, multiplicationMatrix] using h01
    have hphi : goldenMatrixHom m (GoldenMod.phi : GoldenMod m) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    have horder := orderOf_injective (goldenMatrixHom m).toMonoidHom
      hinj (GoldenMod.phi : GoldenMod m)
    change orderOf (goldenMatrixHom m (GoldenMod.phi : GoldenMod m)) = _ at horder
    rw [hphi] at horder
    exact horder.symm
  classical
  let period := fun m : ℕ =>
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
  have period_divides_lifted_base
      (p m t n : ℕ) (a b : ℤ)
      (hp : p.Prime) (hm : 0 < m) (hpm : m + 2 ≤ p * m)
      (hab : ¬ (p : ℤ) ∣ a ∨ ¬ (p : ℤ) ∣ b)
      (hBase : phi ^ t = 1 + (p ^ m : GoldenInt) * (⟨a, b⟩ : GoldenInt)) :
      period (p ^ (n + m)) ∣ t * p ^ n := by
    let x : GoldenMod (p ^ (n + m)) := GoldenMod.phi
    have hPow : x ^ t = 1 + (p ^ m : GoldenMod (p ^ (n + m))) *
        (⟨(a : ZMod (p ^ (n + m))), (b : ZMod (p ^ (n + m)))⟩ :
          GoldenMod (p ^ (n + m))) := by
      have h := congrArg (GoldenMod.reduce (p ^ (n + m))) hBase
      simp only [map_pow, map_one, map_add, map_mul, map_natCast] at h
      have hphi : GoldenMod.reduce (p ^ (n + m)) phi =
          (GoldenMod.phi : GoldenMod (p ^ (n + m))) := by
        apply GoldenMod.ext <;>
          norm_num [GoldenMod.reduce, phi, GoldenMod.phi]
      have hr : GoldenMod.reduce (p ^ (n + m)) (⟨a, b⟩ : GoldenInt) =
          (⟨(a : ZMod (p ^ (n + m))), (b : ZMod (p ^ (n + m)))⟩ :
            GoldenMod (p ^ (n + m))) := rfl
      simpa only [x, hphi, hr] using h
    have hOrderPow : orderOf (x ^ t) = p ^ n := by
      rw [hPow]
      exact golden_prime_power_order hp hm hpm a b hab
    have hReturn : x ^ (t * p ^ n) = 1 := by
      rw [pow_mul, ← hOrderPow]
      exact pow_orderOf_eq_one _
    change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
      (ZMod (p ^ (n + m)))) ∣ t * p ^ n
    rw [← hMatrixOrder (p ^ (n + m))]
    exact orderOf_dvd_of_pow_eq_one hReturn

  have period_two_power_bound (n : ℕ) :
      period (2 ^ (n + 2)) ∣ 6 * 2 ^ n := by
    have hFib5 : Nat.fib 5 = 5 := by decide
    have hFib6 : Nat.fib 6 = 8 := by decide
    have hBase : phi ^ 6 =
        1 + (2 ^ 2 : GoldenInt) * (⟨1, 2⟩ : GoldenInt) := by
      calc
        phi ^ 6 = (⟨5, 8⟩ : GoldenInt) := by
          simpa [hFib5, hFib6] using golden_phi_pow_eq_fib_pair 5
        _ = 1 + (2 ^ 2 : GoldenInt) * (⟨1, 2⟩ : GoldenInt) := by
          decide
    exact period_divides_lifted_base 2 2 6 n 1 2
      (by decide) (by decide) (by decide) (Or.inl (by decide)) hBase

  have period_three_power_bound (n : ℕ) :
      period (3 ^ (n + 1)) ∣ 8 * 3 ^ n := by
    have hFib7 : Nat.fib 7 = 13 := by decide
    have hFib8 : Nat.fib 8 = 21 := by decide
    have hBase : phi ^ 8 =
        1 + (3 : GoldenInt) * (⟨4, 7⟩ : GoldenInt) := by
      calc
        phi ^ 8 = (⟨13, 21⟩ : GoldenInt) := by
          simpa [hFib7, hFib8] using golden_phi_pow_eq_fib_pair 7
        _ = 1 + (3 : GoldenInt) * (⟨4, 7⟩ : GoldenInt) := by
          decide
    exact period_divides_lifted_base 3 1 8 n 4 7
      (by decide) (by decide) (by decide) (Or.inl (by decide)) (by simpa using hBase)

  have period_five_power_bound (n : ℕ) :
      period (5 ^ (n + 1)) ∣ 20 * 5 ^ n := by
    have hFib19 : Nat.fib 19 = 4181 := by decide
    have hFib20 : Nat.fib 20 = 6765 := by decide
    have hBase : phi ^ 20 =
        1 + (5 : GoldenInt) * (⟨836, 1353⟩ : GoldenInt) := by
      calc
        phi ^ 20 = (⟨4181, 6765⟩ : GoldenInt) := by
          simpa [hFib19, hFib20] using golden_phi_pow_eq_fib_pair 19
        _ = 1 + (5 : GoldenInt) * (⟨836, 1353⟩ : GoldenInt) := by
          decide
    exact period_divides_lifted_base 5 1 20 n 836 1353
      (by decide) (by decide) (by decide) (Or.inr (by decide)) (by simpa using hBase)

  have small_prime_power_has_no_large_factor
      (q a P : ℕ) (hq : q.Prime) (hqSmall : q ≤ 5) (ha : 0 < a)
      (hP : P.Prime) (hPBig : 5 < P) : ¬ P ∣ period (q ^ a) := by
    have hCases : q = 2 ∨ q = 3 ∨ q = 5 := by
      interval_cases q <;> norm_num at hq
      all_goals norm_num
    have hNoPow (r k : ℕ) (hrPos : 0 < r) (hr : r ≤ 5) : ¬ P ∣ r ^ k := by
      intro hd
      have hdr : P ∣ r := hP.dvd_of_dvd_pow hd
      exact (not_le_of_gt hPBig) ((Nat.le_of_dvd hrPos hdr).trans hr)
    have hNoSix : ¬ P ∣ 6 := by
      intro hd
      have hle : P ≤ 6 := Nat.le_of_dvd (by decide) hd
      have heq : P = 6 := by omega
      subst P
      norm_num at hP
    have hNoEight : ¬ P ∣ 8 := by
      intro hd
      have hpow : P ∣ 2 ^ 3 := by simpa using hd
      exact hNoPow 2 3 (by decide) (by decide) hpow
    have hNoTwenty : ¬ P ∣ 20 := by
      intro hd
      have hprod : P ∣ 4 * 5 := by simpa using hd
      rcases hP.dvd_mul.mp hprod with h4 | h5
      · have hpow : P ∣ 2 ^ 2 := by simpa using h4
        exact hNoPow 2 2 (by decide) (by decide) hpow
      · exact (not_le_of_gt hPBig)
          ((Nat.le_of_dvd (by decide : 0 < 5) h5).trans (by decide))
    rcases hCases with rfl | rfl | rfl
    · by_cases haOne : a = 1
      · subst a
        have hTwo : period 2 = 3 := by
          change orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 3
          rw [orderOf_eq_iff (by decide)]
          refine ⟨by decide, ?_⟩
          intro n hn hpos
          interval_cases n
          all_goals decide
        simpa [hTwo] using hNoPow 3 1 (by decide) (by decide)
      · have haTwo : 2 ≤ a := by omega
        have haEq : a - 2 + 2 = a := by omega
        intro hd
        have hbound := period_two_power_bound (a - 2)
        rw [haEq] at hbound
        have hprod : P ∣ 6 * 2 ^ (a - 2) := hd.trans hbound
        rcases hP.dvd_mul.mp hprod with h6 | h2
        · exact hNoSix h6
        · exact hNoPow 2 (a - 2) (by decide) (by decide) h2
    · have haEq : a - 1 + 1 = a := by omega
      intro hd
      have hbound := period_three_power_bound (a - 1)
      rw [haEq] at hbound
      have hprod : P ∣ 8 * 3 ^ (a - 1) := hd.trans hbound
      rcases hP.dvd_mul.mp hprod with h8 | h3
      · exact hNoEight h8
      · exact hNoPow 3 (a - 1) (by decide) (by decide) h3
    · have haEq : a - 1 + 1 = a := by omega
      intro hd
      have hbound := period_five_power_bound (a - 1)
      rw [haEq] at hbound
      have hprod : P ∣ 20 * 5 ^ (a - 1) := hd.trans hbound
      rcases hP.dvd_mul.mp hprod with h20 | h5
      · exact hNoTwenty h20
      · exact hNoPow 5 (a - 1) (by decide) (by decide) h5

  have period_crt (m : ℕ) (hm : m ≠ 0) :
      period m = m.primeFactors.lcm
        (fun p => period (p ^ m.factorization p)) := by
    have hSubtypeLcm (S : Finset ℕ) (f : ℕ → ℕ) :
        (Finset.univ : Finset S).lcm (fun p => f p) = S.lcm f := by
      symm
      calc
        S.lcm f = (Finset.image (fun p : S => (p : ℕ)) Finset.univ).lcm f := by
          congr 1
          ext p
          simp
        _ = (Finset.univ : Finset S).lcm (f ∘ fun p : S => (p : ℕ)) :=
          Finset.lcm_image _
        _ = (Finset.univ : Finset S).lcm (fun p => f p) := rfl
    let E : Matrix (Fin 2) (Fin 2) (ZMod m) ≃+*
        (∀ p : m.primeFactors,
          Matrix (Fin 2) (Fin 2) (ZMod ((p : ℕ) ^ m.factorization p))) :=
      ((ZMod.equivPi m hm).mapMatrix).trans Matrix.piRingEquiv
    let Qm : Matrix (Fin 2) (Fin 2) (ZMod m) := !![1, 1; 1, 0]
    have hQ (p : m.primeFactors) : E Qm p =
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2)
          (ZMod ((p : ℕ) ^ m.factorization p))) := by
      ext i j
      fin_cases i <;> fin_cases j
      · change (ZMod.equivPi m hm (1 : ZMod m)) p = 1
        exact congrFun (map_one (ZMod.equivPi m hm)) p
      · change (ZMod.equivPi m hm (1 : ZMod m)) p = 1
        exact congrFun (map_one (ZMod.equivPi m hm)) p
      · change (ZMod.equivPi m hm (1 : ZMod m)) p = 1
        exact congrFun (map_one (ZMod.equivPi m hm)) p
      · change (ZMod.equivPi m hm (0 : ZMod m)) p = 0
        exact congrFun (map_zero (ZMod.equivPi m hm)) p
    change orderOf Qm = _
    calc
      orderOf Qm = orderOf (E Qm) := (E.toMulEquiv.orderOf_eq Qm).symm
      _ = (Finset.univ : Finset m.primeFactors).lcm
          (fun p => orderOf (E Qm p)) := Pi.orderOf (E Qm)
      _ = (Finset.univ : Finset m.primeFactors).lcm
          (fun p => period ((p : ℕ) ^ m.factorization p)) := by
            apply Finset.lcm_congr rfl
            intro p hp
            exact congrArg orderOf (hQ p)
      _ = m.primeFactors.lcm (fun p => period (p ^ m.factorization p)) :=
        hSubtypeLcm m.primeFactors (fun p => period (p ^ m.factorization p))

  have period_pos (m : ℕ) (hm : 0 < m) : 0 < period m := by
    letI : NeZero m := ⟨hm.ne'⟩
    let Q : Matrix (Fin 2) (Fin 2) (ZMod m) := !![1, 1; 1, 0]
    have hDet : Q.det = (-1 : ZMod m) := by
      simp [Q, Matrix.det_fin_two]
    have hUnit : IsUnit Q := by
      rw [Matrix.isUnit_iff_isUnit_det, hDet]
      exact isUnit_neg_one
    exact hUnit.isOfFinOrder.orderOf_pos

  have period_step_bounded_max
      (m P : ℕ) (hm : 0 < m) (hP : P.Prime) (hPBig : 5 < P)
      (hMax : ∀ q ∈ m.primeFactors, q ≤ P) :
      (∀ r ∈ (period m).primeFactors, r ≤ P) ∧
        (period m).factorization P = m.factorization P -
          padicValNat P (Nat.fib
            (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank P)) := by
    classical
    let depth := fun p : ℕ =>
      padicValNat p (Nat.fib
        (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))
    have hBound (q : ℕ) (hq : q.Prime) (hq5 : 5 < q) :
        (period q ∣ q - 1 ∧ ¬ q ∣ period q) ∨
        (period q ∣ 2 * (q + 1) ∧ ¬ q ∣ period q) := by
      letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      have hq5ne : (q : ZMod 5) ≠ 0 := by
        intro hz
        have hd : 5 ∣ q := (ZMod.natCast_eq_zero_iff q 5).mp hz
        have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hq).mp hd
        omega
      have hqNotDvdFive : ¬ q ∣ 5 := by
        intro h
        have hle := Nat.le_of_dvd (by decide : 0 < 5) h
        omega
      have hentry := fibonacci_apparition_entry_point hq hqNotDvdFive
      have hfp : ((Nat.fib q : ℕ) : ZMod q) = (legendreSym 5 q : ZMod q) := by
        simpa only [Int.fib_natCast, Int.cast_natCast] using hentry.2
      have hpair (n : ℕ) :
          (GoldenMod.phi : GoldenMod q) ^ (n + 1) =
            ⟨(Nat.fib n : ZMod q), (Nat.fib (n + 1) : ZMod q)⟩ := by
        have h := congrArg (GoldenMod.reduce q) (golden_phi_pow_eq_fib_pair n)
        have hr : GoldenMod.reduce q
            (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) =
            ⟨(Nat.fib n : ZMod q), (Nat.fib (n + 1) : ZMod q)⟩ := by
          apply GoldenMod.ext
          · change (((Nat.fib n : ℕ) : ℤ) : ZMod q) = (Nat.fib n : ZMod q)
            rw [Int.cast_natCast]
          · change (((Nat.fib (n + 1) : ℕ) : ℤ) : ZMod q) =
              (Nat.fib (n + 1) : ZMod q)
            rw [Int.cast_natCast]
        have hphi : GoldenMod.reduce q D5.S0.Carrier.phi = GoldenMod.phi := by
          apply GoldenMod.ext <;>
            norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
        simpa only [map_pow, hphi, hr] using h
      rcases legendreSym.eq_one_or_neg_one (p := 5) (a := (q : ℤ)) hq5ne with hs | hi
      · have hfprev : ((Nat.fib (q - 1) : ℕ) : ZMod q) = 0 := by
          have h := hentry.1
          rw [hs] at h
          have hindex : (q : ℤ) - 1 = ((q - 1 : ℕ) : ℤ) := by omega
          rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
          exact h
        have hfcurrent : ((Nat.fib q : ℕ) : ZMod q) = 1 := by
          simpa [hs] using hfp
        have hpow : (GoldenMod.phi : GoldenMod q) ^ q = GoldenMod.phi := by
          have h := hpair (q - 1)
          have hindex : q - 1 + 1 = q := by omega
          rw [hindex] at h
          apply GoldenMod.ext
          · simpa [GoldenMod.phi] using (congrArg GoldenMod.a h).trans hfprev
          · simpa [GoldenMod.phi] using (congrArg GoldenMod.b h).trans hfcurrent
        have hinv : (GoldenMod.phi : GoldenMod q) * (GoldenMod.phi - 1) = 1 := by
          apply GoldenMod.ext <;>
            simp [GoldenMod.phi, sub_eq_add_neg]
        have hreturn : (GoldenMod.phi : GoldenMod q) ^ (q - 1) = 1 := by
          have hindex : q - 1 + 1 = q := by omega
          calc
            (GoldenMod.phi : GoldenMod q) ^ (q - 1) =
                (GoldenMod.phi : GoldenMod q) ^ (q - 1) *
                  (GoldenMod.phi * (GoldenMod.phi - 1)) := by rw [hinv, mul_one]
            _ = (GoldenMod.phi : GoldenMod q) ^ q *
                  (GoldenMod.phi - 1) := by
                rw [← mul_assoc, ← pow_succ, hindex]
            _ = 1 := by rw [hpow, hinv]
        have hdiv : period q ∣ q - 1 := by
          change orderOf (!![1, 1; 1, 0] :
            Matrix (Fin 2) (Fin 2) (ZMod q)) ∣ q - 1
          rw [← hMatrixOrder q]
          exact orderOf_dvd_of_pow_eq_one hreturn
        refine Or.inl ⟨hdiv, ?_⟩
        intro hqdvd
        have hbad : q ∣ q - 1 := dvd_trans hqdvd hdiv
        have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hbad
        omega
      · have hfnext : ((Nat.fib (q + 1) : ℕ) : ZMod q) = 0 := by
          have h := hentry.1
          rw [hi] at h
          have hindex : (q : ℤ) - -1 = ((q + 1 : ℕ) : ℤ) := by omega
          rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
          exact h
        have hfcurrent : ((Nat.fib q : ℕ) : ZMod q) = -1 := by
          simpa [hi] using hfp
        have hpow : (GoldenMod.phi : GoldenMod q) ^ (q + 1) = -1 := by
          have h := hpair q
          apply GoldenMod.ext
          · simpa using (congrArg GoldenMod.a h).trans hfcurrent
          · simpa using (congrArg GoldenMod.b h).trans hfnext
        have hreturn : (GoldenMod.phi : GoldenMod q) ^ (2 * (q + 1)) = 1 := by
          calc
            (GoldenMod.phi : GoldenMod q) ^ (2 * (q + 1)) =
                ((GoldenMod.phi : GoldenMod q) ^ (q + 1)) ^ 2 := by
                  rw [Nat.mul_comm 2 (q + 1), pow_mul]
            _ = 1 := by rw [hpow]; norm_num
        have hdiv : period q ∣ 2 * (q + 1) := by
          change orderOf (!![1, 1; 1, 0] :
            Matrix (Fin 2) (Fin 2) (ZMod q)) ∣ 2 * (q + 1)
          rw [← hMatrixOrder q]
          exact orderOf_dvd_of_pow_eq_one hreturn
        refine Or.inr ⟨hdiv, ?_⟩
        intro hqdvd
        have hbad : q ∣ 2 * (q + 1) := dvd_trans hqdvd hdiv
        rcases hq.dvd_mul.mp hbad with htwo | hnext
        · have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
          omega
        · have hone : q ∣ 1 := (Nat.dvd_add_self_left).mp hnext
          have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
          omega
    have hEdge (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hq5 : 5 < q)
        (hpq : p ∣ period q) : p < q := by
      rcases hBound q hq hq5 with hsplit | hinert
      · have hsmall : p ∣ q - 1 := hpq.trans hsplit.1
        exact lt_of_le_of_lt (Nat.le_of_dvd (by omega) hsmall) (by omega)
      · have hdiv : p ∣ 2 * (q + 1) := hpq.trans hinert.1
        by_cases hp2 : p = 2
        · omega
        have hpOdd : Odd p := hp.odd_of_ne_two hp2
        have hqOdd : Odd q := hq.odd_of_ne_two (by omega)
        have hpNotTwo : ¬ p ∣ 2 := by
          intro hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
        have hdivSucc : p ∣ q + 1 :=
          (hp.dvd_mul.mp hdiv).resolve_left hpNotTwo
        obtain ⟨k, hk⟩ := hdivSucc
        have hkPos : 0 < k := by
          by_contra h
          have hz : k = 0 := by omega
          rw [hz] at hk
          omega
        have hkTwo : 2 ≤ k := by
          by_contra h
          have hkOne : k = 1 := by omega
          rcases hpOdd with ⟨u, hu⟩
          rcases hqOdd with ⟨v, hv⟩
          rw [hkOne] at hk
          omega
        have hk' : q + 1 = k * p := by simpa [Nat.mul_comm] using hk
        have hmul : 2 * p ≤ k * p := Nat.mul_le_mul_right p hkTwo
        omega
    have hLocalLarge (q : ℕ) (hq : q ∈ m.primeFactors) (hq5 : 5 < q) :
        period (q ^ m.factorization q) =
          period q * q ^ (m.factorization q - depth q) := by
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have ha : 0 < m.factorization q :=
        hqPrime.factorization_pos_of_dvd hm.ne'
          (Nat.dvd_of_mem_primeFactors hq)
      exact (D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period
        q (m.factorization q) hqPrime hq5 ha).2.2.2.2.2.2.2.2.2
    have hNoLocal (q : ℕ) (hq : q ∈ m.primeFactors)
        (r : ℕ) (hr : r.Prime) (hr5 : 5 < r) (hqr : q < r) :
        ¬ r ∣ period (q ^ m.factorization q) := by
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have ha : 0 < m.factorization q :=
        hqPrime.factorization_pos_of_dvd hm.ne'
          (Nat.dvd_of_mem_primeFactors hq)
      by_cases hqSmall : q ≤ 5
      · exact small_prime_power_has_no_large_factor q _ r hqPrime hqSmall ha hr hr5
      · have hq5 : 5 < q := by omega
        rw [hLocalLarge q hq hq5]
        intro hd
        rcases hr.dvd_mul.mp hd with hTau | hPow
        · exact (not_lt_of_ge (le_of_lt hqr))
            (hEdge r q hr hqPrime hq5 hTau)
        · have hrq : r ∣ q := hr.dvd_of_dvd_pow hPow
          have heq : r = q := (Nat.prime_dvd_prime_iff_eq hr hqPrime).mp hrq
          omega
    have hNoPeriod (r : ℕ) (hr : r.Prime) (hr5 : 5 < r)
        (hAll : ∀ q ∈ m.primeFactors, q < r) : ¬ r ∣ period m := by
      rw [period_crt m hm.ne']
      intro hd
      have hProd : r ∣ ∏ q ∈ m.primeFactors,
          period (q ^ m.factorization q) :=
        hd.trans (Finset.lcm_dvd_prod m.primeFactors
          (fun q => period (q ^ m.factorization q)))
      obtain ⟨q, hq, hqDvd⟩ :=
        (hr.prime.dvd_finsetProd_iff
          (fun q => period (q ^ m.factorization q))).mp hProd
      exact hNoLocal q hq r hr hr5 (hAll q hq) hqDvd
    have hSupport : ∀ r ∈ (period m).primeFactors, r ≤ P := by
      intro r hr
      by_contra hle
      have hrPrime : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrBig : P < r := by omega
      have hAll : ∀ q ∈ m.primeFactors, q < r := by
        intro q hq
        exact lt_of_le_of_lt (hMax q hq) hrBig
      exact (hNoPeriod r hrPrime (by omega) hAll)
        (Nat.dvd_of_mem_primeFactors hr)
    refine ⟨hSupport, ?_⟩
    by_cases hPmem : P ∈ m.primeFactors
    · have hSelf : ¬ P ∣ period P :=
        (hBound P hP hPBig).elim (fun h => h.2) (fun h => h.2)
      have hAtP : (period (P ^ m.factorization P)).factorization P =
          m.factorization P - depth P := by
        rw [hLocalLarge P hPmem hPBig]
        have hPowNe : P ^ (m.factorization P - depth P) ≠ 0 :=
          pow_ne_zero _ hP.ne_zero
        rw [Nat.factorization_mul (period_pos P hP.pos).ne' hPowNe]
        simp [Nat.factorization_eq_zero_of_not_dvd hSelf, hP.factorization_self]
      rw [period_crt m hm.ne']
      rw [Finset.factorization_lcm
        (fun q hq => (period_pos (q ^ m.factorization q)
          (pow_pos (Nat.prime_of_mem_primeFactors hq).pos _)).ne') P]
      apply le_antisymm
      · apply Finset.sup_le
        intro q hq
        by_cases hEq : q = P
        · subst q
          exact le_of_eq hAtP
        · have hqLt : q < P := by have := hMax q hq; omega
          have hZero : (period (q ^ m.factorization q)).factorization P = 0 :=
            Nat.factorization_eq_zero_of_not_dvd
              (hNoLocal q hq P hP hPBig hqLt)
          rw [hZero]
          omega
      · calc
          m.factorization P - depth P =
              (period (P ^ m.factorization P)).factorization P := hAtP.symm
          _ ≤ m.primeFactors.sup
            (fun q => (period (q ^ m.factorization q)).factorization P) :=
            Finset.le_sup (f := fun q =>
              (period (q ^ m.factorization q)).factorization P) hPmem
    · have hNoP : ¬ P ∣ m := by
        intro hd
        exact hPmem (Nat.mem_primeFactors.mpr ⟨hP, hd, hm.ne'⟩)
      have hMZero : m.factorization P = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hNoP
      have hAll : ∀ q ∈ m.primeFactors, q < P := by
        intro q hq
        have := hMax q hq
        have hne : q ≠ P := by
          intro heq
          exact hPmem (heq ▸ hq)
        omega
      have hPeriodZero : (period m).factorization P = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (hNoPeriod P hP hPBig hAll)
      rw [hPeriodZero, hMZero]
      simp
  let depth := fun P : ℕ =>
    padicValNat P (Nat.fib
      (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank P))
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro m P hm hP hPBig hPmem hMax
    have hDepth : 0 < depth P :=
      (D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period
        P 1 hP hPBig (by decide)).1
    have hApos : 0 < m.factorization P :=
      hP.factorization_pos_of_dvd hm.ne'
        (Nat.dvd_of_mem_primeFactors hPmem)
    have hIter (n : ℕ) :
        0 < period^[n] m ∧
        (∀ q ∈ (period^[n] m).primeFactors, q ≤ P) ∧
        (period^[n] m).factorization P =
          m.factorization P - n * depth P := by
      induction n with
      | zero => exact ⟨hm, hMax, by simp⟩
      | succ n ih =>
          have hStep := period_step_bounded_max
            (period^[n] m) P ih.1 hP hPBig ih.2.1
          refine ⟨?_, ?_, ?_⟩
          · simpa [Function.iterate_succ_apply'] using period_pos (period^[n] m) ih.1
          · simpa [Function.iterate_succ_apply'] using hStep.1
          · rw [Function.iterate_succ_apply', hStep.2, ih.2.2]
            change m.factorization P - n * depth P - depth P =
              m.factorization P - (n + 1) * depth P
            simp [Nat.add_mul, Nat.sub_sub]
    constructor
    · intro n
      exact (hIter n).2.2
    · intro n
      have hCeil : m.factorization P ⌈/⌉ depth P =
          (m.factorization P + depth P - 1) / depth P :=
        Nat.ceilDiv_eq_add_pred_div _ _
      have hDvd : P ∣ period^[n] m ↔
          0 < (period^[n] m).factorization P := by
        have hiff := hP.dvd_iff_one_le_factorization (hIter n).1.ne'
        exact hiff.trans (by omega)
      rw [hDvd, (hIter n).2.2, ← hCeil]
      constructor
      · intro hpos
        have hlt : n * depth P < m.factorization P := by omega
        by_contra hnot
        have hceilLe : m.factorization P ⌈/⌉ depth P ≤ n := by omega
        have hmulLe := (ceilDiv_le_iff_le_mul hDepth).mp hceilLe
        rw [Nat.mul_comm] at hmulLe
        omega
      · intro hlt
        have hnot : ¬ m.factorization P ≤ depth P * n := by
          intro hle
          have hceilLe : m.factorization P ⌈/⌉ depth P ≤ n :=
            (ceilDiv_le_iff_le_mul hDepth).2 hle
          omega
        have hmul : n * depth P < m.factorization P := by
          rw [Nat.mul_comm] at hnot
          omega
        omega
  · intro m hm hFix P hPmem
    change period m = m at hFix
    by_contra hPsmall
    have hPBig : 5 < P := by omega
    let S := m.primeFactors
    have hS : S.Nonempty := ⟨P, hPmem⟩
    let Q := S.max' hS
    have hQmem : Q ∈ m.primeFactors := Finset.max'_mem S hS
    have hQprime : Q.Prime := Nat.prime_of_mem_primeFactors hQmem
    have hQBig : 5 < Q := by
      have hPLe : P ≤ Q := Finset.le_max' S P hPmem
      omega
    have hQmax : ∀ q ∈ m.primeFactors, q ≤ Q := by
      intro q hq
      exact Finset.le_max' S q hq
    have hDepth : 0 < padicValNat Q (Nat.fib
        (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank Q)) :=
      (D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod.golden_matrix_prime_power_period
        Q 1 hQprime hQBig (by decide)).1
    have hQfac : 0 < m.factorization Q :=
      hQprime.factorization_pos_of_dvd hm.ne'
        (Nat.dvd_of_mem_primeFactors hQmem)
    have hStep := (period_step_bounded_max m Q hm hQprime hQBig hQmax).2
    rw [hFix] at hStep
    omega
  · intro m P hm hP hPBig hPmem hMax hSquare
    change period (m ^ 2) = period m at hSquare
    have hM2pos : 0 < m ^ 2 := pow_pos hm _
    have hM2max : ∀ q ∈ (m ^ 2).primeFactors, q ≤ P := by
      intro q hq
      exact hMax q (by simpa [Nat.primeFactors_pow m (by decide : (2 : ℕ) ≠ 0)] using hq)
    have hM2fac : (m ^ 2).factorization P = 2 * m.factorization P := by
      rw [Nat.factorization_pow]
      simp
    have hOne := (period_step_bounded_max m P hm hP hPBig hMax).2
    have hTwo := (period_step_bounded_max (m ^ 2) P hM2pos hP hPBig hM2max).2
    rw [hSquare, hM2fac] at hTwo
    have hApos : 0 < m.factorization P :=
      hP.factorization_pos_of_dvd hm.ne'
        (Nat.dvd_of_mem_primeFactors hPmem)
    omega

end D5.S3.Arith.Primes.GoldenLargestPrimePeriodIteration

/- GID: D5/S3/Arith/Primes/GoldenFiniteSupportStrideMasking
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenFiniteSupportStrideMasking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coupling and stride valuations determine finite-support matrix periods. -/

import D5.S3.Arith.Primes.GoldenFiniteSupportSquarePeriod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix
open D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
open D5.S3.Arith.Primes.GoldenFiniteSupportSquarePeriod

namespace D5.S3.Arith.Primes.GoldenFiniteSupportStrideMasking

/-- Exact finite-support stride period and first contributing exponent. -/
theorem golden_finite_support_stride_masking
    (S : Finset ℕ) (hS : S.Nonempty)
    (hPrime : ∀ p ∈ S, p.Prime) (hLarge : ∀ p ∈ S, 5 < p)
    (a : ℕ → ℕ) (ha : ∀ p ∈ S, 1 ≤ a p)
    (s : ℕ) (hs : 1 ≤ s) :
    let period := fun m : ℕ =>
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    let stridePeriod := fun s m : ℕ =>
      orderOf ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) ^ s)
    let M0 := ∏ p ∈ S, p
    let M := ∏ p ∈ S, p ^ a p
    let T := S.lcm period
    let depth := fun p : ℕ =>
      padicValNat p (Nat.fib
        (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))
    stridePeriod s M = (T / Nat.gcd T s) *
      ∏ p ∈ S, p ^ ((a p - depth p) -
        max (T.factorization p) (s.factorization p)) ∧
    (∀ p ∈ S, ∀ e : ℕ, 1 ≤ e →
      let m_e := ∏ q ∈ S, q ^ (if q = p then e else 1)
      stridePeriod s m_e = stridePeriod s M0 *
        p ^ (e - (depth p + max (T.factorization p) (s.factorization p))) ∧
      (stridePeriod s M0 < stridePeriod s m_e ↔
        depth p + max (T.factorization p) (s.factorization p) < e)) := by
  classical
  let period := fun m : ℕ =>
    orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
  let stridePeriod := fun s m : ℕ =>
    orderOf ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) ^ s)
  have finite_lcm_stride_masking
      (S : Finset ℕ) (hPrime : ∀ p ∈ S, p.Prime)
      (tau e : ℕ → ℕ) (hTauPos : ∀ p ∈ S, 0 < tau p)
      (hSelf : ∀ p ∈ S, ¬ p ∣ tau p)
      (s : ℕ) (hs : 0 < s) :
      let T := S.lcm tau
      let L := S.lcm (fun p => tau p * p ^ e p)
      L / Nat.gcd L s =
        (T / Nat.gcd T s) *
          ∏ p ∈ S, p ^ (e p - max (T.factorization p) (s.factorization p)) := by
    classical
    let T := S.lcm tau
    let L := S.lcm (fun p => tau p * p ^ e p)
    let R := ∏ p ∈ S, p ^ (e p - max (T.factorization p) (s.factorization p))
    have hTpos : 0 < T := by
      apply Nat.pos_of_ne_zero
      apply Finset.lcm_ne_zero_iff.mpr
      intro p hp
      exact (hTauPos p hp).ne'
    have hLpos : 0 < L := by
      apply Nat.pos_of_ne_zero
      apply Finset.lcm_ne_zero_iff.mpr
      intro p hp
      exact (mul_pos (hTauPos p hp) (pow_pos (hPrime p hp).pos _)).ne'
    have hRpos : 0 < R := by
      dsimp [R]
      apply Finset.prod_pos
      intro p hp
      exact pow_pos (hPrime p hp).pos _
    have hLocalVal (q r : ℕ) (hq : q ∈ S) :
        (tau q * q ^ e q).factorization r =
          (tau q).factorization r + if q = r then e q else 0 := by
      rw [Nat.factorization_mul (hTauPos q hq).ne'
        (pow_pos (hPrime q hq).pos _).ne', Finsupp.add_apply]
      rw [(hPrime q hq).factorization_pow]
      simp [Finsupp.single_apply]
    have hTVal (r : ℕ) :
        T.factorization r = S.sup (fun q => (tau q).factorization r) := by
      exact Finset.factorization_lcm (fun q hq => (hTauPos q hq).ne') r
    have hTdvdL : T ∣ L := by
      apply Finset.lcm_dvd
      intro q hq
      exact (dvd_mul_right (tau q) (q ^ e q)).trans (Finset.dvd_lcm hq)
    have hLVal (r : ℕ) :
        L.factorization r = max (T.factorization r) (if r ∈ S then e r else 0) := by
      apply le_antisymm
      · rw [Finset.factorization_lcm (fun q hq =>
          (mul_pos (hTauPos q hq) (pow_pos (hPrime q hq).pos _)).ne') r]
        apply Finset.sup_le
        intro q hq
        have hTauLe : (tau q).factorization r ≤ T.factorization r := by
          rw [hTVal r]
          exact Finset.le_sup (s := S) (f := fun x => (tau x).factorization r) hq
        rw [hLocalVal q r hq]
        by_cases hqr : q = r
        · subst q
          have hZero : (tau r).factorization r = 0 :=
            Nat.factorization_eq_zero_of_not_dvd (hSelf r hq)
          simpa [hZero, hq] using (le_max_right (T.factorization r) (e r))
        · simp only [if_neg hqr, add_zero]
          exact hTauLe.trans (le_max_left _ _)
      · have hBetaLe : T.factorization r ≤ L.factorization r :=
          ((Nat.factorization_le_iff_dvd hTpos.ne' hLpos.ne').mpr hTdvdL) r
        apply max_le hBetaLe
        by_cases hr : r ∈ S
        · have hPowDvd : r ^ e r ∣ L :=
            (dvd_mul_left (r ^ e r) (tau r)).trans (Finset.dvd_lcm hr)
          have hPowLe := ((Nat.factorization_le_iff_dvd
            (pow_pos (hPrime r hr).pos _).ne' hLpos.ne').mpr hPowDvd) r
          rw [Nat.factorization_pow_self (hPrime r hr)] at hPowLe
          simpa [hr] using hPowLe
        · simp [hr]
    have hRVal (r : ℕ) : R.factorization r =
        if r ∈ S then e r - max (T.factorization r) (s.factorization r) else 0 := by
      dsimp [R]
      rw [Nat.factorization_prod_apply (fun q hq =>
        (pow_pos (hPrime q hq).pos _).ne')]
      calc
        (∑ q ∈ S, (q ^ (e q - max (T.factorization q) (s.factorization q))).factorization r) =
            ∑ q ∈ S, if q = r then
              e q - max (T.factorization q) (s.factorization q) else 0 := by
                apply Finset.sum_congr rfl
                intro q hq
                rw [(hPrime q hq).factorization_pow]
                by_cases hqr : q = r <;> simp [Finsupp.single_apply, hqr]
        _ = if r ∈ S then e r - max (T.factorization r) (s.factorization r) else 0 := by
          simp
    have hQuotVal (X : ℕ) (hX : 0 < X) (r : ℕ) :
        (X / Nat.gcd X s).factorization r =
          X.factorization r - min (X.factorization r) (s.factorization r) := by
      rw [Nat.factorization_div (Nat.gcd_dvd_left X s), Finsupp.tsub_apply,
        Nat.factorization_gcd hX.ne' hs.ne', Finsupp.inf_apply]
    have hBasePos : 0 < T / Nat.gcd T s := by
      exact Nat.div_pos (Nat.le_of_dvd hTpos (Nat.gcd_dvd_left T s))
        (Nat.gcd_pos_of_pos_left s hTpos)
    have hResult : L / Nat.gcd L s = (T / Nat.gcd T s) * R := by
      apply Nat.eq_of_factorization_eq
        (Nat.div_pos (Nat.le_of_dvd hLpos (Nat.gcd_dvd_left L s))
          (Nat.gcd_pos_of_pos_left s hLpos)).ne'
        (mul_pos hBasePos hRpos).ne'
      intro r
      rw [hQuotVal L hLpos r,
        Nat.factorization_mul hBasePos.ne' hRpos.ne', Finsupp.add_apply,
        hQuotVal T hTpos r, hLVal r, hRVal r]
      by_cases hr : r ∈ S
      · simp only [if_pos hr]
        omega
      · simp [hr]
    exact hResult

  let M0 := ∏ p ∈ S, p
  let M := ∏ p ∈ S, p ^ a p
  let T := S.lcm period
  let depth := fun p : ℕ =>
    padicValNat p (Nat.fib
      (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))
  have hPCL4 := golden_finite_support_square_period S hS hPrime hLarge
  dsimp only at hPCL4
  have hSelf (p : ℕ) (hp : p ∈ S) : ¬ p ∣ period p := by
    intro hd
    exact (lt_irrefl p) (hPCL4.1 p hp p hp hd)
  have hTauPos (p : ℕ) (hp : p ∈ S) : 0 < period p := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hSelf p hp (by simp [hz])
  have hDepth (p : ℕ) (hp : p ∈ S) : 0 < depth p :=
    (golden_matrix_prime_power_period p 1 (hPrime p hp)
      (hLarge p hp) (by decide)).1
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
  have hGeneral (b : ℕ → ℕ) (hb : ∀ p ∈ S, 1 ≤ b p) :
      stridePeriod s (∏ p ∈ S, p ^ b p) =
        (T / Nat.gcd T s) *
          ∏ p ∈ S, p ^ ((b p - depth p) -
            max (T.factorization p) (s.factorization p)) := by
    let N := ∏ p ∈ S, p ^ b p
    have hNpos : 0 < N := by
      dsimp [N]
      apply Finset.prod_pos
      intro p hp
      exact pow_pos (hPrime p hp).pos _
    have hNfac (r : ℕ) : N.factorization r = if r ∈ S then b r else 0 := by
      dsimp [N]
      rw [Nat.factorization_prod_apply (fun p hp =>
        (pow_pos (hPrime p hp).pos _).ne')]
      calc
        (∑ p ∈ S, (p ^ b p).factorization r) =
            ∑ p ∈ S, if p = r then b p else 0 := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [(hPrime p hp).factorization_pow]
              simp [Finsupp.single_apply]
        _ = if r ∈ S then b r else 0 := by simp
    have hNprimeFactors : N.primeFactors = S := by
      ext r
      change r ∈ N.factorization.support ↔ r ∈ S
      rw [Finsupp.mem_support_iff, hNfac r]
      by_cases hr : r ∈ S
      · have hbr : b r ≠ 0 := Nat.ne_of_gt (hb r hr)
        simp [hr, hbr]
      · simp [hr]
    have hLocal (p : ℕ) (hp : p ∈ S) :
        period (p ^ b p) = period p * p ^ (b p - depth p) :=
      (golden_matrix_prime_power_period p (b p) (hPrime p hp)
        (hLarge p hp) (hb p hp)).2.2.2.2.2.2.2.2.2
    have hPeriodN : period N =
        S.lcm (fun p => period p * p ^ (b p - depth p)) := by
      rw [period_crt N hNpos.ne', hNprimeFactors]
      apply Finset.lcm_congr rfl
      intro p hp
      rw [hNfac p, if_pos hp]
      exact hLocal p hp
    calc
      stridePeriod s N = period N / Nat.gcd (period N) s :=
        orderOf_pow' _ (by omega : s ≠ 0)
      _ = (S.lcm (fun p => period p * p ^ (b p - depth p))) /
          Nat.gcd (S.lcm (fun p => period p * p ^ (b p - depth p))) s := by
            rw [hPeriodN]
      _ = (T / Nat.gcd T s) *
          ∏ p ∈ S, p ^ ((b p - depth p) -
            max (T.factorization p) (s.factorization p)) :=
        finite_lcm_stride_masking S hPrime period
          (fun p => b p - depth p) hTauPos hSelf s (by omega)
  dsimp only
  constructor
  · exact hGeneral a ha
  · intro p hp e he
    let f := fun q : ℕ => if q = p then e else 1
    have hf : ∀ q ∈ S, 1 ≤ f q := by
      intro q hq
      by_cases hqp : q = p <;> simp [f, hqp, he]
    have hSpecial := hGeneral f hf
    have hBase := hGeneral (fun _ => 1) (by intro q hq; omega)
    have hBaseProd :
        (∏ q ∈ S, q ^ (((1 : ℕ) - depth q) -
          max (T.factorization q) (s.factorization q))) = 1 := by
      apply Finset.prod_eq_one
      intro q hq
      have hd := hDepth q hq
      have hz : (1 : ℕ) - depth q = 0 := by omega
      simp [hz]
    have hBaseline : stridePeriod s M0 = T / Nat.gcd T s := by
      have hM0 : (∏ q ∈ S, q ^ (1 : ℕ)) = M0 := by simp [M0]
      rw [hM0, hBaseProd, mul_one] at hBase
      exact hBase
    have hSpecialProd :
        (∏ q ∈ S, q ^ ((f q - depth q) -
          max (T.factorization q) (s.factorization q))) =
        p ^ (e - (depth p + max (T.factorization p) (s.factorization p))) := by
      calc
        (∏ q ∈ S, q ^ ((f q - depth q) -
          max (T.factorization q) (s.factorization q))) =
            p ^ ((f p - depth p) -
              max (T.factorization p) (s.factorization p)) := by
                apply Finset.prod_eq_single_of_mem p hp
                intro q hq hqp
                have hd := hDepth q hq
                have hfq : f q = 1 := by simp [f, hqp]
                have hz : f q - depth q = 0 := by omega
                simp [hz]
        _ = p ^ (e - (depth p + max (T.factorization p) (s.factorization p))) := by
          simp only [f, if_pos rfl]
          congr 1
          omega
    have hTarget : stridePeriod s (∏ q ∈ S, q ^ (if q = p then e else 1)) =
        (T / Nat.gcd T s) *
          p ^ (e - (depth p + max (T.factorization p) (s.factorization p))) := by
      rw [hSpecialProd] at hSpecial
      exact hSpecial
    change stridePeriod s (∏ q ∈ S, q ^ (if q = p then e else 1)) =
        stridePeriod s M0 *
          p ^ (e - (depth p + max (T.factorization p) (s.factorization p))) ∧
      (stridePeriod s M0 < stridePeriod s (∏ q ∈ S, q ^ (if q = p then e else 1)) ↔
        depth p + max (T.factorization p) (s.factorization p) < e)
    refine ⟨?_, ?_⟩
    · rw [hTarget, hBaseline]
    · rw [hTarget, hBaseline]
      have hTpos : 0 < T := by
        apply Nat.pos_of_ne_zero
        apply Finset.lcm_ne_zero_iff.mpr
        intro q hq
        exact (hTauPos q hq).ne'
      have hBpos : 0 < T / Nat.gcd T s :=
        Nat.div_pos (Nat.le_of_dvd hTpos (Nat.gcd_dvd_left T s))
          (Nat.gcd_pos_of_pos_left s hTpos)
      constructor
      · intro hlt
        by_contra hne
        change ¬ depth p + max (T.factorization p) (s.factorization p) < e at hne
        have hz : e - (depth p + max (T.factorization p) (s.factorization p)) = 0 := by
          omega
        simp [hz] at hlt
      · intro hgt
        change depth p + max (T.factorization p) (s.factorization p) < e at hgt
        have hexp : 0 < e -
            (depth p + max (T.factorization p) (s.factorization p)) := by omega
        have hpow : 1 < p ^
            (e - (depth p + max (T.factorization p) (s.factorization p))) :=
          Nat.one_lt_pow (Nat.ne_of_gt hexp) (hPrime p hp).one_lt
        exact lt_mul_of_one_lt_right hBpos hpow

#print axioms golden_finite_support_stride_masking

end D5.S3.Arith.Primes.GoldenFiniteSupportStrideMasking

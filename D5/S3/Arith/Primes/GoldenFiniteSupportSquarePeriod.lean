/- GID: D5/S3/Arith/Primes/GoldenFiniteSupportSquarePeriod
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenFiniteSupportSquarePeriod
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Sink primes determine the exact square-period ratio on finite prime support. -/

import D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition D5.S3.Arith.GoldenFibonacciModulusPeriod
open D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

namespace D5.S3.Arith.Primes.GoldenFiniteSupportSquarePeriod

/-- Exact simultaneous square-period ratio, sink criterion, and acyclic edge direction. -/
theorem golden_finite_support_square_period
    (S : Finset ℕ) (hS : S.Nonempty)
    (hPrime : ∀ p ∈ S, p.Prime) (hLarge : ∀ p ∈ S, 5 < p) :
    let period := fun m : ℕ =>
      orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    let stridePeriod := fun s m : ℕ =>
      orderOf ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) ^ s)
    let M := ∏ p ∈ S, p
    let depth := fun p : ℕ =>
      padicValNat p (Nat.fib
        (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))
    let sink := fun p : ℕ => ∀ q ∈ S, ¬ p ∣ period q
    (∀ p ∈ S, ∀ q ∈ S, p ∣ period q → p < q) ∧
    (∀ v : S, ¬ Relation.TransGen
      (fun a b : S => (a : ℕ) ∣ period (b : ℕ)) v v) ∧
    (∀ s : ℕ, 1 ≤ s → s.Coprime M →
      stridePeriod s (M ^ 2) / stridePeriod s M =
        ∏ p ∈ S, if sink p ∧ depth p = 1 then p else 1) ∧
    (∀ s : ℕ, 1 ≤ s → s.Coprime M →
      (stridePeriod s (M ^ 2) = stridePeriod s M ↔
        ∀ p ∈ S, sink p → 2 ≤ depth p) ∧
      (stridePeriod s (M ^ 2) = stridePeriod s M →
        2 ≤ depth (S.max' hS))) := by
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
  let stridePeriod := fun s m : ℕ =>
    orderOf ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m)) ^ s)
  have finite_sink_lcm
      (S : Finset ℕ) (hPrime : ∀ p ∈ S, p.Prime)
      (tau depth : ℕ → ℕ)
      (hSelf : ∀ p ∈ S, ¬ p ∣ tau p)
      (hDepth : ∀ p ∈ S, 0 < depth p) :
      S.lcm (fun p => tau p * p ^ (2 - depth p)) =
        S.lcm tau *
          ∏ p ∈ S.filter (fun p => depth p = 1 ∧
            ∀ q ∈ S, ¬ p ∣ tau q), p := by
    classical
    let T := S.lcm tau
    let H := S.filter (fun p => depth p = 1 ∧ ∀ q ∈ S, ¬ p ∣ tau q)
    let R := ∏ p ∈ H, p
    let L := S.lcm (fun p => tau p * p ^ (2 - depth p))
    have hTdvd : ∀ p ∈ S, tau p ∣ T := by
      intro p hp
      exact Finset.dvd_lcm hp
    have hNoDvdT (p : ℕ) (hp : p ∈ H) : ¬ p ∣ T := by
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hSink := (Finset.mem_filter.mp hp).2.2
      intro hd
      have hProd : p ∣ ∏ q ∈ S, tau q :=
        hd.trans (Finset.lcm_dvd_prod S tau)
      obtain ⟨q, hq, hpq⟩ := ((hPrime p hpS).prime.dvd_finsetProd_iff tau).mp hProd
      exact hSink q hq hpq
    have hCoprime : R.Coprime T := by
      exact Nat.coprime_prod_left_iff.mpr (by
        intro p hp
        exact ((hPrime p (Finset.mem_filter.mp hp).1).coprime_iff_not_dvd).mpr
          (hNoDvdT p hp))
    have hLowerT : T ∣ L := by
      apply Finset.lcm_dvd
      intro p hp
      exact (dvd_mul_right (tau p) (p ^ (2 - depth p))).trans
        (Finset.dvd_lcm hp)
    have hLowerR : R ∣ L := by
      apply Finset.prod_dvd_of_isRelPrime
      · intro p hp q hq hpq
        have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
        have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
        exact Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (hPrime p hpS) (hPrime q hqS)).mpr hpq)
      · intro p hp
        have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
        have hOne : depth p = 1 := (Finset.mem_filter.mp hp).2.1
        have hpLocal : p ∣ tau p * p ^ (2 - depth p) := by
          simpa [hOne, Nat.mul_comm] using (dvd_mul_left p (tau p))
        exact hpLocal.trans (Finset.dvd_lcm hpS)
    have hLower : T * R ∣ L :=
      hCoprime.symm.mul_dvd_of_dvd_of_dvd hLowerT hLowerR
    have hUpper : L ∣ T * R := by
      apply Finset.lcm_dvd
      intro p hp
      by_cases hOne : depth p = 1
      · by_cases hSink : ∀ q ∈ S, ¬ p ∣ tau q
        · have hpH : p ∈ H := Finset.mem_filter.mpr ⟨hp, hOne, hSink⟩
          have hpR : p ∣ R := Finset.dvd_prod_of_mem id hpH
          simpa [hOne] using (Nat.mul_dvd_mul (hTdvd p hp) hpR)
        · push_neg at hSink
          obtain ⟨q, hq, hpq⟩ := hSink
          have hpT : p ∣ T := hpq.trans (hTdvd q hq)
          have hCoprimeSelf : (tau p).Coprime p :=
            (((hPrime p hp).coprime_iff_not_dvd).mpr (hSelf p hp)).symm
          have hlocT : tau p * p ∣ T :=
            hCoprimeSelf.mul_dvd_of_dvd_of_dvd (hTdvd p hp) hpT
          simpa [hOne] using hlocT.trans (dvd_mul_right T R)
      · have hTwo : 2 ≤ depth p := by have := hDepth p hp; omega
        simpa [Nat.sub_eq_zero_of_le hTwo] using
          (hTdvd p hp).trans (dvd_mul_right T R)
    exact Nat.dvd_antisymm hUpper hLower

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
  let M := ∏ p ∈ S, p
  let depth := fun p : ℕ =>
    padicValNat p (Nat.fib
      (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))
  let sink := fun p : ℕ => ∀ q ∈ S, ¬ p ∣ period q
  let T := S.lcm period
  let H := S.filter (fun p => depth p = 1 ∧ sink p)
  let R := ∏ p ∈ H, p
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
  have hSelf (p : ℕ) (hp : p ∈ S) : ¬ p ∣ period p :=
    (hBound p (hPrime p hp) (hLarge p hp)).elim (fun h => h.2) (fun h => h.2)
  have hDepth (p : ℕ) (hp : p ∈ S) : 0 < depth p := by
    exact (golden_matrix_prime_power_period p 1 (hPrime p hp)
      (hLarge p hp) (by decide)).1
  have hPrimeFactors : M.primeFactors = S := Nat.primeFactors_prod hPrime
  have hSquarefree : Squarefree M := by
    dsimp [M]
    refine Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => ?_) (fun p hp => (hPrime p hp).squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hPrime p hp) (hPrime q hq)).mpr hpq)
  have hMpos : 0 < M := by
    dsimp [M]
    exact Finset.prod_pos (fun p hp => (hPrime p hp).pos)
  have hMfac (p : ℕ) (hp : p ∈ S) : M.factorization p = 1 :=
    Nat.factorization_eq_one_of_squarefree hSquarefree (hPrime p hp)
      (Finset.dvd_prod_of_mem id hp)
  have hM2fac (p : ℕ) (hp : p ∈ S) : (M ^ 2).factorization p = 2 := by
    rw [Nat.factorization_pow]
    simp [hMfac p hp]
  have hLocal (p : ℕ) (hp : p ∈ S) (a : ℕ) (ha : 1 ≤ a) :
      period (p ^ a) = period p * p ^ (a - depth p) := by
    exact (golden_matrix_prime_power_period p a (hPrime p hp)
      (hLarge p hp) ha).2.2.2.2.2.2.2.2.2
  have hPeriodM : period M = T := by
    rw [period_crt M hMpos.ne', hPrimeFactors]
    apply Finset.lcm_congr rfl
    intro p hp
    rw [hMfac p hp, pow_one]
  have hPeriodM2 : period (M ^ 2) =
      S.lcm (fun p => period p * p ^ (2 - depth p)) := by
    rw [period_crt (M ^ 2) (pow_ne_zero _ hMpos.ne'), Nat.primeFactors_pow M (by decide),
      hPrimeFactors]
    apply Finset.lcm_congr rfl
    intro p hp
    rw [hM2fac p hp]
    exact hLocal p hp 2 (by decide)
  have hPeriodSquare : period (M ^ 2) = period M * R := by
    rw [hPeriodM2, hPeriodM]
    exact finite_sink_lcm S hPrime period depth hSelf hDepth
  have hRdvdM : R ∣ M :=
    Finset.prod_dvd_prod_of_subset H S id (Finset.filter_subset _ _)
  have hTpos : 0 < T := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro p hp hz
    exact hSelf p hp (by simp [hz])
  have hStride (s m : ℕ) (hs : 1 ≤ s) :
      stridePeriod s m = period m / Nat.gcd (period m) s := by
    exact orderOf_pow' _ (by omega : s ≠ 0)
  have hStrideSquare (s : ℕ) (hs : 1 ≤ s) (hcop : s.Coprime M) :
      stridePeriod s (M ^ 2) = stridePeriod s M * R := by
    have hRcopS : R.Coprime s := Nat.Coprime.of_dvd_left hRdvdM hcop.symm
    have hgcd : Nat.gcd (T * R) s = Nat.gcd T s :=
      Nat.Coprime.gcd_mul_right_cancel T hRcopS
    calc
      stridePeriod s (M ^ 2) = period (M ^ 2) /
          Nat.gcd (period (M ^ 2)) s := hStride s (M ^ 2) hs
      _ = (T * R) / Nat.gcd T s := by rw [hPeriodSquare, hPeriodM, hgcd]
      _ = (T / Nat.gcd T s) * R := by
        rw [Nat.mul_comm T R, Nat.mul_div_assoc R (Nat.gcd_dvd_left T s), Nat.mul_comm]
      _ = stridePeriod s M * R := by rw [hStride s M hs, hPeriodM]
  have hRone : R = 1 ↔ ∀ p ∈ S, sink p → 2 ≤ depth p := by
    constructor
    · intro hOne p hp hSinkP
      have hdpos := hDepth p hp
      by_contra h
      have hdOne : depth p = 1 := by omega
      have hpH : p ∈ H := Finset.mem_filter.mpr ⟨hp, hdOne, hSinkP⟩
      have hpR : p ∣ R := Finset.dvd_prod_of_mem id hpH
      rw [hOne] at hpR
      exact (hPrime p hp).ne_one (Nat.dvd_one.mp hpR)
    · intro h
      have hHempty : H = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hpH
        obtain ⟨hp, hdOne, hSinkP⟩ := Finset.mem_filter.mp hpH
        exact (by omega : ¬ 2 ≤ depth p) (h p hp hSinkP)
      simp [R, hHempty]
  have hRatio (s : ℕ) (hs : 1 ≤ s) (hcop : s.Coprime M) :
      stridePeriod s (M ^ 2) / stridePeriod s M = R := by
    rw [hStrideSquare s hs hcop]
    have hApos : 0 < stridePeriod s M := by
      rw [hStride s M hs, hPeriodM]
      exact Nat.div_pos
        (Nat.le_of_dvd hTpos (Nat.gcd_dvd_left T s))
        (Nat.gcd_pos_of_pos_left s hTpos)
    exact Nat.mul_div_cancel_left R hApos
  have hEqual (s : ℕ) (hs : 1 ≤ s) (hcop : s.Coprime M) :
      (stridePeriod s (M ^ 2) = stridePeriod s M ↔
        ∀ p ∈ S, sink p → 2 ≤ depth p) := by
    rw [hStrideSquare s hs hcop, ← hRone]
    have hApos : 0 < stridePeriod s M := by
      rw [hStride s M hs, hPeriodM]
      exact Nat.div_pos
        (Nat.le_of_dvd hTpos (Nat.gcd_dvd_left T s))
        (Nat.gcd_pos_of_pos_left s hTpos)
    constructor
    · intro heq
      apply Nat.mul_left_cancel hApos
      simpa only [mul_one] using heq
    · intro hR
      simp [hR]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    exact hEdge p q (hPrime p hp) (hPrime q hq) (hLarge q hq) hpq
  · intro v hv
    have hEdgeSub (a b : S)
        (hab : (a : ℕ) ∣ period (b : ℕ)) : (a : ℕ) < b :=
      hEdge _ _ (hPrime _ a.property) (hPrime _ b.property)
        (hLarge _ b.property) hab
    have hPath {a b : S}
        (h : Relation.TransGen
          (fun x y : S => (x : ℕ) ∣ period (y : ℕ)) a b) :
        (a : ℕ) < b := by
      induction h with
      | single hxy => exact hEdgeSub _ _ hxy
      | tail _ hxy ih => exact lt_trans ih (hEdgeSub _ _ hxy)
    exact (lt_irrefl (v : ℕ)) (hPath hv)
  · intro s hs hcop
    rw [hRatio s hs hcop]
    calc
      R = ∏ p ∈ S, if depth p = 1 ∧ sink p then p else 1 := by
        exact Finset.prod_filter (s := S) (fun p => depth p = 1 ∧ sink p) id
      _ = ∏ p ∈ S, if sink p ∧ depth p = 1 then p else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        simp [and_comm]
  · intro s hs hcop
    refine ⟨hEqual s hs hcop, ?_⟩
    intro heq
    have hMaxMem : S.max' hS ∈ S := Finset.max'_mem S hS
    apply (hEqual s hs hcop).mp heq _ hMaxMem
    intro q hq hEdgeMax
    have hlt := hEdge _ _ (hPrime _ hMaxMem)
      (hPrime q hq) (hLarge q hq) hEdgeMax
    exact (not_lt_of_ge (Finset.le_max' S q hq)) hlt

end D5.S3.Arith.Primes.GoldenFiniteSupportSquarePeriod

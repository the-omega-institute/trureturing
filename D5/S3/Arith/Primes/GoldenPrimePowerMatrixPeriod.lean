/- GID: D5/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenPrimePowerMatrixPeriod
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact Fibonacci matrix periods at prime powers. -/

import Mathlib
import D5.S3.Arith.GoldenApparition
import D5.S3.Arith.GoldenPrimePowerOrder
import D5.S3.Arith.GoldenFibonacciModulusPeriod
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

namespace D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

open scoped Matrix
open D5.S0.Carrier D5.S1.Scale
open D5.S3.Arith.GoldenApparition
open D5.S3.Arith.GoldenFibonacciModulusPeriod
open D5.S3.Arith.GoldenPrimePowerOrder
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

set_option maxHeartbeats 1000000 in
-- The single proof elaborates the universal matrix lift and all prime-power depths.
/-- The two coordinates of the first return have equal positive depth, and
the matrix period grows by exactly the remaining prime power. -/
theorem golden_matrix_prime_power_period
    (p a : ℕ) (hp : p.Prime) (hp5 : 5 < p) (ha : 1 ≤ a) :
    let τ := orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))
    let h := padicValNat p (Nat.fib (fibonacciRank p))
    0 < h ∧
      padicValNat p (Nat.fib τ) = h ∧
      padicValNat p (Nat.fib τ) = padicValNat p (Nat.fib (τ - 1) - 1) ∧
      Even τ ∧
      (Nat.fib (τ - 1) - 1) * (Nat.fib (τ - 1) + 1) =
        Nat.fib τ * (Nat.fib τ - Nat.fib (τ - 1)) ∧
      (¬ p ∣ Nat.fib (τ - 1) + 1 ∧
        ¬ p ∣ Nat.fib τ - Nat.fib (τ - 1)) ∧
      (∃ u v : ℕ,
        Nat.fib (τ - 1) = 1 + p ^ h * u ∧
        Nat.fib τ = p ^ h * v ∧ ¬ p ∣ v ∧
        ∃ A : Matrix (Fin 2) (Fin 2) ℕ,
          A = !![u + v, v; v, u] ∧
          (∀ q : ℕ,
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ τ =
              1 + ((p ^ h : ℕ) : ZMod q) •
                A.map (Nat.castRingHom (ZMod q))) ∧
          A.map (Nat.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ m : ℕ, 0 < m →
        ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^
            (τ * m) = 1 ↔ a ≤ h + padicValNat p m)) ∧
      (∀ n : ℕ,
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^ n = 1 →
          τ ∣ n) ∧
      orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
        τ * p ^ (a - h) := by
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
  have hpair (m n : ℕ) :
      (GoldenMod.phi : GoldenMod m) ^ (n + 1) =
        ⟨(Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)⟩ := by
    have h := congrArg (GoldenMod.reduce m) (golden_phi_pow_eq_fib_pair n)
    have hr : GoldenMod.reduce m
        (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) =
        ⟨(Nat.fib n : ZMod m), (Nat.fib (n + 1) : ZMod m)⟩ := by
      apply GoldenMod.ext
      · change (((Nat.fib n : ℕ) : ℤ) : ZMod m) = (Nat.fib n : ZMod m)
        rw [Int.cast_natCast]
      · change (((Nat.fib (n + 1) : ℕ) : ℤ) : ZMod m) =
          (Nat.fib (n + 1) : ZMod m)
        rw [Int.cast_natCast]
    have hphi : GoldenMod.reduce m D5.S0.Carrier.phi = GoldenMod.phi := by
      apply GoldenMod.ext <;>
        norm_num [GoldenMod.reduce, D5.S0.Carrier.phi, GoldenMod.phi]
    simpa only [map_pow, hphi, hr] using h
  let t := orderOf (GoldenMod.phi : GoldenMod p)
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpModFive : (p : ZMod 5) ≠ 0 := by
    intro hz
    have hpEqFive : p = 5 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp
        ((ZMod.natCast_eq_zero_iff p 5).mp hz)).symm
    omega
  have hprimeCase :
      (t ∣ p - 1 ∧ ¬ p ∣ t) ∨ (t ∣ 2 * (p + 1) ∧ ¬ p ∣ t) := by
    have hpNotDvdFive : ¬ p ∣ 5 := by
      intro h
      have hle := Nat.le_of_dvd (by decide : 0 < 5) h
      omega
    have hentry := fibonacci_apparition_entry_point hp hpNotDvdFive
    have hfp : ((Nat.fib p : ℕ) : ZMod p) = (legendreSym 5 p : ZMod p) := by
      simpa only [Int.fib_natCast, Int.cast_natCast] using hentry.2
    rcases legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpModFive with
      heps | heps
    · left
      have hfprev : ((Nat.fib (p - 1) : ℕ) : ZMod p) = 0 := by
        have h := hentry.1
        rw [heps] at h
        have hindex : (p : ℤ) - 1 = ((p - 1 : ℕ) : ℤ) := by omega
        rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
        exact h
      have hfcurrent : ((Nat.fib p : ℕ) : ZMod p) = 1 := by
        simpa [heps] using hfp
      have hpow : (GoldenMod.phi : GoldenMod p) ^ p = GoldenMod.phi := by
        have h := hpair p (p - 1)
        have hindex : p - 1 + 1 = p := by omega
        rw [hindex] at h
        apply GoldenMod.ext
        · simpa [GoldenMod.phi] using (congrArg GoldenMod.a h).trans hfprev
        · simpa [GoldenMod.phi] using (congrArg GoldenMod.b h).trans hfcurrent
      have hinv : (GoldenMod.phi : GoldenMod p) *
          (GoldenMod.phi - 1) = 1 := by
        apply GoldenMod.ext <;>
          simp [GoldenMod.phi, sub_eq_add_neg]
      have hreturn : (GoldenMod.phi : GoldenMod p) ^ (p - 1) = 1 := by
        have hindex : p - 1 + 1 = p := by omega
        calc
          (GoldenMod.phi : GoldenMod p) ^ (p - 1) =
              (GoldenMod.phi : GoldenMod p) ^ (p - 1) *
                (GoldenMod.phi * (GoldenMod.phi - 1)) := by rw [hinv, mul_one]
          _ = (GoldenMod.phi : GoldenMod p) ^ p *
                (GoldenMod.phi - 1) := by
              rw [← mul_assoc, ← pow_succ, hindex]
          _ = 1 := by rw [hpow, hinv]
      have hdiv : t ∣ p - 1 := orderOf_dvd_of_pow_eq_one hreturn
      refine ⟨hdiv, ?_⟩
      intro hpdvd
      have hbad : p ∣ p - 1 := dvd_trans hpdvd hdiv
      have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hbad
      omega
    · right
      have hfnext : ((Nat.fib (p + 1) : ℕ) : ZMod p) = 0 := by
        have h := hentry.1
        rw [heps] at h
        have hindex : (p : ℤ) - -1 = ((p + 1 : ℕ) : ℤ) := by omega
        rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
        exact h
      have hfcurrent : ((Nat.fib p : ℕ) : ZMod p) = -1 := by
        simpa [heps] using hfp
      have hpow : (GoldenMod.phi : GoldenMod p) ^ (p + 1) = -1 := by
        have h := hpair p p
        apply GoldenMod.ext
        · simpa using (congrArg GoldenMod.a h).trans hfcurrent
        · simpa using (congrArg GoldenMod.b h).trans hfnext
      have hreturn : (GoldenMod.phi : GoldenMod p) ^ (2 * (p + 1)) = 1 := by
        calc
          (GoldenMod.phi : GoldenMod p) ^ (2 * (p + 1)) =
              ((GoldenMod.phi : GoldenMod p) ^ (p + 1)) ^ 2 := by
                rw [Nat.mul_comm 2 (p + 1), pow_mul]
          _ = 1 := by rw [hpow]; norm_num
      have hdiv : t ∣ 2 * (p + 1) := orderOf_dvd_of_pow_eq_one hreturn
      refine ⟨hdiv, ?_⟩
      intro hpdvd
      have hbad : p ∣ 2 * (p + 1) := dvd_trans hpdvd hdiv
      rcases hp.dvd_mul.mp hbad with htwo | hnext
      · have hle := Nat.le_of_dvd (by decide : 0 < 2) htwo
        omega
      · have hone : p ∣ 1 := (Nat.dvd_add_self_left).mp hnext
        have hle := Nat.le_of_dvd (by decide : 0 < 1) hone
        omega
  have hprimeBound : t ∣ p - 1 ∨ t ∣ 2 * (p + 1) :=
    hprimeCase.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have htpos : 0 < t := by
    rcases hprimeBound with h | h
    · exact Nat.pos_of_dvd_of_pos h (by omega)
    · exact Nat.pos_of_dvd_of_pos h (by omega)
  have hpNotDvdT : ¬ p ∣ t :=
    hprimeCase.elim (fun h => h.2) (fun h => h.2)
  have htTwo : 2 ≤ t := by
    have htNeOne : t ≠ 1 := by
      intro htOne
      have hphi : (GoldenMod.phi : GoldenMod p) = 1 :=
        orderOf_eq_one_iff.mp htOne
      have hb := congrArg GoldenMod.b hphi
      have hpOne : (1 : ZMod p) ≠ 0 := by
        intro hz
        have hpd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using hz)
        exact hp.ne_one (Nat.dvd_one.mp hpd)
      exact hpOne (by simpa [GoldenMod.phi] using hb)
    omega
  let c := Nat.fib (t - 1)
  let f := Nat.fib t
  have htPred : t - 1 + 1 = t := by omega
  have hreturnP : (GoldenMod.phi : GoldenMod p) ^ t = 1 := pow_orderOf_eq_one _
  have hcMod : (c : ZMod p) = 1 := by
    have h := hpair p (t - 1)
    rw [htPred, hreturnP] at h
    simpa [c] using (congrArg GoldenMod.a h).symm
  have hfMod : (f : ZMod p) = 0 := by
    have h := hpair p (t - 1)
    rw [htPred, hreturnP] at h
    simpa [f] using (congrArg GoldenMod.b h).symm
  have hpDvdF : p ∣ f := (ZMod.natCast_eq_zero_iff f p).mp hfMod
  have hfNeZero : f ≠ 0 := (Nat.fib_pos.mpr htpos).ne'
  let h := padicValNat p (Nat.fib (fibonacciRank p))
  have hval : padicValNat p f = h :=
    fibonacci_original_rank_valuation p t hp hpDvdF hpNotDvdT
  letI : Fact p.Prime := ⟨hp⟩
  have hhpos : 0 < h := by
    have hvalpos : 1 ≤ padicValNat p f :=
      (padicValNat_dvd_iff_le (p := p) hfNeZero).mp (by simpa using hpDvdF)
    omega
  have hCassini :
      (c : ℤ) * (Nat.fib (t + 1) : ℤ) - (f : ℤ) ^ 2 = (-1 : ℤ) ^ t := by
    have hbase := fib_cassini_from_golden_norm (t - 1)
    have hnext : t - 1 + 2 = t + 1 := by omega
    simpa only [htPred, hnext, c, f] using hbase
  have htEven : Even t := by
    by_contra hnot
    have hodd : Odd t := Nat.not_even_iff_odd.mp hnot
    have hfNextMod : (Nat.fib (t + 1) : ZMod p) = 1 := by
      have hrec := Nat.fib_add_two (n := t - 1)
      have hnext : t - 1 + 2 = t + 1 := by omega
      rw [hnext, htPred] at hrec
      have hz := congrArg (fun n : ℕ => (n : ZMod p)) hrec
      simpa [c, f, hcMod, hfMod] using hz
    have hmod := congrArg (fun z : ℤ => (z : ZMod p)) hCassini
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_neg, Int.cast_one] at hmod
    rw [hcMod, hfMod, hfNextMod] at hmod
    have hneg : (-1 : ZMod p) = 1 := by
      simpa [hodd.neg_one_pow] using hmod.symm
    have htwozero : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = 1 + 1 := by ring
        _ = -1 + 1 := by rw [hneg]
        _ = 0 := by ring
    have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwozero
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hpd
    omega
  have hrec : Nat.fib (t + 1) = c + f := by
    have hbase := Nat.fib_add_two (n := t - 1)
    simpa only [htPred, show t - 1 + 2 = t + 1 by omega, c, f,
      Nat.add_comm] using hbase
  have hCassiniOne : (c : ℤ) ^ 2 + (c : ℤ) * (f : ℤ) - (f : ℤ) ^ 2 = 1 := by
    rw [hrec, htEven.neg_one_pow] at hCassini
    push_cast at hCassini
    nlinarith [hCassini]
  have hcPos : 0 < c := Nat.fib_pos.mpr (by omega)
  have hcLeF : c ≤ f := Nat.fib_mono (by omega : t - 1 ≤ t)
  have hIdentity : (c - 1) * (c + 1) = f * (f - c) := by
    have hInt : ((c - 1 : ℕ) : ℤ) * ((c + 1 : ℕ) : ℤ) =
        (f : ℤ) * ((f - c : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_add, Nat.cast_one,
        Nat.cast_sub hcLeF]
      nlinarith [hCassiniOne]
    exact_mod_cast hInt
  have hcPlusNot : ¬ p ∣ c + 1 := by
    intro hdvd
    have hz : ((c + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have htwo : (2 : ZMod p) = 0 := by
      calc
        (2 : ZMod p) = (c : ZMod p) + 1 := by rw [hcMod]; ring
        _ = 0 := by simpa [Nat.cast_add] using hz
    have hpd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hpd
    omega
  have hpPowF : p ^ h ∣ f := by
    exact (padicValNat_dvd_iff_le (p := p) hfNeZero).mpr (by omega)
  have hpPowC : p ^ h ∣ c - 1 := by
    have hcop : (p ^ h).Coprime (c + 1) := by
      rw [Nat.coprime_comm, Nat.coprime_pow_right_iff hhpos,
        Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hcPlusNot
    apply (hcop.dvd_mul_right).mp
    rw [hIdentity]
    exact dvd_mul_of_dvd_left hpPowF _
  have hfSubNot : ¬ p ∣ f - c := by
    intro hdvd
    have hz : ((f - c : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hsub : (f : ZMod p) - (c : ZMod p) = 0 := by
      simpa only [Nat.cast_sub hcLeF] using hz
    rw [hfMod, hcMod] at hsub
    have hneg : (-1 : ZMod p) = 0 := by simpa only [zero_sub] using hsub
    have hone : (1 : ZMod p) = 0 := neg_eq_zero.mp hneg
    have hpd : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using hone)
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hpd
    omega
  have hpPowCNextNot : ¬ p ^ (h + 1) ∣ c - 1 := by
    intro hdvd
    have hcop : (p ^ (h + 1)).Coprime (f - c) := by
      rw [Nat.coprime_comm, Nat.coprime_pow_right_iff (by omega : 0 < h + 1),
        Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hfSubNot
    have hmul : p ^ (h + 1) ∣ f * (f - c) := by
      rw [← hIdentity]
      exact dvd_mul_of_dvd_left hdvd _
    have hbad : p ^ (h + 1) ∣ f := (hcop.dvd_mul_right).mp hmul
    have hnot := pow_succ_padicValNat_not_dvd (p := p) hfNeZero
    rw [hval] at hnot
    exact hnot hbad
  have hvalC : padicValNat p (c - 1) = h := by
    have hcMinusNe : c - 1 ≠ 0 := by
      intro hz
      exact hpPowCNextNot (by rw [hz]; exact dvd_zero _)
    have hge : h ≤ padicValNat p (c - 1) :=
      (padicValNat_dvd_iff_le (p := p) hcMinusNe).mp hpPowC
    have hlt : padicValNat p (c - 1) < h + 1 := by
      by_contra hnot
      exact hpPowCNextNot
        ((padicValNat_dvd_iff_le (p := p) hcMinusNe).mpr (by omega))
    omega
  let u := (c - 1) / p ^ h
  let v := f / p ^ h
  have hCu : c = 1 + p ^ h * u := by
    have hdiv := Nat.mul_div_cancel' hpPowC
    dsimp [u] at *
    omega
  have hFv : f = p ^ h * v := by
    simpa only [v] using (Nat.mul_div_cancel' hpPowF).symm
  have hpNotDvdV : ¬ p ∣ v := by
    intro hdvd
    have hbad : p ^ (h + 1) ∣ f := by
      rw [pow_succ, hFv]
      exact mul_dvd_mul_left _ hdvd
    have hnot : ¬ p ^ (padicValNat p f + 1) ∣ f :=
      pow_succ_padicValNat_not_dvd hfNeZero
    rw [hval] at hnot
    exact hnot hbad
  have hformula (m : ℕ) :
      (GoldenMod.phi : GoldenMod m) ^ t =
        1 + ((p ^ h : ℕ) : GoldenMod m) *
          (⟨(u : ZMod m), (v : ZMod m)⟩ : GoldenMod m) := by
    have hbase := hpair m (t - 1)
    rw [htPred] at hbase
    rw [hbase]
    apply GoldenMod.ext
    · have hc := congrArg (fun n : ℕ => (n : ZMod m)) hCu
      simpa only [c, GoldenMod.a_add, GoldenMod.a_one, GoldenMod.a_mul,
        GoldenMod.a_natCast, GoldenMod.b_natCast, Nat.cast_add,
        Nat.cast_one, Nat.cast_mul, zero_mul, add_zero] using hc
    · have hf := congrArg (fun n : ℕ => (n : ZMod m)) hFv
      simpa only [f, GoldenMod.b_add, GoldenMod.b_one, GoldenMod.b_mul,
        GoldenMod.a_natCast, GoldenMod.b_natCast, Nat.cast_mul,
        zero_mul, zero_add, add_zero] using hf
  let A : Matrix (Fin 2) (Fin 2) ℕ := !![u + v, v; v, u]
  have hmatrixLift (q : ℕ) :
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ t =
        1 + ((p ^ h : ℕ) : ZMod q) • A.map (Nat.castRingHom (ZMod q)) := by
    have hbase := congrArg (goldenMatrixHom q) (hpair q (t - 1))
    have hphi : goldenMatrixHom q (GoldenMod.phi : GoldenMod q) =
        !![1, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [goldenMatrixHom, multiplicationMatrix, GoldenMod.phi]
    rw [htPred, map_pow, hphi] at hbase
    have hcoords :
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ t =
          goldenMatrixHom q (⟨(c : ZMod q), (f : ZMod q)⟩ : GoldenMod q) := by
      simpa only [c, f] using hbase
    have hcq : (c : ZMod q) = 1 + (p ^ h : ZMod q) * (u : ZMod q) := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod q)) hCu
    have hfq : (f : ZMod q) = (p ^ h : ZMod q) * (v : ZMod q) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod q)) hFv
    rw [hcoords]
    change
      !![(c : ZMod q) + (f : ZMod q), (f : ZMod q);
          (f : ZMod q), (c : ZMod q)] =
        1 + ((p ^ h : ℕ) : ZMod q) • A.map (Nat.castRingHom (ZMod q))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, hcq, hfq] <;> ring
  have hAnonzero : A.map (Nat.castRingHom (ZMod p)) ≠ 0 := by
    intro hzero
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (ZMod p) => M 0 1) hzero
    have hvzero : (v : ZMod p) = 0 := by
      simpa [A, Matrix.map_apply] using h01
    exact hpNotDvdV ((ZMod.natCast_eq_zero_iff v p).mp hvzero)
  have hpm : h + 2 ≤ p * h := by nlinarith
  let pair (q : ℕ) : GoldenMod q := ⟨u, v⟩
  have hvNotDvd : ¬ (p : ℤ) ∣ (v : ℤ) := by
    intro hdvd
    exact hpNotDvdV (Int.natCast_dvd_natCast.mp hdvd)
  have hlocal (n : ℕ) :
      orderOf (1 + ((p ^ h : ℕ) : GoldenMod (p ^ (n + h))) *
        pair (p ^ (n + h))) = p ^ n := by
    have horder := golden_prime_power_order (p := p) (m := h) (n := n)
      hp hhpos hpm (u : ℤ) (v : ℤ) (Or.inr hvNotDvd)
    simpa only [Nat.cast_pow, Int.cast_natCast, pair] using horder
  have hlower (e : ℕ) (he : 1 ≤ e)
      (hpos : 0 < orderOf (GoldenMod.phi : GoldenMod (p ^ e))) :
      t ∣ orderOf (GoldenMod.phi : GoldenMod (p ^ e)) := by
    let N := orderOf (GoldenMod.phi : GoldenMod (p ^ e))
    have hpred : N - 1 + 1 = N := by omega
    have hpow : (GoldenMod.phi : GoldenMod (p ^ e)) ^ N = 1 :=
      pow_orderOf_eq_one _
    have hcoords := hpair (p ^ e) (N - 1)
    rw [hpred, hpow] at hcoords
    have hcE : (Nat.fib (N - 1) : ZMod (p ^ e)) = 1 := by
      simpa using (congrArg GoldenMod.a hcoords).symm
    have hfE : (Nat.fib N : ZMod (p ^ e)) = 0 := by
      simpa using (congrArg GoldenMod.b hcoords).symm
    have hpdiv : p ∣ p ^ e := dvd_pow_self p (by omega : e ≠ 0)
    let cast : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
    have hcP : (Nat.fib (N - 1) : ZMod p) = 1 := by
      have hcast := congrArg cast hcE
      simpa only [cast, ZMod.castHom_apply, ZMod.cast_natCast hpdiv,
        map_one] using hcast
    have hfP : (Nat.fib N : ZMod p) = 0 := by
      have hcast := congrArg cast hfE
      simpa only [cast, ZMod.castHom_apply, ZMod.cast_natCast hpdiv,
        map_zero] using hcast
    apply orderOf_dvd_of_pow_eq_one
    have hcoordsP := hpair p (N - 1)
    rw [hpred] at hcoordsP
    rw [hcoordsP]
    apply GoldenMod.ext
    · simpa using hcP
    · simpa using hfP
  let x : GoldenMod (p ^ a) := GoldenMod.phi
  have hgoal : orderOf x = t * p ^ (a - h) := by
    by_cases hale : a ≤ h
    · have hzero : (((p ^ h : ℕ) : GoldenMod (p ^ a))) = 0 :=
        (CharP.cast_eq_zero_iff (GoldenMod (p ^ a)) (p ^ a) _).mpr
          (pow_dvd_pow p hale)
      have hxreturn : x ^ t = 1 := by
        simpa [x, hzero, pair] using hformula (p ^ a)
      have hNdivT : orderOf x ∣ t := orderOf_dvd_of_pow_eq_one hxreturn
      have hNpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hNdivT htpos
      have htdivN : t ∣ orderOf x := hlower a ha hNpos
      have hNeqT : orderOf x = t := Nat.dvd_antisymm hNdivT htdivN
      simpa [Nat.sub_eq_zero_of_le hale] using hNeqT
    · have hle : h ≤ a := by omega
      let n := a - h
      have hnadd : n + h = a := Nat.sub_add_cancel hle
      have hY : orderOf (x ^ t) = p ^ n := by
        have hloc := hlocal n
        rw [hnadd] at hloc
        have hform := hformula (p ^ a)
        change x ^ t = 1 + ((p ^ h : ℕ) : GoldenMod (p ^ a)) * pair (p ^ a) at hform
        rw [hform]
        exact hloc
      have hxreturn : x ^ (t * p ^ n) = 1 := by
        rw [pow_mul, ← hY]
        exact pow_orderOf_eq_one _
      have hNdiv : orderOf x ∣ t * p ^ n := orderOf_dvd_of_pow_eq_one hxreturn
      have hNpos : 0 < orderOf x :=
        Nat.pos_of_dvd_of_pos hNdiv (mul_pos htpos (pow_pos hp.pos n))
      have htdivN : t ∣ orderOf x := hlower a ha hNpos
      have hquot : orderOf x / t = p ^ n := by
        rw [← hY]
        exact (orderOf_pow_of_dvd (by omega : t ≠ 0) htdivN).symm
      have hmult := Nat.div_mul_cancel htdivN
      rw [hquot] at hmult
      simpa only [n, Nat.mul_comm] using hmult.symm
  have hreturns (m : ℕ) (hm : 0 < m) :
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^
          (t * m) = 1 ↔ a ≤ h + padicValNat p m) := by
    rw [← orderOf_dvd_iff_pow_eq_one,
      ← hMatrixOrder (p ^ a), hgoal]
    have hcancel : (t * p ^ (a - h) ∣ t * m) ↔ p ^ (a - h) ∣ m := by
      exact Nat.mul_dvd_mul_iff_left htpos
    rw [hcancel, padicValNat_dvd_iff_le (p := p) hm.ne']
    omega
  have hreturnDiv (n : ℕ)
      (hn : (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^ n = 1) :
      t ∣ n := by
    have hdvd := orderOf_dvd_of_pow_eq_one hn
    rw [← hMatrixOrder (p ^ a)] at hdvd
    change orderOf x ∣ n at hdvd
    rw [hgoal] at hdvd
    exact dvd_trans ⟨p ^ (a - h), rfl⟩ hdvd
  change 0 < h ∧
      padicValNat p
          (Nat.fib (orderOf
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)))) = h ∧
      padicValNat p
          (Nat.fib (orderOf
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)))) =
      padicValNat p
          (Nat.fib (orderOf
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) - 1) ∧
      Even (orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) ∧
      (Nat.fib (orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) - 1) *
        (Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) + 1) =
        Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) *
          (Nat.fib (orderOf
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) -
            Nat.fib (orderOf
              (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1)) ∧
      (¬ p ∣ Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) + 1 ∧
        ¬ p ∣ Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) -
            Nat.fib (orderOf
              (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1)) ∧
      (∃ u v : ℕ,
        Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) =
            1 + p ^ h * u ∧
        Nat.fib (orderOf
          (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) =
            p ^ h * v ∧ ¬ p ∣ v ∧
        ∃ A : Matrix (Fin 2) (Fin 2) ℕ,
          A = !![u + v, v; v, u] ∧
          (∀ q : ℕ,
            (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^
                (orderOf
                  (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) =
              1 + ((p ^ h : ℕ) : ZMod q) •
                A.map (Nat.castRingHom (ZMod q))) ∧
          A.map (Nat.castRingHom (ZMod p)) ≠ 0) ∧
      (∀ m : ℕ, 0 < m →
        ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^
            (orderOf
              (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) * m) =
          1 ↔ a ≤ h + padicValNat p m)) ∧
      (∀ n : ℕ,
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) ^ n = 1 →
          orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ∣ n) ∧
      orderOf
        (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod (p ^ a))) =
        orderOf (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
          p ^ (a - h)
  rw [← hMatrixOrder (p ^ a), ← hMatrixOrder p]
  exact ⟨hhpos, by simpa only [f] using hval,
    by simpa only [f, c] using hval.trans hvalC.symm,
    htEven, by simpa only [c, f] using hIdentity,
    ⟨by simpa only [c] using hcPlusNot,
      by simpa only [f, c] using hfSubNot⟩,
    ⟨u, v, by simpa only [c] using hCu,
      by simpa only [f] using hFv, hpNotDvdV,
      A, rfl, hmatrixLift, hAnonzero⟩,
    hreturns, hreturnDiv, hgoal⟩

#print axioms golden_matrix_prime_power_period

end D5.S3.Arith.Primes.GoldenPrimePowerMatrixPeriod

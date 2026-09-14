/- GID: D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   generality: I
   mirror-B: D5/B/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.NumberTheory.Multiplicity, mathlib/module/Mathlib.Tactic.NormNum, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Krizek's sigma-tau rational powers are exactly squarefree Mersenne-prime products. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.Mersenne.KrizekSigmaTauRationalPowerMersenne

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Products of distinct primes one less than a positive power of two. -/
def isMersenneProduct (n : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    n = ∏ p ∈ S, p ∧
      ∀ p ∈ S, p.Prime ∧ ∃ k : ℕ, 0 < k ∧ p + 1 = 2 ^ k

/-- The integer-power form of `sigma(n) = tau(n)^(a/b)`. -/
def ratPow (n : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (σ 1 n) ^ b = (σ 0 n) ^ a

private theorem tau_power_two_of_same_prime_support (n : ℕ) (hn : 1 < n)
    (hsupport : ∀ r : ℕ, r.Prime → (r ∣ σ 1 n ↔ r ∣ σ 0 n)) :
    ∃ c : ℕ, σ 0 n = 2 ^ c := by
  have hn0 : n ≠ 0 := by omega
  have htau0 : σ 0 n ≠ 0 := (sigma_pos 0 n hn0).ne'
  have htau1 : σ 0 n ≠ 1 := by
    intro h
    have := (sigma_eq_one_iff 0 n).mp h
    omega
  have htau : 1 < σ 0 n := by
    have := sigma_pos 0 n hn0
    omega
  have htauFactors : (σ 0 n).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.mpr htau
  let q := (σ 0 n).primeFactors.max' htauFactors
  have hqmem : q ∈ (σ 0 n).primeFactors := by
    exact Finset.max'_mem _ _
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  have hqTau : q ∣ σ 0 n := Nat.dvd_of_mem_primeFactors hqmem
  have hqeq : q = 2 := by
    rcases hqPrime.eq_two_or_odd' with hq | hqOdd
    · exact hq
    · exfalso
      have hcard : σ 0 n = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
        rw [sigma_zero_apply, Nat.card_divisors hn0]
      rw [hcard] at hqTau
      obtain ⟨p, hpMem, hqExp⟩ :=
        (hqPrime.prime.dvd_finsetProd_iff (fun p : ℕ => n.factorization p + 1)).mp hqTau
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
      let e := n.factorization p
      let G := ∑ i ∈ Finset.range q, p ^ i
      have hGdivLong : G ∣ ∑ i ∈ Finset.range (e + 1), p ^ i := by
        have hpowDiv : p ^ q - 1 ∣ p ^ (e + 1) - 1 :=
          Nat.pow_sub_one_dvd_pow_sub_one p hqExp
        have hqGeom : G * (p - 1) = p ^ q - 1 := by
          exact geom_sum_mul_of_one_le hpPrime.one_le q
        have heGeom : (∑ i ∈ Finset.range (e + 1), p ^ i) * (p - 1) =
            p ^ (e + 1) - 1 := by
          exact geom_sum_mul_of_one_le hpPrime.one_le (e + 1)
        rw [← hqGeom, ← heGeom] at hpowDiv
        exact (mul_dvd_mul_iff_right (Nat.sub_ne_zero_of_lt hpPrime.one_lt)).mp hpowDiv
      have hLongDivSigma : (∑ i ∈ Finset.range (e + 1), p ^ i) ∣ σ 1 n := by
        rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
        have hfactor :
            (∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) ∣
              ∏ r ∈ n.primeFactors,
                ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1) :=
          Finset.dvd_prod_of_mem
            (fun r : ℕ => ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1)) hpMem
        simpa only [e, mul_one] using hfactor
      have hGsigma : G ∣ σ 1 n := hGdivLong.trans hLongDivSigma
      have hsmall : 1 + p ≤ G := by
        have hq2 : 2 ≤ q := hqPrime.two_le
        have hle := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono hq2)
          (fun _ _ _ => Nat.zero_le _)
          (f := fun i : ℕ => p ^ i)
        simpa [G, Finset.sum_range_succ] using hle
      have hG1 : 1 < G := by
        have hp2 := hpPrime.two_le
        omega
      have uniquePrime (r : ℕ) (hrPrime : r.Prime) (hrG : r ∣ G) : r = q := by
        have hrSigma : r ∣ σ 1 n := hrG.trans hGsigma
        have hrTau : r ∣ σ 0 n := (hsupport r hrPrime).mp hrSigma
        have hrMem : r ∈ (σ 0 n).primeFactors :=
          hrPrime.mem_primeFactors hrTau htau0
        have hrle : r ≤ q := Finset.le_max' _ r hrMem
        have hrp : ¬r ∣ p := by
          intro hrp
          have hre : r = p := (Nat.prime_dvd_prime_iff_eq hrPrime hpPrime).mp hrp
          subst r
          letI : NeZero p := ⟨hpPrime.ne_zero⟩
          have hGzero : (G : ZMod p) = 0 :=
            (ZMod.natCast_eq_zero_iff G p).mpr hrG
          have hcast : (G : ZMod p) = 1 := by
            simp only [G, Nat.cast_sum, Nat.cast_pow]
            rw [Finset.sum_eq_single 0]
            · simp
            · intro i hi hi0
              simp [hi0]
            · simp [hqPrime.pos]
          have hpOneCast : ((1 : ℕ) : ZMod p) = 0 := by
            simpa only [Nat.cast_one] using hcast.symm.trans hGzero
          have hpOne : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp hpOneCast
          exact hpPrime.not_dvd_one hpOne
        letI : Fact r.Prime := ⟨hrPrime⟩
        letI : Fact q.Prime := ⟨hqPrime⟩
        have hGzero : (G : ZMod r) = 0 :=
          (ZMod.natCast_eq_zero_iff G r).mpr hrG
        have hGcast : (G : ZMod r) =
            ∑ i ∈ Finset.range q, (p : ZMod r) ^ i := by
          simp only [G, Nat.cast_sum, Nat.cast_pow]
        by_cases hpr : (p : ZMod r) = 1
        · have hrq : r ∣ q := by
            rw [← ZMod.natCast_eq_zero_iff q r]
            calc
              (q : ZMod r) = ∑ _i ∈ Finset.range q, (1 : ZMod r) := by simp
              _ = ∑ i ∈ Finset.range q, (p : ZMod r) ^ i := by simp [hpr]
              _ = (G : ZMod r) := hGcast.symm
              _ = 0 := hGzero
          exact (Nat.prime_dvd_prime_iff_eq hrPrime hqPrime).mp hrq
        · have hpzero : (p : ZMod r) ≠ 0 :=
            (ZMod.natCast_eq_zero_iff p r).not.mpr hrp
          have hpow : (p : ZMod r) ^ q = 1 := by
            have hgeom := geom_sum_mul (p : ZMod r) q
            have hz : (p : ZMod r) ^ q - 1 = 0 := by
              rw [← hgeom, ← hGcast, hGzero, zero_mul]
            exact sub_eq_zero.mp hz
          have hord : orderOf (p : ZMod r) = q := orderOf_eq_prime hpow hpr
          have hordDvd : orderOf (p : ZMod r) ∣ r - 1 :=
            ZMod.orderOf_dvd_card_sub_one hpzero
          rw [hord] at hordDvd
          have hr2 := hrPrime.two_le
          have hqle : q ≤ r - 1 := Nat.le_of_dvd (by omega) hordDvd
          omega
      obtain ⟨r, hrPrime, hrG⟩ := Nat.exists_prime_and_dvd (by omega : G ≠ 1)
      have hrq := uniquePrime r hrPrime hrG
      subst r
      have hqG : q ∣ G := hrG
      have hGzeroQ : (G : ZMod q) = 0 :=
        (ZMod.natCast_eq_zero_iff G q).mpr hqG
      letI : Fact q.Prime := ⟨hqPrime⟩
      have hGcastQ : (G : ZMod q) =
          ∑ i ∈ Finset.range q, (p : ZMod q) ^ i := by
        simp only [G, Nat.cast_sum, Nat.cast_pow]
      have hpmod : (p : ZMod q) = 1 := by
        have hgeom := geom_sum_mul (p : ZMod q) q
        have hpow : (p : ZMod q) ^ q = 1 := by
          have hz : (p : ZMod q) ^ q - 1 = 0 := by
            rw [← hgeom, ← hGcastQ, hGzeroQ, zero_mul]
          exact sub_eq_zero.mp hz
        calc
          (p : ZMod q) = (p : ZMod q) ^ q := (ZMod.pow_card _).symm
          _ = 1 := hpow
      have hpModEq : p ≡ 1 [MOD q] :=
        (ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hpmod)
      have hqpm1 : q ∣ p - 1 :=
        (Nat.modEq_iff_dvd' hpPrime.one_le).mp hpModEq.symm
      have hq_lt_p : q < p := by
        have hp2 := hpPrime.two_le
        have := Nat.le_of_dvd (by omega : 0 < p - 1) hqpm1
        omega
      have hq_not_p : ¬q ∣ p := by
        intro hqp
        have := (Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hqp
        omega
      have hmult : emultiplicity (q : ℤ) (G : ℤ) = 1 := by
        have hqIntPrime : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqPrime
        have hqIntSub' : (q : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hqpm1
        have hqIntSub : (q : ℤ) ∣ (p : ℤ) - 1 := by
          simpa only [Nat.cast_sub hpPrime.one_le, Nat.cast_one] using hqIntSub'
        have hqIntP : ¬(q : ℤ) ∣ (p : ℤ) := by exact_mod_cast hq_not_p
        simpa only [G, Nat.cast_sum, Nat.cast_pow, Nat.cast_one, one_pow, mul_one] using
          (emultiplicity_geom_sum₂_eq_one (p := q) (x := (p : ℤ)) (y := (1 : ℤ))
            hqIntPrime hqOdd hqIntSub hqIntP)
      have hqSqNotG : ¬q ^ 2 ∣ G := by
        have hlt : emultiplicity (q : ℤ) (G : ℤ) < (2 : ℕ) := by
          rw [hmult]
          norm_num
        have hz : ¬(q : ℤ) ^ 2 ∣ (G : ℤ) :=
          emultiplicity_lt_iff_not_dvd.mp hlt
        exact_mod_cast hz
      obtain ⟨k, hGqk⟩ := hqG
      by_cases hk : k = 1
      · subst k
        omega
      · obtain ⟨r, hrPrime, hrk⟩ := Nat.exists_prime_and_dvd hk
        have hrG : r ∣ G := by
          rw [hGqk]
          exact hrk.trans (dvd_mul_left k q)
        have hrq : r = q := uniquePrime r hrPrime hrG
        subst r
        apply hqSqNotG
        rw [hGqk, pow_two]
        exact Nat.mul_dvd_mul_left q hrk
  refine ⟨(σ 0 n).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd htau0 ?_⟩
  intro r hrPrime hrTau
  have hrMem : r ∈ (σ 0 n).primeFactors := hrPrime.mem_primeFactors hrTau htau0
  have hrle : r ≤ q := Finset.le_max' _ r hrMem
  have hr2 := hrPrime.two_le
  omega

#print axioms isMersenneProduct
#print axioms ratPow

end D5.S3.Arith.Mersenne.KrizekSigmaTauRationalPowerMersenne

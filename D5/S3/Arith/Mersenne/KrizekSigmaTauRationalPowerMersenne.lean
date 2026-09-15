/- GID: D5/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   generality: I
   mirror-B: D5/B/S3/Arith/Mersenne/KrizekSigmaTauRationalPowerMersenne
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.NumberTheory.Multiplicity]
   utility: none
   digest: Krizek's sigma-tau rational powers are exactly squarefree Mersenne-prime products. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Multiplicity

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

/-- The classical Sivaramakrishnan-Shallit classification, proved here as a prerequisite. -/
private theorem mersenne_product_of_sigma_tau_pow_two (n c d : ℕ) (hn : 0 < n)
    (htau : σ 0 n = 2 ^ c) (hsigma : σ 1 n = 2 ^ d) :
    isMersenneProduct n := by
  have hn0 : n ≠ 0 := hn.ne'
  have hcard : σ 0 n = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
    rw [sigma_zero_apply, Nat.card_divisors hn0]
  have exponent_one (p : ℕ) (hpMem : p ∈ n.primeFactors) : n.factorization p = 1 := by
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hePos : 0 < n.factorization p :=
      hpPrime.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hpMem)
    have heTau : n.factorization p + 1 ∣ σ 0 n := by
      rw [hcard]
      exact Finset.dvd_prod_of_mem (fun r : ℕ => n.factorization r + 1) hpMem
    rw [htau] at heTau
    obtain ⟨h, _hhc, hePow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp heTau
    have hhPos : 0 < h := by
      by_contra hh
      have : h = 0 := by omega
      subst h
      simp only [pow_zero] at hePow
      omega
    let e := n.factorization p
    let G := ∑ i ∈ Finset.range (e + 1), p ^ i
    have hGsigma : G ∣ σ 1 n := by
      rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
      have hfactor :
          (∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) ∣
            ∏ r ∈ n.primeFactors,
              ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1) :=
        Finset.dvd_prod_of_mem
          (fun r : ℕ => ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1)) hpMem
      simpa only [G, e, mul_one] using hfactor
    rw [hsigma] at hGsigma
    obtain ⟨j, _hjd, hGPow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hGsigma
    have hsmall : 1 + p ≤ G := by
      have he2 : 2 ≤ e + 1 := by dsimp only [e]; omega
      have hle := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono he2)
        (fun _ _ _ => Nat.zero_le _)
        (f := fun i : ℕ => p ^ i)
      simpa [G, Finset.sum_range_succ] using hle
    have hG1 : 1 < G := by
      have hp2 := hpPrime.two_le
      omega
    have hjPos : 0 < j := by
      by_contra hj
      have : j = 0 := by omega
      subst j
      simp only [pow_zero] at hGPow
      omega
    have hpNeTwo : p ≠ 2 := by
      intro hpTwo
      subst p
      have htwoG : 2 ∣ G := by
        rw [hGPow]
        exact dvd_pow_self 2 hjPos.ne'
      have hGzero : (G : ZMod 2) = 0 :=
        (ZMod.natCast_eq_zero_iff G 2).mpr htwoG
      have hcast : (G : ZMod 2) = 1 := by
        simp only [G, Nat.cast_sum, Nat.cast_pow]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i hi hi0
          have hbase : ((2 : ℕ) : ZMod 2) = 0 :=
            (ZMod.natCast_eq_zero_iff 2 2).mpr dvd_rfl
          rw [hbase, zero_pow hi0]
        · simp [e]
      have hOneCast : ((1 : ℕ) : ZMod 2) = 0 := by
        simpa only [Nat.cast_one] using hcast.symm.trans hGzero
      exact Nat.prime_two.not_dvd_one ((ZMod.natCast_eq_zero_iff 1 2).mp hOneCast)
    have hpOdd : Odd p := hpPrime.odd_of_ne_two hpNeTwo
    by_contra heNeOne
    have hh2 : 2 ≤ h := by
      by_contra hh
      have : h = 1 := by omega
      subst h
      simp only [pow_one] at hePow
      omega
    have hfourExp : 4 ∣ e + 1 := by
      have hpowDvd : 2 ^ 2 ∣ 2 ^ h := pow_dvd_pow 2 hh2
      rw [hePow]
      simpa using hpowDvd
    let G4 := ∑ i ∈ Finset.range 4, p ^ i
    have hG4divG : G4 ∣ G := by
      have hpowDiv : p ^ 4 - 1 ∣ p ^ (e + 1) - 1 :=
        Nat.pow_sub_one_dvd_pow_sub_one p hfourExp
      have h4Geom : G4 * (p - 1) = p ^ 4 - 1 := by
        exact geom_sum_mul_of_one_le hpPrime.one_le 4
      have heGeom : G * (p - 1) = p ^ (e + 1) - 1 := by
        exact geom_sum_mul_of_one_le hpPrime.one_le (e + 1)
      rw [← h4Geom, ← heGeom] at hpowDiv
      exact (mul_dvd_mul_iff_right (Nat.sub_ne_zero_of_lt hpPrime.one_lt)).mp hpowDiv
    have hpSqDivG4 : p ^ 2 + 1 ∣ G4 := by
      have hG4 : G4 = (p + 1) * (p ^ 2 + 1) := by
        norm_num [G4, Finset.sum_range_succ]
        ring
      rw [hG4]
      exact dvd_mul_left _ _
    have hpSqDivPow : p ^ 2 + 1 ∣ 2 ^ j := by
      rw [← hGPow]
      exact hpSqDivG4.trans hG4divG
    obtain ⟨k, _hkj, hpSqPow⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hpSqDivPow
    have hk2 : 2 ≤ k := by
      by_contra hk
      interval_cases k <;> norm_num at hpSqPow <;> nlinarith [hpPrime.two_le]
    have hfourDvd : 4 ∣ p ^ 2 + 1 := by
      rw [hpSqPow]
      have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
      simpa using this
    have hpModTwo : p % 2 = 1 := hpPrime.eq_two_or_odd.resolve_left hpNeTwo
    rcases Nat.odd_mod_four_iff.mp hpModTwo with hpModFour | hpModFour
    · have hmod : (p ^ 2 + 1) % 4 = 2 := by
        simp [pow_two, Nat.add_mod, Nat.mul_mod, hpModFour]
      exact (by simpa [Nat.dvd_iff_mod_eq_zero, hmod] using hfourDvd)
    · have hmod : (p ^ 2 + 1) % 4 = 2 := by
        simp [pow_two, Nat.add_mod, Nat.mul_mod, hpModFour]
      exact (by simpa [Nat.dvd_iff_mod_eq_zero, hmod] using hfourDvd)
  refine ⟨n.primeFactors, ?_, ?_⟩
  · calc
      n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Nat.prod_primeFactors_pow_factorization hn0
      _ = ∏ p ∈ n.primeFactors, p := by
        apply Finset.prod_congr rfl
        intro p hpMem
        rw [exponent_one p hpMem, pow_one]
  · intro p hpMem
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have heOne := exponent_one p hpMem
    have hpSigma : σ 1 (p ^ n.factorization p) ∣ σ 1 n := by
      rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0]
      rw [sigma_one_apply_prime_pow hpPrime]
      have hfactor :
          (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) ∣
            ∏ r ∈ n.primeFactors,
              ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1) := by
        simpa only [mul_one] using
          (Finset.dvd_prod_of_mem
            (fun r : ℕ => ∑ i ∈ Finset.range (n.factorization r + 1), r ^ (i * 1)) hpMem)
      exact hfactor
    rw [sigma_one_apply_prime_pow hpPrime] at hpSigma
    have hpPlusDvd : p + 1 ∣ σ 1 n := by
      simpa [heOne, Finset.sum_range_succ, add_comm] using hpSigma
    rw [hsigma] at hpPlusDvd
    obtain ⟨k, hk, hpPow⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpPlusDvd
    refine ⟨hpPrime, k, ?_, hpPow⟩
    by_contra hk0
    have : k = 0 := by omega
    subst k
    simp only [pow_zero] at hpPow
    have hp2 := hpPrime.two_le
    omega

/-- Krizek's 2013 characterization from OEIS A046528. -/
theorem result : ∀ n : ℕ, 0 < n → (isMersenneProduct n ↔ ratPow n) := by
  intro n hn
  constructor
  · rintro ⟨S, hnS, hS⟩
    by_cases hSempty : S = ∅
    · subst S
      have hnOne : n = 1 := by simpa using hnS
      subst n
      exact ⟨1, 1, by norm_num, by norm_num, by simp⟩
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSempty
    have hprimes : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
    have hn0 : n ≠ 0 := hn.ne'
    have hprimeFactors : n.primeFactors = S := by
      rw [hnS, Nat.primeFactors_prod hprimes]
    have hfac (p : ℕ) (hpMem : p ∈ S) : n.factorization p = 1 := by
      rw [hnS, Nat.factorization_prod_apply (fun r hr => (hprimes r hr).ne_zero)]
      have hpPrime := hprimes p hpMem
      rw [Finset.sum_eq_single p]
      · exact hpPrime.factorization_self
      · intro q hq hqp
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdiv
        exact hqp ((Nat.dvd_prime_two_le (hprimes q hq) hpPrime.two_le).mp hdiv).symm
      · exact fun hp => (hp hpMem).elim
    let k : ℕ → ℕ := fun p =>
      if hp : p ∈ S then Classical.choose (hS p hp).2 else 0
    have hk_spec (p : ℕ) (hpMem : p ∈ S) :
        0 < k p ∧ p + 1 = 2 ^ k p := by
      simp only [k, dif_pos hpMem]
      exact Classical.choose_spec (hS p hpMem).2
    let A := ∑ p ∈ S, k p
    let B := S.card
    have hApos : 0 < A := by
      obtain ⟨p, hpMem⟩ := hSne
      have hkp := (hk_spec p hpMem).1
      have hle : k p ≤ ∑ r ∈ S, k r := Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) hpMem
      dsimp only [A]
      omega
    have hBpos : 0 < B := by
      dsimp only [B]
      simpa only [Finset.card_pos] using hSne
    have hsigmaPow : σ 1 n = 2 ^ A := by
      rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0,
        hprimeFactors]
      calc
        (∏ p ∈ S, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 1)) =
            ∏ p ∈ S, (p + 1) := by
              apply Finset.prod_congr rfl
              intro p hpMem
              rw [hfac p hpMem]
              simp [Finset.sum_range_succ, add_comm]
        _ = ∏ p ∈ S, 2 ^ k p := by
              apply Finset.prod_congr rfl
              intro p hpMem
              exact (hk_spec p hpMem).2
        _ = 2 ^ A := by
              rw [Finset.prod_pow_eq_pow_sum]
    have htauPow : σ 0 n = 2 ^ B := by
      rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn0,
        hprimeFactors]
      calc
        (∏ p ∈ S, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ (i * 0)) =
            ∏ _p ∈ S, 2 := by
              apply Finset.prod_congr rfl
              intro p hpMem
              rw [hfac p hpMem]
              norm_num [Finset.sum_range_succ]
        _ = 2 ^ B := by simp [B]
    refine ⟨A, B, hApos, hBpos, ?_⟩
    rw [hsigmaPow, htauPow, ← pow_mul, ← pow_mul, Nat.mul_comm A B]
  · intro hrat
    by_cases hnOne : n = 1
    · subst n
      refine ⟨∅, by simp, ?_⟩
      simp
    have hnLarge : 1 < n := by omega
    rcases hrat with ⟨a, b, ha, hb, hpow⟩
    have hsupport : ∀ r : ℕ, r.Prime → (r ∣ σ 1 n ↔ r ∣ σ 0 n) := by
      intro r hr
      constructor
      · intro hrsigma
        apply hr.dvd_of_dvd_pow
        rw [← hpow]
        exact hrsigma.trans (dvd_pow (dvd_refl (σ 1 n)) hb.ne')
      · intro hrtau
        apply hr.dvd_of_dvd_pow
        rw [hpow]
        exact hrtau.trans (dvd_pow (dvd_refl (σ 0 n)) ha.ne')
    obtain ⟨c, htauPow⟩ := tau_power_two_of_same_prime_support n hnLarge hsupport
    have hsigma0 : σ 1 n ≠ 0 := (sigma_pos 1 n hn.ne').ne'
    have hsigmaPow : σ 1 n = 2 ^ (σ 1 n).primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hsigma0
      intro r hrPrime hrSigma
      have hrTau : r ∣ σ 0 n := (hsupport r hrPrime).mp hrSigma
      rw [htauPow] at hrTau
      exact Nat.prime_eq_prime_of_dvd_pow hrPrime Nat.prime_two hrTau
    exact mersenne_product_of_sigma_tau_pow_two n c _ hn htauPow hsigmaPow

#print axioms isMersenneProduct
#print axioms ratPow
#print axioms result

end D5.S3.Arith.Mersenne.KrizekSigmaTauRationalPowerMersenne

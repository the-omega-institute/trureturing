/- GID: D5/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AffineLcmCoreArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual affine lcm families have positive Robin margins under explicit residue and additive Euler-product estimates. -/

import D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
import D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution
import D5.S3.Weil.Mertens.Third
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
The affine lcm size asymptotic is classical: Qian–Hong, arXiv:1204.5415v2,
Corollary 1.2, specialized to a=3, b=2, l=1 and m=0. The actual-family
valuation, fiber and additive-weight bridges are proved inside the result.
The residue estimates and additive Euler-product limit remain explicit premises.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter Asymptotics Real Finset MeasureTheory
open D5.S3.Arith.FibonacciAtomic.UniformDivisorWeightTransfer
open D5.S3.Arith.FibonacciAtomic.ModularDivisorWeightResolution

namespace D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins

noncomputable def affineLcm (L : ℕ) : ℕ := (range L).lcm (fun a => 3 * a + 5)
noncomputable def saturatedCore (L : ℕ) : ℕ := 3 ^ Nat.log 3 L * affineLcm L
noncomputable def shortSignature (L N : ℕ) : ℕ × (Fin L → ℕ) :=
  (N.factorization 3, fun a => N.gcd (3 * a.val + 5))
noncomputable def visibleCore (L N : ℕ) : ℕ := 3 ^ N.factorization 3 * N.gcd (affineLcm L)
noncomputable def residueTheta (r : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊y⌋₊).filter (fun p => p.Prime ∧ p % 3 = r), Real.log p
noncomputable def robinMargin (N : ℕ) : ℝ :=
  exp eulerMascheroniConstant * log (log N) - normalizedWeight N

set_option maxHeartbeats 2000000 in
theorem arithmetic (L : ℕ) (hL : 2 ≤ L) :
  0 < affineLcm L ∧ 0 < saturatedCore L ∧
  (∀ p k : ℕ, p.Prime → 1 ≤ k →
    (p ^ k ∣ affineLcm L ↔
      ((p ^ k % 3 = 1 ∧ 2 * p ^ k ≤ 3 * L + 2) ∨
       (p ^ k % 3 = 2 ∧ p ^ k ≤ 3 * L + 2)))) ∧
  (¬3 ∣ affineLcm L) ∧ (saturatedCore L).factorization 3 = Nat.log 3 L ∧
  Nat.lcmUpto L ∣ saturatedCore L ∧
  saturatedCore L ∣ Nat.lcmUpto (3 * L + 2) ∧
  visibleCore L (saturatedCore L) = saturatedCore L ∧
  (∀ N : ℕ, 0 < N →
    (shortSignature L N = shortSignature L (saturatedCore L) ↔
      ∃ t : ℕ, N = saturatedCore L * t ∧ 1 ≤ t ∧ Nat.Coprime t 3)) ∧
  (∀ N : ℕ, 0 < N → shortSignature L N = shortSignature L (saturatedCore L) →
    visibleCore L N = saturatedCore L) ∧
  (16 ≤ L → 5040 ∣ saturatedCore L) ∧
  (3 ≤ L →
    |log (saturatedCore L) -
      (residueTheta 1 (((3 * L + 2 : ℕ) : ℝ) / 2) +
        residueTheta 2 ((3 * L + 2 : ℕ) : ℝ))| ≤
      log 3 + 2 * sqrt ((3 * L + 2 : ℕ) : ℝ) * log (3 * L + 2 : ℕ)) ∧
  (3 ≤ L →
    let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
    let missing := primes.filter (fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p)
    let B : ℝ := ∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)
    let δ : ℝ := ∏ p ∈ (saturatedCore L).primeFactors,
      (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))
    normalizedWeight (saturatedCore L) = primeProduct ((3 * L + 2 : ℕ) : ℝ) * exp (-B) * δ) ∧
  (16 ≤ L →
    |(∏ p ∈ (saturatedCore L).primeFactors,
      (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))) - 1| ≤
        6 / sqrt (L : ℝ)) ∧
  (∀ x : ℝ,
    |(∏ p ∈ blockSet (3 * L + 2) x, (1 - (p : ℝ)⁻¹ ^ 2)) - 1| ≤
      4 / ((3 * L + 3 : ℕ) : ℝ)) ∧
  (3 ≤ L → ∀ x : ℝ, ((3 * L + 2 : ℕ) : ℝ) ≤ x →
    let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
    let missing := primes.filter (fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p)
    let B : ℝ := ∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)
    let δ : ℝ := ∏ p ∈ (saturatedCore L).primeFactors,
      (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))
    normalizedWeight (saturatedCore L * primeBlock (3 * L + 2) x) =
      primeProduct x * exp (-B) * δ *
        ∏ p ∈ blockSet (3 * L + 2) x, (1 - (p : ℝ)⁻¹ ^ 2) ∧
      log (primeBlock (3 * L + 2) x) =
        Chebyshev.theta x - Chebyshev.theta ((3 * L + 2 : ℕ) : ℝ)) ∧
  (∀ x : ℝ,
    0 < primeBlock (3 * L + 2) x ∧
    Nat.Coprime (saturatedCore L) (primeBlock (3 * L + 2) x) ∧
    Nat.Coprime (primeBlock (3 * L + 2) x) 3 ∧
    shortSignature L (saturatedCore L * primeBlock (3 * L + 2) x) =
      shortSignature L (saturatedCore L) ∧
    visibleCore L (saturatedCore L * primeBlock (3 * L + 2) x) = saturatedCore L ∧
    normalizedWeight (saturatedCore L * primeBlock (3 * L + 2) x) =
      normalizedWeight (saturatedCore L) *
        ∏ p ∈ blockSet (3 * L + 2) x, (1 + (p : ℝ)⁻¹) ∧
    ∀ p : ℕ, (primeBlock (3 * L + 2) x).factorization p =
      if p ∈ blockSet (3 * L + 2) x then 1 else 0) := by
  classical
  have squares (s : Finset ℕ) (N : ℕ) (hN : 1 ≤ N) (hs : ∀ p ∈ s, N ≤ p) :
      (∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 2 / (N : ℝ) := by
    have hbase : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2) := by simp
    have hshift : Summable (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + N) ^ 2) := by
      simpa only [Nat.cast_add] using (summable_nat_add_iff N).mpr hbase
    calc
      (∑ p ∈ s, (1 : ℝ) / (p : ℝ) ^ 2) =
          ∑ j ∈ s.image (fun p => p - N), (1 : ℝ) / ((j : ℝ) + N) ^ 2 := by
        rw [Finset.sum_image]
        · apply sum_congr rfl
          intro p hp
          rw [← Nat.cast_add, Nat.sub_add_cancel (hs p hp)]
        · intro p hp q hq heq
          have hpN := hs p hp
          have hqN := hs q hq
          dsimp only at heq
          omega
      _ ≤ ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + N) ^ 2 :=
        Summable.sum_le_tsum _ (fun j _ => by positivity) hshift
      _ ≤ 2 / (N : ℝ) := Mertens.sum_one_div_sq_le (by exact_mod_cast hN)
  have hQ0 : affineLcm L ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro a ha
    omega
  have occurrence (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
      p ^ k ∣ affineLcm L ↔ ∃ a < L, p ^ k ∣ 3 * a + 5 := by
    rw [hp.pow_dvd_iff_le_factorization hQ0]
    rw [affineLcm, Finset.factorization_lcm (by intros; omega)]
    rw [Finset.le_sup_iff (by omega : 0 < k)]
    simp only [mem_range]
    apply exists_congr
    intro a
    apply and_congr_right
    intro ha
    exact (hp.pow_dvd_iff_le_factorization (by omega : 3 * a + 5 ≠ 0)).symm
  have encode (n : ℕ) (hn : 5 ≤ n) (hnm : n ≤ 3 * L + 2) (hr : n % 3 = 2) :
      ∃ a < L, 3 * a + 5 = n := by
    refine ⟨n / 3 - 1, ?_, ?_⟩ <;> omega
  have criterion : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      (p ^ k ∣ affineLcm L ↔
        ((p ^ k % 3 = 1 ∧ 2 * p ^ k ≤ 3 * L + 2) ∨
         (p ^ k % 3 = 2 ∧ p ^ k ≤ 3 * L + 2))) := by
    intro p k hp hk
    rw [occurrence p k hp hk]
    have hd : 2 ≤ p ^ k := by
      calc
        2 ≤ p := hp.two_le
        _ = p ^ 1 := by simp
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    constructor
    · rintro ⟨a, ha, b, hb⟩
      have hseed : 3 * a + 5 ≤ 3 * L + 2 := by omega
      have hmod : (p ^ k % 3) * (b % 3) % 3 = 2 := by
        rw [← Nat.mul_mod, ← hb]
        omega
      have hdr : p ^ k % 3 < 3 := Nat.mod_lt _ (by decide)
      have hbr : b % 3 < 3 := Nat.mod_lt _ (by decide)
      have hbpos : 1 ≤ b := by nlinarith [Nat.zero_le (p ^ k)]
      have hdne : p ^ k % 3 ≠ 0 := by
        intro hz
        simp [hz] at hmod
      rcases (by omega : p ^ k % 3 = 1 ∨ p ^ k % 3 = 2) with h | h
      · left
        have hb2 : 2 ≤ b := by simp only [h, one_mul, Nat.mod_mod] at hmod; omega
        refine ⟨h, ?_⟩
        rw [hb] at hseed
        nlinarith
      · right
        refine ⟨h, ?_⟩
        rw [hb] at hseed
        nlinarith
    · rintro (⟨hr, hm⟩ | ⟨hr, hm⟩)
      · have h4 : 4 ≤ p ^ k := by omega
        obtain ⟨a, ha, heq⟩ := encode (2 * p ^ k) (by omega) hm (by omega)
        exact ⟨a, ha, heq ▸ dvd_mul_left (p ^ k) 2⟩
      · by_cases h2 : p ^ k = 2
        · refine ⟨1, by omega, ?_⟩
          simp [h2]
        · have h5 : 5 ≤ p ^ k := by omega
          obtain ⟨a, ha, heq⟩ := encode (p ^ k) h5 hm hr
          exact ⟨a, ha, heq ▸ dvd_rfl⟩
  have hQ3 : ¬3 ∣ affineLcm L := by
    simpa using (criterion 3 1 Nat.prime_three (by decide)).not.mpr (by simp)
  have hQcop : Nat.Coprime (affineLcm L) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hQ3).symm
  have hA0 : saturatedCore L ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (by decide)) hQ0
  have hQdvd : affineLcm L ∣ saturatedCore L := dvd_mul_left _ _
  have hpowdvd : 3 ^ Nat.log 3 L ∣ saturatedCore L := dvd_mul_right _ _
  have hv3 : (saturatedCore L).factorization 3 = Nat.log 3 L := by
    rw [saturatedCore, Nat.factorization_mul (pow_ne_zero _ (by decide)) hQ0]
    simp [Nat.prime_three.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hQ3]
  have hQupper : affineLcm L ∣ Nat.lcmUpto (3 * L + 2) := by
    apply Finset.lcm_dvd
    intro a ha
    apply Finset.dvd_lcm (f := id)
    simp only [mem_range] at ha
    simp only [mem_Icc]
    omega
  have hAupper : saturatedCore L ∣ Nat.lcmUpto (3 * L + 2) := by
    apply (hQcop.symm.pow_left (Nat.log 3 L)).mul_dvd_of_dvd_of_dvd
    · apply Finset.dvd_lcm (f := id)
      have hpow := Nat.pow_log_le_self 3 (by omega : L ≠ 0)
      simp only [mem_Icc]
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      · omega
    · exact hQupper
  have hsmallPower (p k : ℕ) (hp : p.Prime) (hpk : p ^ k ≤ L) :
      p ^ k ∣ saturatedCore L := by
    by_cases hk : k = 0
    · simp [hk]
    by_cases hp3 : p = 3
    · subst p
      apply dvd_trans (pow_dvd_pow 3 (Nat.le_log_of_pow_le (by decide) hpk)) hpowdvd
    · have hnot3 : ¬3 ∣ p ^ k := by
        intro h
        exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      have hres0 : p ^ k % 3 ≠ 0 := by
        simpa only [Nat.dvd_iff_mod_eq_zero] using hnot3
      have hreslt : p ^ k % 3 < 3 := Nat.mod_lt _ (by decide)
      apply dvd_trans ((criterion p k hp (by omega)).mpr ?_) hQdvd
      rcases (by omega : p ^ k % 3 = 1 ∨ p ^ k % 3 = 2) with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨h, by omega⟩
  have hAlower : Nat.lcmUpto L ∣ saturatedCore L := by
    apply Finset.lcm_dvd
    intro n hn
    obtain ⟨hn1, hnL⟩ := mem_Icc.mp hn
    apply (Nat.dvd_iff_prime_pow_dvd_dvd (saturatedCore L) n).mpr
    intro p k hp hpk
    exact hsmallPower p k hp ((Nat.le_of_dvd (by omega) hpk).trans hnL)
  have hAcore : visibleCore L (saturatedCore L) = saturatedCore L := by
    rw [visibleCore, hv3, Nat.gcd_eq_right hQdvd]
    rfl
  have hseed (a : Fin L) : 3 * a.val + 5 ∣ saturatedCore L :=
    (Finset.dvd_lcm (mem_range.mpr a.isLt)).trans hQdvd
  have hsig (N : ℕ) (hN : 0 < N) :
      shortSignature L N = shortSignature L (saturatedCore L) ↔
        ∃ t : ℕ, N = saturatedCore L * t ∧ 1 ≤ t ∧ Nat.Coprime t 3 := by
    constructor
    · intro hs
      have hv : N.factorization 3 = Nat.log 3 L := by
        have he := congrArg Prod.fst hs
        exact he.trans hv3
      have hNdvdQ : affineLcm L ∣ N := by
        apply Finset.lcm_dvd
        intro a ha
        let af : Fin L := ⟨a, mem_range.mp ha⟩
        have he := congrFun (congrArg Prod.snd hs) af
        change N.gcd (3 * a + 5) = (saturatedCore L).gcd (3 * a + 5) at he
        rw [Nat.gcd_eq_right (hseed af)] at he
        exact Nat.gcd_eq_right_iff_dvd.mp he
      have hNpow : 3 ^ Nat.log 3 L ∣ N := by
        rw [← hv]
        exact Nat.ordProj_dvd N 3
      have hAN : saturatedCore L ∣ N :=
        (hQcop.symm.pow_left (Nat.log 3 L)).mul_dvd_of_dvd_of_dvd hNpow hNdvdQ
      obtain ⟨t, ht⟩ := hAN
      have ht0 : t ≠ 0 := by intro hz; simp [hz] at ht; omega
      have hvt : t.factorization 3 = 0 := by
        rw [ht, Nat.factorization_mul hA0 ht0, Finsupp.add_apply, hv3] at hv
        omega
      have hct : Nat.Coprime t 3 := by
        apply (Nat.prime_three.coprime_iff_not_dvd.mpr ?_).symm
        intro hd
        have := (Nat.prime_three.dvd_iff_one_le_factorization ht0).mp hd
        omega
      exact ⟨t, ht, Nat.one_le_iff_ne_zero.mpr ht0, hct⟩
    · rintro ⟨t, rfl, ht, hct⟩
      have ht0 : t ≠ 0 := by omega
      have hvt : t.factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (Nat.prime_three.coprime_iff_not_dvd.mp hct.symm)
      apply Prod.ext
      · simp [shortSignature, Nat.factorization_mul hA0 ht0, hvt]
      · funext a
        simp only [shortSignature]
        rw [Nat.gcd_eq_right ((hseed a).trans (dvd_mul_right _ _)),
          Nat.gcd_eq_right (hseed a)]
  have hcore (N : ℕ) (hN : 0 < N)
      (hs : shortSignature L N = shortSignature L (saturatedCore L)) :
      visibleCore L N = saturatedCore L := by
    obtain ⟨t, rfl, ht, hct⟩ := (hsig N hN).mp hs
    have ht0 : t ≠ 0 := by omega
    have hvt : t.factorization 3 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (Nat.prime_three.coprime_iff_not_dvd.mp hct.symm)
    rw [visibleCore, Nat.factorization_mul hA0 ht0, Finsupp.add_apply, hvt,
      add_zero, hv3, Nat.gcd_eq_right (hQdvd.trans (dvd_mul_right _ _))]
    rfl
  have h5040 (h16 : 16 ≤ L) : 5040 ∣ saturatedCore L := by
    have hd : 5040 ∣ Nat.lcmUpto 16 := by decide +kernel
    apply hd.trans (dvd_trans ?_ hAlower)
    apply Finset.lcm_mono
    intro n hn
    simp only [mem_Icc] at hn ⊢
    omega
  have hAprimemax (p : ℕ) (hp : p.Prime) (hd : p ∣ saturatedCore L) : p ≤ 3 * L + 2 := by
    have hmem := hp.mem_primeFactors (hd.trans hAupper) (Nat.lcmUpto_ne_zero (3 * L + 2))
    rw [Nat.primeFactors_lcmUpto] at hmem
    exact Nat.le_of_mem_primesLE hmem
  have block (x : ℝ) :
      0 < primeBlock (3 * L + 2) x ∧
      Nat.Coprime (saturatedCore L) (primeBlock (3 * L + 2) x) ∧
      Nat.Coprime (primeBlock (3 * L + 2) x) 3 ∧
      shortSignature L (saturatedCore L * primeBlock (3 * L + 2) x) =
        shortSignature L (saturatedCore L) ∧
      visibleCore L (saturatedCore L * primeBlock (3 * L + 2) x) = saturatedCore L ∧
      normalizedWeight (saturatedCore L * primeBlock (3 * L + 2) x) =
        normalizedWeight (saturatedCore L) *
          ∏ p ∈ blockSet (3 * L + 2) x, (1 + (p : ℝ)⁻¹) ∧
      ∀ p : ℕ, (primeBlock (3 * L + 2) x).factorization p =
        if p ∈ blockSet (3 * L + 2) x then 1 else 0 := by
    have members (p : ℕ) (hp : p ∈ blockSet (3 * L + 2) x) :
        p.Prime ∧ 3 * L + 2 < p := by
      obtain ⟨hi, hprime⟩ := mem_filter.mp hp
      exact ⟨hprime, (mem_Ioc.mp hi).1⟩
    have hTpos : 0 < primeBlock (3 * L + 2) x := by
      exact Finset.prod_pos (fun p hp => (members p hp).1.pos)
    have hAT : Nat.Coprime (saturatedCore L) (primeBlock (3 * L + 2) x) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro p hp
      apply ((members p hp).1.coprime_iff_not_dvd.mpr ?_).symm
      intro hd
      exact (members p hp).2.not_ge (hAprimemax p (members p hp).1 hd)
    have hT3 : Nat.Coprime (primeBlock (3 * L + 2) x) 3 := by
      apply Nat.coprime_prod_left_iff.mpr
      intro p hp
      apply (members p hp).1.coprime_iff_not_dvd.mpr
      intro hd
      have hple := Nat.le_of_dvd (by decide : 0 < (3 : ℕ)) hd
      have hpg := (members p hp).2
      omega
    have hs := (hsig (saturatedCore L * primeBlock (3 * L + 2) x)
        (Nat.mul_pos (Nat.pos_of_ne_zero hA0) hTpos)).mpr
      ⟨primeBlock (3 * L + 2) x, rfl, hTpos, hT3⟩
    have hc := hcore _ (Nat.mul_pos (Nat.pos_of_ne_zero hA0) hTpos) hs
    have hTweight : normalizedWeight (primeBlock (3 * L + 2) x) =
        ∏ p ∈ blockSet (3 * L + 2) x, (1 + (p : ℝ)⁻¹) := by
      rw [normalizedWeight, primeBlock,
        ArithmeticFunction.isMultiplicative_sigma.map_prod_of_prime _ (fun p hp => (members p hp).1)]
      push_cast
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hσ := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) (members p hp).1
      simp only [pow_one, sum_range_succ, range_zero, sum_empty, zero_add, pow_zero] at hσ
      rw [hσ]
      push_cast
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (members p hp).1.ne_zero
      field_simp
      ring
    have hweight : normalizedWeight (saturatedCore L * primeBlock (3 * L + 2) x) =
        normalizedWeight (saturatedCore L) *
          ∏ p ∈ blockSet (3 * L + 2) x, (1 + (p : ℝ)⁻¹) := by
      rw [← hTweight, normalizedWeight, normalizedWeight, normalizedWeight,
        ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hAT]
      push_cast
      exact mul_div_mul_comm _ _ _ _
    refine ⟨hTpos, hAT, hT3, hs, hc, hweight, ?_⟩
    intro p
    rw [primeBlock, Nat.factorization_prod (fun q hq => (members q hq).1.ne_zero)]
    rw [Finsupp.finsetSum_apply]
    have he (q : ℕ) (hq : q ∈ blockSet (3 * L + 2) x) :
        q.factorization p = if q = p then 1 else 0 := by
      rw [(members q hq).1.factorization]
      simp [Finsupp.single_apply, eq_comm]
    rw [Finset.sum_congr rfl he]
    simp [Finsupp.single_apply, eq_comm]
  have support (hL3 : 3 ≤ L) :
      (saturatedCore L).primeFactors =
        ((Ioc 0 (3 * L + 2)).filter Nat.Prime).filter
          (fun p => ¬(p % 3 = 1 ∧ 3 * L + 2 < 2 * p)) := by
    let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
    let bad : ℕ → Prop := fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p
    ext p
    constructor
    · intro hpA
      have hp := Nat.prime_of_mem_primeFactors hpA
      have hd := Nat.dvd_of_mem_primeFactors hpA
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.pos, hAprimemax p hp hd⟩, hp⟩, ?_⟩
      rintro ⟨hr, hgt⟩
      change p ∣ 3 ^ Nat.log 3 L * affineLcm L at hd
      rcases hp.dvd_mul.mp hd with hd3 | hdQ
      · have heq := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd3)
        simp [heq] at hr
      · have hs := (criterion p 1 hp (by decide)).mp (by simpa using hdQ)
        simp only [pow_one] at hs
        rcases hs with ⟨hres, hle⟩ | ⟨hres, hle⟩ <;> omega
    · intro hpS
      obtain ⟨hpP, hnot⟩ := mem_filter.mp hpS
      obtain ⟨hi, hp⟩ := mem_filter.mp hpP
      obtain ⟨hp0, hpm⟩ := mem_Ioc.mp hi
      apply hp.mem_primeFactors _ hA0
      by_cases hp3 : p = 3
      · subst p
        have he : 1 ≤ Nat.log 3 L := Nat.le_log_of_pow_le (by decide) (by simpa using hL3)
        exact (pow_dvd_pow 3 he).trans hpowdvd
      · have hr0 : p % 3 ≠ 0 := by
          intro hr
          exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
            (Nat.dvd_iff_mod_eq_zero.mpr hr)).symm
        have hrlt := Nat.mod_lt p (by decide : 0 < (3 : ℕ))
        have hdQ : p ^ 1 ∣ affineLcm L := (criterion p 1 hp (by decide)).mpr (by
          simp only [pow_one]
          rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hr | hr
          · exact Or.inl ⟨hr, by omega⟩
          · exact Or.inr ⟨hr, hpm⟩)
        have hdQ' : p ∣ affineLcm L := by simpa only [pow_one] using hdQ
        exact hdQ'.trans hQdvd
  have sizeBound (hL3 : 3 ≤ L) :
      |log (saturatedCore L) -
        (residueTheta 1 (((3 * L + 2 : ℕ) : ℝ) / 2) +
          residueTheta 2 ((3 * L + 2 : ℕ) : ℝ))| ≤
        log 3 + 2 * sqrt ((3 * L + 2 : ℕ) : ℝ) * log (3 * L + 2 : ℕ) := by
    let M : ℕ := 3 * L + 2
    let P := (Ioc 0 M).filter Nat.Prime
    let S := (saturatedCore L).primeFactors
    let D := Nat.lcmUpto M
    have hS := support hL3
    change S = P.filter (fun p => ¬(p % 3 = 1 ∧ M < 2 * p)) at hS
    have hsubset : S ⊆ P := by rw [hS]; exact filter_subset _ _
    have hlow : (Ioc 0 ⌊(M : ℝ) / 2⌋₊).filter (fun p => p.Prime ∧ p % 3 = 1) =
        P.filter (fun p => p % 3 = 1 ∧ 2 * p ≤ M) := by
      ext p
      simp only [P, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hp0, hpf⟩, hp, hr⟩
        have hpr := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (M : ℝ) / 2)).mp hpf
        have hpm : 2 * p ≤ M := by
          exact_mod_cast (show 2 * (p : ℝ) ≤ (M : ℝ) by linarith)
        exact ⟨⟨⟨hp0, by omega⟩, hp⟩, hr, hpm⟩
      · rintro ⟨⟨⟨hp0, hpM⟩, hp⟩, hr, hpm⟩
        have hpmr : 2 * (p : ℝ) ≤ (M : ℝ) := by exact_mod_cast hpm
        exact ⟨⟨hp0, (Nat.le_floor_iff (by positivity)).mpr (by linarith)⟩, hp, hr⟩
    have hθ1 : residueTheta 1 ((M : ℝ) / 2) =
        ∑ p ∈ P, if p % 3 = 1 ∧ 2 * p ≤ M then log p else 0 := by
      rw [residueTheta, hlow, sum_filter]
    have hθ2 : residueTheta 2 (M : ℝ) =
        ∑ p ∈ P, if p % 3 = 2 then log p else 0 := by
      simp only [residueTheta, Nat.floor_natCast, P, sum_filter]
      apply sum_congr rfl
      intro p _
      split_ifs <;> simp_all
    have hthree : 3 ∈ P := by
      apply mem_filter.mpr
      exact ⟨mem_Ioc.mpr ⟨by decide, by dsimp [M]; omega⟩, Nat.prime_three⟩
    have hbase : (∑ p ∈ S, log (p : ℝ)) =
        residueTheta 1 ((M : ℝ) / 2) + residueTheta 2 (M : ℝ) + log 3 := by
      rw [hS, sum_filter, hθ1, hθ2]
      have hthreeSum : (∑ p ∈ P, if p = 3 then log (p : ℝ) else 0) = log 3 := by
        simp [hthree]
      rw [← hthreeSum, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro p hpP
      have hp := (mem_filter.mp hpP).2
      by_cases hp3 : p = 3
      · subst p
        norm_num
      · have hr0 : p % 3 ≠ 0 := by
          intro hr
          exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
            (Nat.dvd_iff_mod_eq_zero.mpr hr)).symm
        have hrlt := Nat.mod_lt p (by decide : 0 < (3 : ℕ))
        rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with hr | hr
        · by_cases hcut : 2 * p ≤ M <;>
            simp [hr, hp3, hcut, show (M < 2 * p) ↔ ¬2 * p ≤ M by omega]
        · simp [hr, hp3]
    have hDset : D.primeFactors = P := by
      rw [Nat.primeFactors_lcmUpto]
      ext p
      simp only [Nat.mem_primesLE, P, mem_filter, mem_Ioc]
      constructor
      · rintro ⟨hpm, hp⟩
        exact ⟨⟨hp.pos, hpm⟩, hp⟩
      · rintro ⟨⟨_, hpm⟩, hp⟩
        exact ⟨hpm, hp⟩
    have hlogA : log (saturatedCore L) =
        ∑ p ∈ S, ((saturatedCore L).factorization p : ℝ) * log p := by
      rw [log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    have hlogD : log (D : ℝ) = ∑ p ∈ P, (D.factorization p : ℝ) * log p := by
      rw [log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization, hDset]
    have hθ : Chebyshev.theta (M : ℝ) = ∑ p ∈ P, log (p : ℝ) := by
      simp only [Chebyshev.theta, Nat.floor_natCast, P]
    have hfac (p : ℕ) : (saturatedCore L).factorization p ≤ D.factorization p :=
      (Nat.factorization_le_iff_dvd hA0 (Nat.lcmUpto_ne_zero M)).mpr hAupper p
    have hextra : 0 ≤ log (saturatedCore L) - (∑ p ∈ S, log (p : ℝ)) ∧
        log (saturatedCore L) - (∑ p ∈ S, log (p : ℝ)) ≤
          Chebyshev.psi (M : ℝ) - Chebyshev.theta (M : ℝ) := by
      rw [hlogA, ← sum_sub_distrib]
      constructor
      · apply sum_nonneg
        intro p hpS
        have hp := Nat.prime_of_mem_primeFactors hpS
        have hv := (hp.dvd_iff_one_le_factorization hA0).mp (Nat.dvd_of_mem_primeFactors hpS)
        have hvr : (1 : ℝ) ≤ (saturatedCore L).factorization p := by exact_mod_cast hv
        nlinarith [log_nonneg (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.one_le)]
      · rw [Chebyshev.psi_eq_log_lcmUpto, hlogD, hθ, ← sum_sub_distrib]
        calc
          _ ≤ ∑ p ∈ S, ((D.factorization p : ℝ) * log p - log p) := by
            apply sum_le_sum
            intro p hpS
            have hp := Nat.prime_of_mem_primeFactors hpS
            have hfr : ((saturatedCore L).factorization p : ℝ) ≤ D.factorization p := by
              exact_mod_cast hfac p
            nlinarith [log_nonneg (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.one_le)]
          _ ≤ _ := by
            apply sum_le_sum_of_subset_of_nonneg hsubset
            intro p hpP _
            have hp := (mem_filter.mp hpP).2
            have hpD := (hp.dvd_iff_one_le_factorization (Nat.lcmUpto_ne_zero M)).mp
              (Nat.dvd_of_mem_primeFactors (hDset.symm ▸ hpP))
            have hfr : (1 : ℝ) ≤ D.factorization p := by exact_mod_cast hpD
            nlinarith [log_nonneg (show (1 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.one_le)]
    have hb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
      (x := (M : ℝ)) (by dsimp [M]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) L])
    rw [hbase] at hextra
    have hp3 : 0 ≤ log (3 : ℝ) := log_nonneg (by norm_num)
    rw [abs_of_nonneg (by linarith [hextra.1])]
    linarith [le_abs_self (Chebyshev.psi (M : ℝ) - Chebyshev.theta (M : ℝ))]
  have saturation (hL3 : 3 ≤ L) :
      let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
      let missing := primes.filter (fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p)
      let B : ℝ := ∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)
      let δ : ℝ := ∏ p ∈ (saturatedCore L).primeFactors,
        (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))
      normalizedWeight (saturatedCore L) = primeProduct ((3 * L + 2 : ℕ) : ℝ) * exp (-B) * δ := by
    let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
    let bad : ℕ → Prop := fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p
    let missing := primes.filter bad
    let B : ℝ := ∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)
    let F : ℕ → ℝ := fun p => (1 - (p : ℝ)⁻¹)⁻¹
    have hS := support hL3
    change (saturatedCore L).primeFactors = primes.filter (fun p => ¬bad p) at hS
    have hFpos (p : ℕ) (hp : p ∈ primes) : 0 < F p := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))
    have hMBpos : 0 < ∏ p ∈ missing, F p :=
      Finset.prod_pos (fun p hp => hFpos p (mem_filter.mp hp).1)
    have hBprod : exp B = ∏ p ∈ missing, F p := by
      dsimp only [B]
      rw [exp_sum]
      apply Finset.prod_congr rfl
      intro p hp
      rw [exp_neg, exp_log]
      exact inv_pos.mp (hFpos p (mem_filter.mp hp).1)
    have hPprod : primeProduct ((3 * L + 2 : ℕ) : ℝ) =
        (∏ p ∈ (saturatedCore L).primeFactors, F p) * ∏ p ∈ missing, F p := by
      have ht := Finset.prod_filter_not_mul_prod_filter primes bad F
      rw [← hS] at ht
      symm
      simpa only [primeProduct, Nat.floor_natCast] using ht
    have hEuler : (∏ p ∈ (saturatedCore L).primeFactors, F p) =
        primeProduct ((3 * L + 2 : ℕ) : ℝ) * exp (-B) := by
      rw [hPprod, exp_neg, hBprod]
      exact (mul_inv_cancel_right₀ hMBpos.ne' _).symm
    have hNormalize (n : ℕ) (hn : n ≠ 0) : normalizedWeight n =
        (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹ ^ (n.factorization p + 1))) *
          ∏ p ∈ n.primeFactors, F p := by
      have hnProd : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.prod_primeFactors_pow_factorization hn
      rw [normalizedWeight, ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
      push_cast
      rw [hnProd, ← Finset.prod_div_distrib,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
      have hq : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      simp only [Nat.cast_sum, Nat.cast_pow, mul_one, F]
      rw [geom_sum_eq hp1.ne', inv_pow, pow_succ]
      field_simp [hp0, hp1.ne', hq.ne', pow_ne_zero (n.factorization p) hp0] <;> ring
    rw [hNormalize (saturatedCore L) hA0, hEuler]
    ring
  have defect (hL16 : 16 ≤ L) :
      |(∏ p ∈ (saturatedCore L).primeFactors,
        (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))) - 1| ≤
          6 / sqrt (L : ℝ) := by
    let s := (saturatedCore L).primeFactors
    let q : ℕ → ℝ := fun p => (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1)
    let J := ⌊sqrt (L : ℝ)⌋₊
    have hLR : 0 < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hsqrt : 0 < sqrt (L : ℝ) := sqrt_pos.mpr hLR
    have hmembers (p : ℕ) (hp : p ∈ s) :
        p.Prime ∧ 1 ≤ (saturatedCore L).factorization p := by
      have hpr := Nat.prime_of_mem_primeFactors hp
      exact ⟨hpr, (hpr.dvd_iff_one_le_factorization hA0).mp (Nat.dvd_of_mem_primeFactors hp)⟩
    have hsmall (p : ℕ) (hp : p ∈ s) : q p ≤ 1 / (L : ℝ) := by
      have hpr := (hmembers p hp).1
      have hlt : L < p ^ ((saturatedCore L).factorization p + 1) := by
        apply lt_of_not_ge
        intro hle
        exact Nat.pow_succ_factorization_not_dvd hA0 hpr (hsmallPower p _ hpr hle)
      have hltR : (L : ℝ) < (p : ℝ) ^ ((saturatedCore L).factorization p + 1) := by
        exact_mod_cast hlt
      dsimp only [q]
      rw [inv_pow, one_div]
      exact inv_anti₀ hLR hltR.le
    have hlarge (p : ℕ) (hp : p ∈ s) : q p ≤ 1 / (p : ℝ) ^ 2 := by
      have hpr := (hmembers p hp).1
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
      have hv := (hmembers p hp).2
      calc
        q p ≤ (p : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by positivity)
          ((inv_le_one₀ (by positivity)).mpr hp1.le) (by omega)
        _ = 1 / (p : ℝ) ^ 2 := by rw [inv_pow, one_div]
    have hsmallSum : (∑ p ∈ s.filter (fun p => p ≤ J), q p) ≤ 1 / sqrt (L : ℝ) := by
      calc
        _ ≤ ∑ p ∈ s.filter (fun p => p ≤ J), 1 / (L : ℝ) :=
          sum_le_sum (fun p hp => hsmall p (mem_filter.mp hp).1)
        _ ≤ ∑ p ∈ Ioc 0 J, 1 / (L : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            exact mem_Ioc.mpr ⟨(hmembers p (mem_filter.mp hp).1).1.pos, (mem_filter.mp hp).2⟩
          · intros
            positivity
        _ = (J : ℝ) / L := by simp [div_eq_mul_inv]
        _ ≤ sqrt (L : ℝ) / L := div_le_div_of_nonneg_right
          (Nat.floor_le (sqrt_nonneg _)) hLR.le
        _ = 1 / sqrt (L : ℝ) := by
          have hsq := sq_sqrt hLR.le
          field_simp
          nlinarith
    have hlargeSum : (∑ p ∈ s.filter (fun p => ¬p ≤ J), q p) ≤ 2 / sqrt (L : ℝ) := by
      calc
        _ ≤ ∑ p ∈ s.filter (fun p => ¬p ≤ J), 1 / (p : ℝ) ^ 2 :=
          sum_le_sum (fun p hp => hlarge p (mem_filter.mp hp).1)
        _ ≤ 2 / ((J + 1 : ℕ) : ℝ) := squares _ _ (by omega)
          (fun p hp => by have := (mem_filter.mp hp).2; omega)
        _ ≤ 2 / sqrt (L : ℝ) := by
          apply div_le_div_of_nonneg_left (by norm_num) hsqrt
          simpa only [J, Nat.cast_add, Nat.cast_one] using
            (Nat.lt_floor_add_one (sqrt (L : ℝ))).le
    have hsum : (∑ p ∈ s, q p) ≤ 3 / sqrt (L : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not s (fun p => p ≤ J)]
      calc
        _ ≤ 1 / sqrt (L : ℝ) + 2 / sqrt (L : ℝ) := add_le_add hsmallSum hlargeSum
        _ = 3 / sqrt (L : ℝ) := by ring
    have hsum0 : 0 ≤ ∑ p ∈ s, q p := sum_nonneg (fun p _ => by dsimp [q]; positivity)
    have hsum1 : (∑ p ∈ s, q p) ≤ 1 := by
      have hsq4 : 4 ≤ sqrt (L : ℝ) := (le_sqrt (by norm_num) hLR.le).mpr (by exact_mod_cast hL16)
      apply hsum.trans
      exact (div_le_iff₀ hsqrt).mpr (by linarith)
    have hprod := Finset.norm_prod_one_add_sub_one_le s (fun p => -q p)
    have hq0 (p : ℕ) : 0 ≤ q p := by dsimp [q]; positivity
    simp only [norm_neg, Real.norm_eq_abs] at hprod
    simp_rw [abs_of_nonneg (hq0 _)] at hprod
    have he := Real.abs_exp_sub_one_le (x := ∑ p ∈ s, q p) (by rwa [abs_of_nonneg hsum0])
    rw [abs_of_nonneg hsum0] at he
    have hpbound : |(∏ p ∈ s, (1 - q p)) - 1| ≤ 2 * ∑ p ∈ s, q p := by
      have hh := hprod.trans ((le_abs_self _).trans he)
      simpa only [sub_eq_add_neg, Real.norm_eq_abs] using hh
    apply hpbound.trans
    calc
      _ ≤ 2 * (3 / sqrt (L : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 6 / sqrt (L : ℝ) := by ring
  have squarefree (x : ℝ) :
      |(∏ p ∈ blockSet (3 * L + 2) x, (1 - (p : ℝ)⁻¹ ^ 2)) - 1| ≤
        4 / ((3 * L + 3 : ℕ) : ℝ) := by
    let s := blockSet (3 * L + 2) x
    let q : ℕ → ℝ := fun p => (p : ℝ)⁻¹ ^ 2
    have hq0 (p : ℕ) : 0 ≤ q p := sq_nonneg _
    have hsum : (∑ p ∈ s, q p) ≤ 2 / ((3 * L + 3 : ℕ) : ℝ) := by
      have hb := squares s (3 * L + 3) (by omega) (by
        intro p hp
        have hpm := (mem_Ioc.mp (mem_filter.mp hp).1).1
        omega)
      simpa only [q, inv_pow, one_div] using hb
    have hsum0 : 0 ≤ ∑ p ∈ s, q p := sum_nonneg (fun p _ => hq0 p)
    have hsum1 : (∑ p ∈ s, q p) ≤ 1 := by
      apply hsum.trans
      have hd : (0 : ℝ) < (3 * L + 3 : ℕ) := by positivity
      apply (div_le_iff₀ hd).mpr
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) L]
    have hprod := Finset.norm_prod_one_add_sub_one_le s (fun p => -q p)
    simp only [norm_neg, Real.norm_eq_abs] at hprod
    simp_rw [abs_of_nonneg (hq0 _)] at hprod
    have he := Real.abs_exp_sub_one_le (x := ∑ p ∈ s, q p) (by rwa [abs_of_nonneg hsum0])
    rw [abs_of_nonneg hsum0] at he
    have hpbound : |(∏ p ∈ s, (1 - q p)) - 1| ≤ 2 * ∑ p ∈ s, q p := by
      simpa only [sub_eq_add_neg, Real.norm_eq_abs] using hprod.trans ((le_abs_self _).trans he)
    apply hpbound.trans
    calc
      _ ≤ 2 * (2 / ((3 * L + 3 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 4 / ((3 * L + 3 : ℕ) : ℝ) := by ring
  have highEuler (hL3 : 3 ≤ L) (x : ℝ) (hx : ((3 * L + 2 : ℕ) : ℝ) ≤ x) :
      let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
      let missing := primes.filter (fun p => p % 3 = 1 ∧ 3 * L + 2 < 2 * p)
      let B : ℝ := ∑ p ∈ missing, -log (1 - (p : ℝ)⁻¹)
      let δ : ℝ := ∏ p ∈ (saturatedCore L).primeFactors,
        (1 - (p : ℝ)⁻¹ ^ ((saturatedCore L).factorization p + 1))
      normalizedWeight (saturatedCore L * primeBlock (3 * L + 2) x) =
        primeProduct x * exp (-B) * δ *
          ∏ p ∈ blockSet (3 * L + 2) x, (1 - (p : ℝ)⁻¹ ^ 2) ∧
        log (primeBlock (3 * L + 2) x) =
          Chebyshev.theta x - Chebyshev.theta ((3 * L + 2 : ℕ) : ℝ) := by
    let primes := (Ioc 0 (3 * L + 2)).filter Nat.Prime
    let allPrimes := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    let F : ℕ → ℝ := fun p => (1 - (p : ℝ)⁻¹)⁻¹
    have hfloor : 3 * L + 2 ≤ ⌊x⌋₊ :=
      (Nat.le_floor_iff ((by positivity : (0 : ℝ) ≤ (3 * L + 2 : ℕ)).trans hx)).mpr hx
    have hsets : allPrimes = primes ∪ blockSet (3 * L + 2) x := by
      ext p
      simp only [allPrimes, primes, blockSet, mem_filter, mem_Ioc, mem_union]
      constructor
      · rintro ⟨⟨hp0, hpx⟩, hp⟩
        by_cases hpm : p ≤ 3 * L + 2
        · exact Or.inl ⟨⟨hp0, hpm⟩, hp⟩
        · exact Or.inr ⟨⟨by omega, hpx⟩, hp⟩
      · rintro (⟨⟨hp0, hpm⟩, hp⟩ | ⟨⟨hpm, hpx⟩, hp⟩)
        · exact ⟨⟨hp0, hpm.trans hfloor⟩, hp⟩
        · exact ⟨⟨by omega, hpx⟩, hp⟩
    have hdisjoint : Disjoint primes (blockSet (3 * L + 2) x) := by
      apply Finset.disjoint_left.mpr
      intro p hp hpb
      have hple := (mem_Ioc.mp (mem_filter.mp hp).1).2
      have hpgt := (mem_Ioc.mp (mem_filter.mp hpb).1).1
      omega
    have hfpos (p : ℕ) (hp : p.Prime) : 0 < F p := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))
    have hPpos : 0 < primeProduct ((3 * L + 2 : ℕ) : ℝ) := by
      apply Finset.prod_pos
      intro p hp
      exact hfpos p (mem_filter.mp hp).2
    have hPpartition : primeProduct x = primeProduct ((3 * L + 2 : ℕ) : ℝ) *
        ∏ p ∈ blockSet (3 * L + 2) x, F p := by
      change (∏ p ∈ allPrimes, F p) = _
      rw [hsets, Finset.prod_union hdisjoint]
      simp only [primeProduct, Nat.floor_natCast]
      rfl
    have hProduct : (∏ p ∈ blockSet (3 * L + 2) x, (1 + (p : ℝ)⁻¹)) =
        (primeProduct x / primeProduct ((3 * L + 2 : ℕ) : ℝ)) *
          ∏ p ∈ blockSet (3 * L + 2) x, (1 - (p : ℝ)⁻¹ ^ 2) := by
      rw [hPpartition, mul_div_cancel_left₀ _ hPpos.ne', ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
      have hq : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      dsimp only [F]
      rw [show 1 - (p : ℝ)⁻¹ ^ 2 = (1 - (p : ℝ)⁻¹) * (1 + (p : ℝ)⁻¹) by ring,
        ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hq.ne'), one_mul]
    have hA := saturation hL3
    have hH := (block x).2.2.2.2.2.1
    constructor
    · rw [hH, hA, hProduct]
      field_simp [hPpos.ne'] <;> ring
    · have hthetaPartition : Chebyshev.theta x =
          Chebyshev.theta ((3 * L + 2 : ℕ) : ℝ) +
            ∑ p ∈ blockSet (3 * L + 2) x, log (p : ℝ) := by
        change (∑ p ∈ allPrimes, log (p : ℝ)) = _
        rw [hsets, Finset.sum_union hdisjoint]
        simp only [Chebyshev.theta, Nat.floor_natCast]
        rfl
      have hlogT : log (primeBlock (3 * L + 2) x) =
          ∑ p ∈ blockSet (3 * L + 2) x, log (p : ℝ) := by
        rw [primeBlock, Nat.cast_prod]
        exact Real.log_prod (fun p hp => by
          exact_mod_cast (mem_filter.mp hp).2.ne_zero)
      linarith
  exact ⟨Nat.pos_of_ne_zero hQ0, Nat.pos_of_ne_zero hA0, criterion, hQ3, hv3,
    hAlower, hAupper, hAcore, hsig, hcore, h5040, sizeBound, saturation, defect, squarefree, highEuler, block⟩

end D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins

#print axioms D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins.arithmetic
#check @D5.S3.Arith.FibonacciAtomic.AffineLcmRobinMargins.arithmetic

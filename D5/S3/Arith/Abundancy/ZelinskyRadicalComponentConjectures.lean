/- GID: D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures
   mirror-E: none(waiver:symbolic-asymptotic-density)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.claim; result=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.result; claim=D5/S3/Arith/Abundancy/ZelinskyRadicalComponentConjectures.claim
   digest: Primitive non-deficient integers are sparse in each radical component set. -/

import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
import D5.S3.Arith.Abundancy.ZelinskyRadicalComponentDensity
import D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
import D5.S3.Arith.Robin.PrimeFiberPropagation
import D5.S3.Weil.Mertens.Third
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic

/-! Primitive non-deficient integers and radical-component counting ratios. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures

open ZelinskyZhangDoublePrimitive
open ZelinskyZhangKLPrimitive (Deficient sig sig_prime_mul)
open D5.S3.Arith.Robin.PrimeFiberPropagation (divisorRatio edge_excess divisorRatio_pos)
open ZelinskyRadicalComponentDensity (count radicalComponentSet radicalComponentCount)

attribute [local instance] Classical.propDecidable

/-- Positive primitive non-deficient integers up to the given bound. -/
def primitiveCount (X : ℕ) : ℕ :=
  ((Icc 1 X).filter PrimitiveNonDeficient).card

private lemma deficient_iff_ratio {n : ℕ} (hn : 0 < n) :
    Deficient n ↔ divisorRatio n < 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Deficient, divisorRatio, div_lt_iff₀ hnR]

private lemma primitive_ratio_lower {n : ℕ} (hn : 0 < n)
    (hC : PrimitiveNonDeficient n) : 2 ≤ divisorRatio n := by
  exact le_of_not_gt (fun h => hC.1 ((deficient_iff_ratio hn).mpr h))

private lemma ratio_one_le {n : ℕ} (hn : 0 < n) : 1 ≤ divisorRatio n := by
  simpa [divisorRatio] using
    (D5.S3.Arith.Robin.GA2ForcedPrimeSource.abundancy_mono
      (n := 1) (L := n) (by omega) hn (one_dvd n))

private lemma primitive_prime_step {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hC : PrimitiveNonDeficient (m * p)) :
    divisorRatio (m * p) < 2 + 2 / (p : ℝ) ^ (m * p).factorization p := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hd : m ∈ (m * p).divisors :=
    Nat.mem_divisors.mpr ⟨dvd_mul_right m p, Nat.mul_ne_zero hm.ne' hp.ne_zero⟩
  have hproper : m < m * p := by nlinarith [hp.two_le]
  have hdef := (deficient_iff_ratio hm).mp (hC.2 m hd hproper)
  have hpos := divisorRatio_pos hm.ne'
  have hs : (p : ℝ) ^ m.factorization p ≤
      (ArithmeticFunction.sigma 1 (p ^ m.factorization p) : ℝ) := by
    have h := ratio_one_le (pow_pos hp.pos (m.factorization p))
    rw [divisorRatio, le_div_iff₀] at h
    · simpa only [one_mul, Nat.cast_pow] using h
    · exact_mod_cast pow_pos hp.pos (m.factorization p)
  have hfac : (m * p).factorization p = m.factorization p + 1 := by
    rw [Nat.factorization_mul hm.ne' hp.ne_zero, Finsupp.add_apply]
    simp [hp.factorization]
  have hexcess := edge_excess hp hm.ne'
  have heq : divisorRatio (m * p) = divisorRatio m *
      (1 + 1 / ((p : ℝ) * ArithmeticFunction.sigma 1 (p ^ m.factorization p))) := by
    have hdiv : divisorRatio (m * p) / divisorRatio m =
        1 + 1 / ((p : ℝ) * ArithmeticFunction.sigma 1 (p ^ m.factorization p)) :=
      by linarith
    simpa only [mul_comm] using (div_eq_iff hpos.ne').mp hdiv
  have hden : (0 : ℝ) < p * ArithmeticFunction.sigma 1 (p ^ m.factorization p) := by
    have hsig : (0 : ℝ) < ArithmeticFunction.sigma 1 (p ^ m.factorization p) := by
      exact_mod_cast (ArithmeticFunction.sigma_pos 1 (p ^ m.factorization p)
        (pow_ne_zero _ hp.ne_zero))
    exact mul_pos hpR hsig
  have hbound : 1 / ((p : ℝ) *
      ArithmeticFunction.sigma 1 (p ^ m.factorization p)) ≤
        1 / (p : ℝ) ^ (m * p).factorization p := by
    apply one_div_le_one_div_of_le (pow_pos hpR _)
    rw [hfac, pow_succ]
    nlinarith
  rw [heq]
  calc
    _ < 2 * (1 + 1 / ((p : ℝ) *
        ArithmeticFunction.sigma 1 (p ^ m.factorization p))) :=
      mul_lt_mul_of_pos_right hdef (by positivity)
    _ ≤ 2 * (1 + 1 / (p : ℝ) ^ (m * p).factorization p) := by linarith
    _ = _ := by ring

private lemma bounded_prime_powers_dvd_factorial {n T : ℕ} (hn : n ≠ 0)
    (hbound : ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ T) : n ∣ T.factorial := by
  apply (Nat.factorization_le_iff_dvd hn (Nat.factorial_ne_zero T)).mp
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hprime := Nat.prime_of_mem_primeFactors hp
    have hd : p ^ n.factorization p ∣ T.factorial :=
      Nat.dvd_factorial (pow_pos hprime.pos _) (hbound p hp)
    exact (hprime.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero T)).mp hd
  · have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp [hz]

private lemma primitive_ratio_tail {n T : ℕ} (hn : 0 < n)
    (hC : PrimitiveNonDeficient n) (hT : 0 < T) (hlarge : T.factorial < n) :
    divisorRatio n < 2 + 2 / (T : ℝ) := by
  have hex : ∃ p ∈ n.primeFactors, T < p ^ n.factorization p := by
    by_contra! h
    have hd := bounded_prime_powers_dvd_factorial hn.ne' h
    have := Nat.le_of_dvd (Nat.factorial_pos T) hd
    omega
  obtain ⟨p, hp, hpow⟩ := hex
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hprime.pos
  have hnrepr : n / p * p = n := Nat.div_mul_cancel hd
  have hstep := primitive_prime_step hm hprime (hnrepr.symm ▸ hC)
  rw [hnrepr] at hstep
  apply hstep.trans_le
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hpowR : (T : ℝ) ≤ (p : ℝ) ^ n.factorization p := by exact_mod_cast hpow.le
  have hb := one_div_le_one_div_of_le hTR hpowR
  simpa only [mul_one_div, add_comm] using
    (add_le_add_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)) 2)

private lemma ratio_prime_mul {m p : ℕ} (hp : p.Prime) (hc : m.Coprime p) :
    divisorRatio (m * p) = divisorRatio m * (1 + 1 / (p : ℝ)) := by
  rw [divisorRatio,
    D5.S3.Arith.ExponentExchange.IntegerSwap.normalized_sigma_mul hc,
    D5.S3.Factorization.ReciprocalSigmaThreshold.sigma_prime hp]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [add_div, div_self (by exact_mod_cast hp.ne_zero)]
  rfl

private lemma narrow_prime_order_impossible {m p q L : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hpL : p ≤ L) (hqL : q ≤ L) (hcp : m.Coprime p) (hcq : m.Coprime q)
    (hlo : 2 ≤ divisorRatio (m * q))
    (hhi : divisorRatio (m * p) < 2 + 1 / (L : ℝ) ^ 2) : False := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hLR : (0 : ℝ) < L := by exact_mod_cast (hp.pos.trans_le hpL)
  have hdiff : (1 : ℝ) ≤ q - p := by
    have hcast : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    linarith
  have hpLR : (p : ℝ) ≤ L := by exact_mod_cast hpL
  have hqLR : (q : ℝ) ≤ L := by exact_mod_cast hqL
  have hden : (p : ℝ) * q ≤ (L : ℝ) ^ 2 := by nlinarith
  have hgap : 1 / (L : ℝ) ^ 2 ≤ 1 / (p : ℝ) - 1 / (q : ℝ) := by
    calc
      _ ≤ 1 / ((p : ℝ) * q) :=
        one_div_le_one_div_of_le (mul_pos hpR hqR) hden
      _ ≤ ((q : ℝ) - p) / ((p : ℝ) * q) := by
        exact div_le_div_of_nonneg_right hdiff (by positivity)
      _ = _ := by field_simp
  have hA := ratio_one_le hm
  have hprod := mul_le_mul_of_nonneg_right hA
    ((show 0 ≤ 1 / (L : ℝ) ^ 2 by positivity).trans hgap)
  rw [ratio_prime_mul hp hcp] at hhi
  rw [ratio_prime_mul hq hcq] at hlo
  nlinarith

private lemma narrow_prime_unique {m p q L : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hpL : p ≤ L) (hqL : q ≤ L)
    (hcp : m.Coprime p) (hcq : m.Coprime q)
    (hplo : 2 ≤ divisorRatio (m * p))
    (hphi : divisorRatio (m * p) < 2 + 1 / (L : ℝ) ^ 2)
    (hqlo : 2 ≤ divisorRatio (m * q))
    (hqhi : divisorRatio (m * q) < 2 + 1 / (L : ℝ) ^ 2) : p = q := by
  by_contra h
  rcases lt_or_gt_of_ne h with hpq | hqp
  · exact narrow_prime_order_impossible hm hp hq hpq hpL hqL hcp hcq hqlo hphi
  · exact narrow_prime_order_impossible hm hq hp hqp hqL hpL hcq hcp hplo hqhi

private def avoiding (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)

private lemma avoiding_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    ((avoiding P X).card : ℝ) ≤
      (X : ℝ) * (∏ p ∈ P, (1 - 1 / (p : ℝ))) + (∏ p ∈ P, p).totient := by
  let Q := ∏ p ∈ P, p
  have hQ : 0 < Q := prod_pos (fun p hp => (hP p hp).pos)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcount : (avoiding P X).card ≤
      (range (X / Q + 1) ×ˢ (range Q).filter (fun r => Q.Coprime r)).card := by
    apply card_le_card_of_injOn (f := fun n => (n / Q, n % Q))
      (t := range (X / Q + 1) ×ˢ (range Q).filter (fun r => Q.Coprime r))
    · intro n hn
      obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
      have hcop : Q.Coprime n := Nat.coprime_prod_left_iff.mpr
        (fun p hp => (hP p hp).coprime_iff_not_dvd.mpr (hnP p hp))
      apply mem_product.mpr
      refine ⟨mem_range.mpr ?_, mem_filter.mpr ⟨mem_range.mpr
        (Nat.mod_lt n hQ), ?_⟩⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_Icc.mp hnI).2)
      · exact (ZMod.coprime_mod_iff_coprime n Q).mpr hcop.symm |>.symm
    · intro n hn m hm heq
      have hdiv := congrArg Prod.fst heq
      have hmod := congrArg Prod.snd heq
      nlinarith [Nat.mod_add_div n Q, Nat.mod_add_div m Q]
  have hprod : (Q.totient : ℝ) =
      Q * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have h := Nat.totient_eq_mul_prod_factors Q
    rw [show Q.primeFactors = P from Nat.primeFactors_prod hP] at h
    have hR := congrArg (fun z : ℚ => (z : ℝ)) h
    push_cast at hR
    simpa only [one_div] using hR
  have hdiv : ((X / Q : ℕ) : ℝ) ≤ (X : ℝ) / Q := Nat.cast_div_le
  have hcast : ((avoiding P X).card : ℝ) ≤
      (((X / Q : ℕ) : ℝ) + 1) * Q.totient := by
    have hcountN : (avoiding P X).card ≤ (X / Q + 1) * Q.totient := by
      simpa [Nat.totient_eq_card_coprime] using hcount
    exact_mod_cast hcountN
  calc
    _ ≤ ((X : ℝ) / Q + 1) * Q.totient := by
      exact hcast.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ = _ := by rw [hprod]; field_simp

private def primeInterval (K L : ℕ) : Finset ℕ := (Icc K L).filter Nat.Prime

private lemma full_prime_product_limit :
    Tendsto (fun L : ℕ => ∏ p ∈ Ioc 0 L with p.Prime,
      (1 - 1 / (p : ℝ))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ =>
      exp (-eulerMascheroniConstant) / log x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul
      (exp (-eulerMascheroniConstant))
  have hreal := Mertens.E₃.bound''.symm.tendsto_nhds hlim
  simpa [Function.comp_def] using hreal.comp tendsto_natCast_atTop_atTop

private lemma interval_prime_product_limit (K : ℕ) (hK : 2 ≤ K) :
    Tendsto (fun L : ℕ => ∏ p ∈ primeInterval K L,
      (1 - 1 / (p : ℝ))) atTop (𝓝 0) := by
  let A := (Ioc 0 (K - 1)).filter Nat.Prime
  let c : ℝ := ∏ p ∈ A, (1 - 1 / (p : ℝ))
  have hc : 0 < c := by
    apply prod_pos
    intro p hp
    have hpR : (1 : ℝ) < p := by
      exact_mod_cast (mem_filter.mp hp).2.one_lt
    have hi := (inv_lt_one₀ (by linarith : (0 : ℝ) < p)).mpr hpR
    rw [one_div]
    linarith
  have hlim := full_prime_product_limit.div_const c
  simp only [zero_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop K] with L hL
  have hsplit : (Ioc 0 L).filter Nat.Prime = A ∪ primeInterval K L := by
    ext p
    by_cases hprime : p.Prime
    · simp [A, primeInterval, hprime]
      omega
    · simp [A, primeInterval, hprime]
  have hdis : Disjoint A (primeInterval K L) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_Ioc.mp (mem_filter.mp hp).1).2
    have hq' := (mem_Icc.mp (mem_filter.mp hq).1).1
    omega
  rw [hsplit, prod_union hdis]
  dsimp only [c] at hc
  dsimp only [c]
  field_simp

private def narrowExtensions (X K L : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 (X / K)) ×ˢ primeInterval K L).filter (fun z =>
    z.1.Coprime z.2 ∧ 2 ≤ divisorRatio (z.1 * z.2) ∧
      divisorRatio (z.1 * z.2) < 2 + 1 / (L : ℝ) ^ 2)

private lemma narrowExtensions_card (X K L : ℕ) :
    (narrowExtensions X K L).card ≤ X / K := by
  have h : (narrowExtensions X K L).card ≤ (Icc 1 (X / K)).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro z hz
      exact (mem_product.mp (mem_filter.mp hz).1).1
    · intro a ha b hb hab
      obtain ⟨haI, hac, halo, hahi⟩ := mem_filter.mp ha
      obtain ⟨hbI, hbc, hblo, hbhi⟩ := mem_filter.mp hb
      obtain ⟨ham, hap⟩ := mem_product.mp haI
      obtain ⟨hbm, hbp⟩ := mem_product.mp hbI
      apply Prod.ext hab
      have hm : 0 < a.1 := (mem_Icc.mp ham).1
      have hp := (mem_filter.mp hap).2
      have hq := (mem_filter.mp hbp).2
      have hpL := (mem_Icc.mp (mem_filter.mp hap).1).2
      have hqL := (mem_Icc.mp (mem_filter.mp hbp).1).2
      rw [← hab] at hbc hblo hbhi
      exact narrow_prime_unique hm hp hq hpL hqL hac hbc halo hahi hblo hbhi
  simpa using h

private lemma square_mem_largeSquares {n p X K : ℕ} (hn : 0 < n) (hnX : n ≤ X)
    (hp : 0 < p) (hpK : K ≤ p) (hK : 0 < K) (hd : p ^ 2 ∣ n) :
    n ∈ StrongPseudoperfectEulerDensity.largeSquares X (K - 1) := by
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have hpX : p ≤ X := by
    have hpn := Nat.le_of_dvd hn hd
    nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) p]
  apply mem_biUnion.mpr
  refine ⟨p, mem_Icc.mpr ⟨by omega, hpX⟩, mem_image.mpr ?_⟩
  refine ⟨n / p ^ 2, mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnX⟩, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hn hd) hp2
  · exact Nat.div_mul_cancel hd

private lemma primitive_cover (X K L : ℕ) (hK : 2 ≤ K) (hKL : K ≤ L) :
    (Icc 1 X).filter PrimitiveNonDeficient ⊆
      Icc 1 (2 * L ^ 2).factorial ∪ avoiding (primeInterval K L) X ∪
        StrongPseudoperfectEulerDensity.largeSquares X (K - 1) ∪
          (narrowExtensions X K L).image (fun z => z.1 * z.2) := by
  intro n hn
  obtain ⟨hnI, hC⟩ := mem_filter.mp hn
  have hnpos := (mem_Icc.mp hnI).1
  have hnX := (mem_Icc.mp hnI).2
  by_cases hsmall : n ≤ (2 * L ^ 2).factorial
  · exact mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_Icc.mpr ⟨hnpos, hsmall⟩)))
  by_cases havoid : n ∈ avoiding (primeInterval K L) X
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _ havoid))
  have hex : ∃ p ∈ primeInterval K L, p ∣ n := by
    by_contra! h
    exact havoid (mem_filter.mpr ⟨hnI, h⟩)
  obtain ⟨p, hp, hpn⟩ := hex
  have hprime := (mem_filter.mp hp).2
  have hpK := (mem_Icc.mp (mem_filter.mp hp).1).1
  by_cases hsquare : p ^ 2 ∣ n
  · exact mem_union_left _ (mem_union_right _
      (square_mem_largeSquares hnpos hnX hprime.pos hpK (by omega) hsquare))
  have hm : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hnpos hpn) hprime.pos
  have hnrepr : n / p * p = n := Nat.div_mul_cancel hpn
  have hcop : (n / p).Coprime p := by
    apply Nat.Coprime.symm
    apply hprime.coprime_iff_not_dvd.mpr
    intro h
    apply hsquare
    simpa only [pow_two, hnrepr] using (Nat.mul_dvd_mul_right h p)
  have hmX : n / p ≤ X / K := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < K)).mpr
    calc
      n / p * K ≤ n / p * p := Nat.mul_le_mul_left _ hpK
      _ = n := hnrepr
      _ ≤ X := hnX
  have hL : 0 < L := by omega
  have htail := primitive_ratio_tail hnpos hC
    (show 0 < 2 * L ^ 2 by positivity) (by omega)
  have htail' : divisorRatio n < 2 + 1 / (L : ℝ) ^ 2 := by
    convert htail using 1
    push_cast
    field_simp
  apply mem_union_right
  apply mem_image.mpr
  refine ⟨(n / p, p), mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_Icc.mpr ⟨hm, hmX⟩, hp⟩, hcop, ?_, ?_⟩, hnrepr⟩
  · simpa only [hnrepr] using primitive_ratio_lower hnpos hC
  · simpa only [hnrepr] using htail'

private lemma primitive_count_envelope (X K L : ℕ) (hK : 2 ≤ K) (hKL : K ≤ L) :
    (primitiveCount X : ℝ) ≤
      ((2 * L ^ 2).factorial : ℝ) +
        (∏ p ∈ primeInterval K L, p).totient +
          (X : ℝ) * (∏ p ∈ primeInterval K L, (1 - 1 / (p : ℝ))) +
            3 * (X : ℝ) / K := by
  have hc := (card_le_card (primitive_cover X K L hK hKL)).trans
    (card_union_le _ _)
  have hsum : primitiveCount X ≤ (2 * L ^ 2).factorial +
      (avoiding (primeInterval K L) X).card +
        (StrongPseudoperfectEulerDensity.largeSquares X (K - 1)).card +
          (narrowExtensions X K L).card := by
    have hu := card_union_le (Icc 1 (2 * L ^ 2).factorial ∪
      avoiding (primeInterval K L) X)
        (StrongPseudoperfectEulerDensity.largeSquares X (K - 1))
    have hu' := card_union_le (Icc 1 (2 * L ^ 2).factorial)
      (avoiding (primeInterval K L) X)
    have hi := card_image_le (s := narrowExtensions X K L) (f := fun z => z.1 * z.2)
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hu'
    change ((Icc 1 X).filter PrimitiveNonDeficient).card ≤ _
    omega
  have hsumR : (primitiveCount X : ℝ) ≤ ((2 * L ^ 2).factorial : ℝ) +
      (avoiding (primeInterval K L) X).card +
        (StrongPseudoperfectEulerDensity.largeSquares X (K - 1)).card +
          (narrowExtensions X K L).card := by exact_mod_cast hsum
  have ha := avoiding_card (primeInterval K L)
    (fun p hp => (mem_filter.mp hp).2) X
  have hs := StrongPseudoperfectEulerDensity.largeSquares_card X (K - 1)
  have hKcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast (show K - 1 + 1 = K by omega)
  rw [hKcast] at hs
  have hn : ((narrowExtensions X K L).card : ℝ) ≤ (X : ℝ) / K := by
    have hnR : ((narrowExtensions X K L).card : ℝ) ≤ ((X / K : ℕ) : ℝ) := by
      exact_mod_cast narrowExtensions_card X K L
    exact hnR.trans Nat.cast_div_le
  simp only [div_eq_mul_inv, one_mul] at ha hs hn ⊢
  linarith

/-- Primitive non-deficient positive integers have natural density zero. -/
theorem primitive_density_zero :
    Tendsto (fun X : ℕ => (primitiveCount X : ℝ) / X) atTop (𝓝 0) := by
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hfour : Tendsto (fun K : ℕ => 4 / (K : ℝ)) atTop (𝓝 0) :=
    hnat.const_div_atTop 4
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp
    (hfour.eventually (gt_mem_nhds (half_pos hε)))
  let K := max 2 K₀
  have hK : 2 ≤ K := le_max_left _ _
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hKsmall : 4 / (K : ℝ) < ε / 2 := hK₀ K (le_max_right _ _)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp
    ((interval_prime_product_limit K hK).eventually
      (gt_mem_nhds (one_div_pos.mpr hKpos)))
  let L := max K L₀
  have hKL : K ≤ L := le_max_left _ _
  have hprod : (∏ p ∈ primeInterval K L, (1 - 1 / (p : ℝ))) < 1 / K :=
    hL₀ L (le_max_right _ _)
  let C : ℝ := (2 * L ^ 2).factorial + (∏ p ∈ primeInterval K L, p).totient
  have hconst : Tendsto (fun X : ℕ => C / (X : ℝ)) atTop (𝓝 0) :=
    hnat.const_div_atTop C
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (hconst.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hCX : C / (X : ℝ) < ε / 2 := hX₀ X (by omega)
  have hen := primitive_count_envelope X K L hK hKL
  have hquot : (primitiveCount X : ℝ) / X ≤
      C / X + (∏ p ∈ primeInterval K L, (1 - 1 / (p : ℝ))) + 3 / K := by
    calc
      _ ≤ (((2 * L ^ 2).factorial : ℝ) +
          (∏ p ∈ primeInterval K L, p).totient +
            (X : ℝ) * (∏ p ∈ primeInterval K L, (1 - 1 / (p : ℝ))) +
              3 * (X : ℝ) / K) / X :=
        div_le_div_of_nonneg_right hen hXpos.le
      _ = _ := by dsimp only [C]; field_simp
  have hbound : (primitiveCount X : ℝ) / X < ε := by
    have htotal : 1 / (K : ℝ) + 3 / K = 4 / K := by ring
    linarith
  simpa only [Real.dist_eq, sub_zero,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (primitiveCount X : ℝ) / X)] using hbound

private lemma subset_relative_density_zero (lam : ℝ) (hlam : 0 < lam)
    (S : Set ℕ) (hS : ∀ n ∈ S, PrimitiveNonDeficient n) :
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet lam ∩ S) X : ℝ) / radicalComponentCount lam X)
        atTop (𝓝 0) := by
  classical
  have hpositive : 0 < 1 - log 2 := by linarith [Real.log_two_lt_d9]
  have hlim : Tendsto (fun X : ℕ =>
      ((primitiveCount X : ℝ) / X) / ((radicalComponentCount lam X : ℝ) / X))
        atTop (𝓝 0) := by
    have h := primitive_density_zero.div
      (ZelinskyRadicalComponentDensity.result lam hlam) hpositive.ne'
    simp only [zero_div] at h
    apply h.congr
    intro X
    rfl
  have hupper : Tendsto (fun X : ℕ =>
      (primitiveCount X : ℝ) / radicalComponentCount lam X) atTop (𝓝 0) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    exact div_div_div_cancel_right₀ (by exact_mod_cast (by omega : X ≠ 0)) _ _
  apply squeeze_zero' (Eventually.of_forall (fun X => by positivity)) ?_ hupper
  apply Eventually.of_forall
  intro X
  have hcard : count (radicalComponentSet lam ∩ S) X ≤ primitiveCount X := by
    unfold count primitiveCount
    apply card_le_card
    intro n hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn.1, hS n hn.2.2⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

/-- Conjectures 10, 12 and 14, retaining the source's prime-set quantifiers. -/
theorem conjectures :
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    Tendsto (fun X : ℕ =>
      (count (radicalComponentSet 2 ∩ {n | PrimitiveNonDeficient n ∧ Odd n}) X : ℝ) /
        radicalComponentCount 2 X) atTop (𝓝 0) ∧
    ∀ M : Finset ℕ, M.Nonempty → (∀ p ∈ M, p.Prime) →
      Tendsto (fun X : ℕ =>
        (count (radicalComponentSet 2 ∩
          {n | PrimitiveNonDeficient n ∧ ∀ p ∈ M, ¬ p ∣ n}) X : ℝ) /
            radicalComponentCount 2 X) atTop (𝓝 0) := by
  refine ⟨subset_relative_density_zero 2 (by norm_num) _ (fun n hn => hn),
    subset_relative_density_zero 2 (by norm_num) _ (fun n hn => hn.1), ?_⟩
  intro M _hM _hprime
  exact subset_relative_density_zero 2 (by norm_num) _ (fun n hn => hn.1)

/-- The source's assertion that its set B has natural density zero. -/
def claim : Prop :=
  Tendsto (fun X : ℕ => (radicalComponentCount 2 X : ℝ) / X) atTop (𝓝 0)

/-- The positive density of B contradicts the zero-density assertion. -/
theorem result : ¬ claim := by
  intro hzero
  have hlimit := ZelinskyRadicalComponentDensity.result 2 (by norm_num)
  have heq : 1 - log (2 : ℝ) = 0 := tendsto_nhds_unique hlimit hzero
  linarith [Real.log_two_lt_d9]

end D5.S3.Arith.Abundancy.ZelinskyRadicalComponentConjectures

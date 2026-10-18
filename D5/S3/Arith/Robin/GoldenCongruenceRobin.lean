/- GID: D5/S3/Arith/Robin/GoldenCongruenceRobin
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/GoldenCongruenceRobin
   mirror-E: none(waiver:universal-inequality)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Robin/GoldenCongruenceRobin.robin_of_modEq_2241; premises=D5/S3/Arith/Robin/MertensExplicitEnvelope.prime_product_upper_effective
   digest: Strict Robin for the complete 5040 divisibility and power-congruence branch. -/

import D5.S3.Arith.Robin.ElevenSmooth
import D5.S3.Arith.Robin.GoldenResidualFive
import D5.S3.Weil.GronwallUpperEnvelope
import D5.S3.Arith.Robin.MertensExplicitEnvelope
import Mathlib.Data.Nat.Totient

/-!
For every n > 5040 with 5040 | n and 3^n = 2241 (mod n), strict Robin holds.
The same-delivery elementary Mertens envelope supplies the live new numerical
input; this theorem has no distinct-prime cardinality hypothesis. It is not
an unrestricted Robin theorem or a resolution of the Riemann hypothesis.
The ordinary restricted range is already covered by published small-valuation
Robin criteria (Hertlein and Axler). The contribution is the checked local
proof chain, not a claim of a new ordinary number-theory range.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.GoldenCongruenceRobin

open Real Finset
open D5.S3.Arith.Robin.ElevenSmooth
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.ExponentExchange.IntegerSwap
open D5.S3.Arith.RobinExponentSwap
open D5.S3.Weil.GronwallUpperEnvelope
open D5.S3.Arith.GoldenResource.GoldenCell5040SmallPrimeExclusion
open D5.S3.Arith.Robin.GoldenResidualFive
open D5.S3.Arith.Robin.MertensExplicitEnvelope

noncomputable section

private theorem sigma_totient_core_bound {n : ℕ} (h5040 : 5040 ∣ n) (hmod : Nat.ModEq n (3 ^ n) 2241) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      (2032 / 2205 : ℝ) * ((n : ℝ) / Nat.totient n) := by
  have general (m : ℕ) (hm : m ≠ 0) :
      (ArithmeticFunction.sigma 1 m : ℝ) / m ≤ (m : ℝ) / Nat.totient m := by
    have hgeom (p : ℕ) (hp : p.Prime) (a : ℕ) :
        (∑ i ∈ Finset.range (a + 1), (p : ℝ) ^ i) / (p : ℝ) ^ a ≤
          (p : ℝ) / ((p : ℝ) - 1) := by
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hpm : 0 < (p : ℝ) - 1 := by linarith
      have hpow : 0 < (p : ℝ)^a := pow_pos hp0 a
      rw [geom_sum_eq hp1.ne']
      calc
        _ ≤ (p : ℝ)^(a + 1) / (p - 1) / p^a :=
          div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hpm.le) hpow.le
        _ = _ := by rw [pow_succ]; field_simp
    have hnprod : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ)^m.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hm
    have hsprod : (ArithmeticFunction.sigma 1 m : ℝ) =
        ∏ p ∈ m.primeFactors, ∑ i ∈ Finset.range (m.factorization p + 1), (p : ℝ)^i := by
      simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
        congrArg (fun k : ℕ => (k : ℝ))
          (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
            (k := 1) hm)
    have hratio : (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
        ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
      rw [hsprod, hnprod, ← Finset.prod_div_distrib]
      exact Finset.prod_le_prod₀
        (fun p _ => div_nonneg (Finset.sum_nonneg (fun i _ => by positivity)) (by positivity))
        (fun p hp => hgeom p (Nat.prime_of_mem_primeFactors hp) _)
    have hphi : (Nat.totient m : ℝ) * (∏ p ∈ m.primeFactors, (p : ℝ)) =
        (m : ℝ) * (∏ p ∈ m.primeFactors, ((p : ℝ) - 1)) := by
      have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors m)
      push_cast at h
      have hcast : (∏ p ∈ m.primeFactors, (p - 1 : ℕ) : ℝ) =
          ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact_mod_cast Nat.cast_sub (R := ℝ) (Nat.prime_of_mem_primeFactors hp).one_lt.le
      rw [hcast] at h
      exact h
    have hprodpos : 0 < ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
      apply Finset.prod_pos
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      linarith
    have hphipos : (0 : ℝ) < Nat.totient m := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
    apply hratio.trans
    rw [Finset.prod_div_distrib]
    exact (div_le_div_iff₀ hprodpos hphipos).mpr (le_of_eq (by nlinarith only [hphi]))
  obtain ⟨a, b, r, hn, ha4, ha6, hb2, hb3, hc83⟩ :=
    D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_shape h5040 hmod
  have hn0 := (D5.S3.Arith.GoldenResource.GoldenCell5040Shape.modEq_2241_factorization
    h5040 hmod).1
  have hr0 : r ≠ 0 := by intro hz; rw [hn, hz, mul_zero] at hn0; exact hn0 rfl
  have hc : r.Coprime 210 := hc83.coprime_dvd_right (by decide)
  have h2 : r.Coprime 2 := hc.coprime_dvd_right (by decide)
  have h3 : r.Coprime 3 := hc.coprime_dvd_right (by decide)
  have h5 : r.Coprime 5 := hc.coprime_dvd_right (by decide)
  have h7 : r.Coprime 7 := hc.coprime_dvd_right (by decide)
  have hcore : (2^a * 3^b * 5 * 7).Coprime r :=
    ((((h2.pow_right a).mul_right (h3.pow_right b)).mul_right h5).mul_right h7).symm
  have hcorebound :
      (ArithmeticFunction.sigma 1 (2^a * 3^b * 5 * 7) : ℝ) /
        (2^a * 3^b * 5 * 7 : ℕ) ≤
      (2032 / 2205 : ℝ) *
        ((2^a * 3^b * 5 * 7 : ℕ) : ℝ) / Nat.totient (2^a * 3^b * 5 * 7) := by
    have cop (p q i j : ℕ) (h : p.Coprime q) : (p ^ i).Coprime (q ^ j) :=
      (h.pow_left i).pow_right j
    have hc7 : (2^a * 3^b * 5).Coprime 7 :=
      (((by decide : Nat.Coprime 2 7).pow_left a).mul_left
        ((by decide : Nat.Coprime 3 7).pow_left b)).mul_left (by decide)
    have hc5 : (2^a * 3^b).Coprime 5 :=
      ((by decide : Nat.Coprime 2 5).pow_left a).mul_left
        ((by decide : Nat.Coprime 3 5).pow_left b)
    have hc23 := cop 2 3 a b (by decide)
    have hs5 := normalized_sigma_prime_pow (by decide : Nat.Prime 5) 1
    have hs7 := normalized_sigma_prime_pow (by decide : Nat.Prime 7) 1
    norm_num [reciprocalGeomSum, Finset.sum_range_succ] at hs5 hs7
    rw [normalized_sigma_mul hc7, normalized_sigma_mul hc5,
      normalized_sigma_mul hc23, normalized_sigma_prime_pow Nat.prime_two,
      normalized_sigma_prime_pow Nat.prime_three, hs5, hs7,
      Nat.totient_mul hc7, Nat.totient_mul hc5, Nat.totient_mul hc23,
      Nat.totient_prime_pow Nat.prime_two (by omega : 0 < a),
      Nat.totient_prime_pow Nat.prime_three (by omega : 0 < b),
      Nat.totient_prime (by decide : Nat.Prime 5),
      Nat.totient_prime (by decide : Nat.Prime 7)]
    interval_cases a <;> interval_cases b <;>
      norm_num [reciprocalGeomSum, Finset.sum_range_succ]
  rw [hn, normalized_sigma_mul hcore, Nat.totient_mul hcore]
  have hprod : ((2^a * 3^b * 5 * 7 * r : ℕ) : ℝ) /
      ((Nat.totient (2^a * 3^b * 5 * 7) * Nat.totient r : ℕ) : ℝ) =
      (((2^a * 3^b * 5 * 7 : ℕ) : ℝ) / Nat.totient (2^a * 3^b * 5 * 7)) *
        ((r : ℝ) / Nat.totient r) := by
    simp only [Nat.cast_mul]
    exact mul_div_mul_comm _ _ _ _
  rw [hprod]
  calc
    _ ≤ ((2032 / 2205 : ℝ) * ((2^a * 3^b * 5 * 7 : ℕ) : ℝ) /
        Nat.totient (2^a * 3^b * 5 * 7)) * ((r : ℝ) / Nat.totient r) := by
      apply mul_le_mul hcorebound (general r hr0)
      · positivity
      · positivity
    _ = _ := by ring


private theorem large_prime_product_sharp {n : ℕ} (hn : 0 < n) {y : ℝ} (hy : 2 ≤ y) :
    (∏ p ∈ largePrimes n y, (1 - 1 / (p : ℝ))⁻¹) ≤
      exp (log n / ((y - 1) * log y)) := by
  have hy0 : 0 < y := by linarith
  have hym : 0 < y - 1 := by linarith
  have hp1 : ∀ p ∈ largePrimes n y, (1 : ℝ) < p := by
    intro p hp
    have h := (mem_filter.mp hp).2
    linarith
  have hfac : ∀ p ∈ largePrimes n y, 0 < (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    exact inv_pos.mpr (sub_pos.mpr (by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ (hp1 p hp)))
  have hpoint : ∀ p ∈ largePrimes n y,
      log ((1 - 1 / (p : ℝ))⁻¹) ≤ 1 / (y - 1) := by
    intro p hp
    have hyp := (mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := hy0.trans hyp
    have hpm : 0 < (p : ℝ) - 1 := by linarith [hp1 p hp]
    rw [one_sub_div hp0.ne', inv_div]
    calc
      _ ≤ (p : ℝ) / (p - 1) - 1 := log_le_sub_one_of_pos (div_pos hp0 hpm)
      _ = 1 / ((p : ℝ) - 1) := by rw [div_sub_one hpm.ne', sub_sub_cancel]
      _ ≤ 1 / (y - 1) := by gcongr
  apply (log_le_iff_le_exp (prod_pos hfac)).mp
  rw [log_prod (fun p hp => (hfac p hp).ne')]
  calc
    _ ≤ ((largePrimes n y).card : ℝ) * (1 / (y - 1)) := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hpoint
    _ ≤ (log n / log y) * (1 / (y - 1)) :=
      mul_le_mul_of_nonneg_right (large_prime_count_le hn hy) (by positivity)
    _ = _ := by field_simp <;> ring

private theorem omitted_small_prime_product (n : ℕ) (y : ℝ) (E : Finset ℕ)
    (hE : ∀ p ∈ E, p.Prime) (hEy : ∀ p ∈ E, (p : ℝ) ≤ y)
    (hEn : ∀ p ∈ E, ¬ p ∣ n) :
    (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y),
      (1 - 1 / (p : ℝ))⁻¹) ≤
    (∏ p ∈ Ioc (0 : ℕ) ⌊y⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹) *
      (∏ p ∈ E, (1 - 1 / (p : ℝ))) := by
  let S := n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y)
  let B := (Ioc (0 : ℕ) ⌊y⌋₊).filter Nat.Prime
  let F := fun p : ℕ => (1 - 1 / (p : ℝ))⁻¹
  let G := fun p : ℕ => (1 - 1 / (p : ℝ))
  have hpos (p : ℕ) (hp : p.Prime) : 0 < G p := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hp1)
  have hone (p : ℕ) (hp : p.Prime) : 1 ≤ F p :=
    (one_le_inv₀ (hpos p hp)).mpr (sub_le_self _ (by positivity))
  have hsub : S ∪ E ⊆ B := by
    intro p hp
    rcases mem_union.mp hp with hp | hp
    · have hs := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hs.1).pos, Nat.le_floor hs.2⟩,
        Nat.prime_of_mem_primeFactors hs.1⟩
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hE p hp).pos, Nat.le_floor (hEy p hp)⟩,
        hE p hp⟩
  have hdis : Disjoint S E := by
    apply disjoint_left.mpr
    intro p hs he
    exact hEn p he (Nat.dvd_of_mem_primeFactors (mem_filter.mp hs).1)
  have hb : (∏ p ∈ S, F p) * (∏ p ∈ E, F p) ≤ ∏ p ∈ B, F p := by
    rw [← prod_union hdis]
    exact prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => (hone p (mem_filter.mp (hsub hp)).2).trans' zero_le_one)
      (fun p hp _ => hone p (mem_filter.mp hp).2)
  have hc : (∏ p ∈ E, F p) * (∏ p ∈ E, G p) = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    exact inv_mul_cancel₀ (hpos p (hE p hp)).ne'
  have hg : 0 ≤ ∏ p ∈ E, G p := prod_nonneg (fun p hp => (hpos p (hE p hp)).le)
  have h := mul_le_mul_of_nonneg_right hb hg
  rw [mul_assoc, hc, mul_one] at h
  exact h

private theorem loglog_counterexample_size {n : ℕ} (hn : 5040 * 47 ^ 36 ≤ n) :
    (499 / 100 : ℝ) < Real.log (Real.log (n : ℝ)) := by
  have hb : (499 / 100 : ℝ) < Real.log (Real.log ((2 : ℝ)^212 * (6 / 5))) :=
    loglog_of ((2 : ℝ)^212 * (6 / 5)) (3678 / 25) (499 / 100)
      (6 / 5) (1839 / 1600) 212 7
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPartial, Finset.sum_range_succ])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPartial, Finset.sum_range_succ]) (by norm_num)
  have hc : ((2 : ℝ)^212 * (6 / 5)) ≤ (n : ℝ) := by
    apply le_trans (by norm_num : ((2 : ℝ)^212 * (6 / 5)) ≤
      (5040 * 47 ^ 36 : ℕ))
    exact_mod_cast hn
  have hp : 0 < Real.log ((2 : ℝ)^212 * (6 / 5)) := Real.log_pos (by norm_num)
  exact hb.trans_le (Real.log_le_log hp (Real.log_le_log (by positivity) hc))

private theorem excluded_prime_scalar_margin (L : ℝ) (hL : 499 / 100 ≤ L) :
    (3236010393600 / 5663533044013 : ℝ) * (1 + (347 / 500) / L) *
      Real.exp ((241 / 100) / (L + 69 / 100)) < 1 := by
  have hp : 0 < L := by linarith
  have hratio : 1 + (347 / 500 : ℝ) / L ≤ 1 + (347 / 500) / (499 / 100) := by
    gcongr
  have harg : (241 / 100 : ℝ) / (L + 69 / 100) ≤ 241 / 568 := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 241 / 100)
      (by norm_num : (0 : ℝ) < 499 / 100 + 69 / 100)
      (show (499 / 100 : ℝ) + 69 / 100 ≤ L + 69 / 100 by linarith)
    norm_num at h
    exact h
  have hexp : Real.exp (241 / 568 : ℝ) < 153 / 100 := by
    have hb := (log_expansion_remainder_bound (y := (153 / 100 : ℝ))
      (by norm_num) (by norm_num) 4).1
    norm_num [logRemainder, atanhParameter, atanhPartial, Finset.sum_range_succ] at hb
    have hlog : (241 / 568 : ℝ) < Real.log (153 / 100) := by linarith only [hb]
    calc
      _ < Real.exp (Real.log (153 / 100)) := Real.exp_lt_exp.mpr hlog
      _ = _ := Real.exp_log (by norm_num)
  have he := (Real.exp_le_exp.mpr harg).trans_lt hexp
  calc
    _ ≤ (3236010393600 / 5663533044013 : ℝ) *
        (1 + (347 / 500) / (499 / 100)) *
        Real.exp ((241 / 100) / (L + 69 / 100)) := by gcongr
    _ < (3236010393600 / 5663533044013 : ℝ) *
        (1 + (347 / 500) / (499 / 100)) * (153 / 100) := by gcongr
    _ < 1 := by norm_num

private theorem totient_prime_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / Nat.totient n =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have ht : (Nat.totient n : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    simpa only [one_div] using h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ht, div_mul_eq_div_mul_one_div, div_self hnR, one_mul, one_div,
    prod_inv_distrib]

/-- The complete divisibility and power-congruence branch satisfies strict Robin. -/
theorem robin_of_modEq_2241 {n : ℕ} (hn : 5040 < n) (h5040 : 5040 ∣ n)
    (hmod : Nat.ModEq n (3 ^ n) 2241) :
    (ArithmeticFunction.sigma 1 n : ℝ) / n <
      exp eulerMascheroniConstant * log (log (n : ℝ)) := by
  by_contra hnot
  have hbad := le_of_not_gt hnot
  have hsize := counterexample_size_lower_bound hn h5040 hmod hbad
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  let t : ℝ := log (n : ℝ)
  let L : ℝ := log t
  let y : ℝ := 2 * t
  let E : Finset ℕ := {11,13,17,19,23,29,31,37,41,43}
  have ht : (143 : ℝ) ≤ t := by
    have hbase : (2 : ℝ)^212 ≤ n := by
      apply le_trans (by norm_num : (2 : ℝ)^212 ≤ (5040 * 47^36 : ℕ))
      exact_mod_cast hsize
    have hlog := log_le_log (by positivity : (0 : ℝ) < 2^212) hbase
    rw [log_pow] at hlog
    norm_num at hlog
    dsimp [t]
    nlinarith [Real.log_two_gt_d9]
  have hy : 286 ≤ y := by dsimp [y]; linarith
  have hy2 : 2 ≤ y := by linarith
  have hL : 499 / 100 ≤ L := (loglog_counterexample_size hsize).le
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hy0 : 0 < y := by linarith
  have hym : 0 < y - 1 := by linarith
  have hlogy : log y = L + log 2 := by
    dsimp [y, L]
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne', add_comm]
  have hlogy0 : 0 < log y := by rw [hlogy]; positivity
  have hEp : ∀ p ∈ E, p.Prime := by decide +kernel
  have hElo : ∀ p ∈ E, 7 < p := by decide +kernel
  have hEhi : ∀ p ∈ E, p < 47 := by decide +kernel
  have hEy : ∀ p ∈ E, (p : ℝ) ≤ y := by
    intro p hp
    have hb : (p : ℝ) ≤ 47 := by exact_mod_cast (hEhi p hp).le
    linarith
  have hEn : ∀ p ∈ E, ¬p ∣ n := fun p hp =>
    modEq_2241_small_prime_not_dvd h5040 hmod (hEp p hp) (hElo p hp) (hEhi p hp)
  have hEvalue : (∏ p ∈ E, (1 - 1 / (p : ℝ))) =
      (3511517184000 / 5663533044013 : ℝ) := by norm_num [E]
  have hsmall := omitted_small_prime_product n y E hEp hEy hEn
  rw [hEvalue] at hsmall
  have hmertens := prime_product_upper_effective hy
  rw [← prod_inv_distrib] at hmertens
  have hsmall' :
      (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y),
        (1 - 1 / (p : ℝ))⁻¹) ≤
      (exp eulerMascheroniConstant * log y * exp ((19 / 10 : ℝ) / log y)) *
        (3511517184000 / 5663533044013) :=
    hsmall.trans (mul_le_mul_of_nonneg_right hmertens (by norm_num))
  have hlarge := large_prime_product_sharp hn0 hy2
  have hsplit :
      (∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹) =
      (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ y),
        (1 - 1 / (p : ℝ))⁻¹) *
      (∏ p ∈ largePrimes n y, (1 - 1 / (p : ℝ))⁻¹) := by
    simpa only [not_le, largePrimes] using
      (prod_filter_mul_prod_filter_not n.primeFactors
        (fun p : ℕ => (p : ℝ) ≤ y) (fun p => (1 - 1 / (p : ℝ))⁻¹)).symm
  have hlarge0 : 0 ≤ ∏ p ∈ largePrimes n y, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      have hpy := (mem_filter.mp hp).2
      linarith
    exact (inv_pos.mpr (sub_pos.mpr (by
      simpa only [one_div] using inv_lt_one_of_one_lt₀ hp1))).le
  have htotient : (n : ℝ) / Nat.totient n ≤
      (exp eulerMascheroniConstant * log y * exp ((19 / 10 : ℝ) / log y) *
        (3511517184000 / 5663533044013)) *
      exp (t / ((y - 1) * log y)) := by
    rw [totient_prime_product hn0, hsplit]
    exact mul_le_mul hsmall' hlarge hlarge0 (by positivity)
  have hlocal := sigma_totient_core_bound h5040 hmod
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      (3236010393600 / 5663533044013 : ℝ) * exp eulerMascheroniConstant *
        log y * exp (((19 / 10 : ℝ) + t / (y - 1)) / log y) := by
    apply (hlocal.trans (mul_le_mul_of_nonneg_left htotient (by norm_num))).trans
    apply le_of_eq
    rw [add_div, exp_add, div_mul_eq_div_mul_one_div]
    ring
  have hhalf : t / (y - 1) ≤ 51 / 100 := by
    apply (div_le_iff₀ hym).mpr
    dsimp [y]
    linarith
  have h2lo : (69 / 100 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : log (2 : ℝ) ≤ 347 / 500 := by linarith [Real.log_two_lt_d9]
  have harg : ((19 / 10 : ℝ) + t / (y - 1)) / log y ≤
      (241 / 100) / (L + 69 / 100) := by
    have hnumer : (19 / 10 : ℝ) + t / (y - 1) ≤ 241 / 100 := by linarith
    have hdenom : L + 69 / 100 ≤ log y := by rw [hlogy]; linarith
    exact (div_le_div_of_nonneg_right hnumer hlogy0.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by linarith) hdenom)
  have hlogcap : log y ≤ L * (1 + (347 / 500) / L) := by
    rw [hlogy]
    field_simp
    nlinarith
  have hratio' : (ArithmeticFunction.sigma 1 n : ℝ) / n ≤
      (exp eulerMascheroniConstant * L) *
        ((3236010393600 / 5663533044013 : ℝ) * (1 + (347 / 500) / L) *
          exp ((241 / 100) / (L + 69 / 100))) := by
    apply hratio.trans
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left hlogcap
        (by positivity : 0 ≤ (3236010393600 / 5663533044013 : ℝ) *
          exp eulerMascheroniConstant))
      (exp_le_exp.mpr harg) (exp_pos _).le (by positivity)
    convert h using 1 <;> ring
  have hstrict := mul_lt_mul_of_pos_left (excluded_prime_scalar_margin L hL)
    (mul_pos (exp_pos eulerMascheroniConstant) hL0)
  rw [mul_one] at hstrict
  exact (not_lt_of_ge hbad) (hratio'.trans_lt hstrict)

#print axioms robin_of_modEq_2241

end

end D5.S3.Arith.Robin.GoldenCongruenceRobin

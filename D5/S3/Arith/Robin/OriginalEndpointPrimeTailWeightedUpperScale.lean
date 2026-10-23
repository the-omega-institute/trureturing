/- GID: D5/S3/Arith/Robin/OriginalEndpointPrimeTailWeightedUpperScale
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalEndpointPrimeTailWeightedUpperScale
   mirror-E: none(waiver:general-analytic-results-no-numerical-evidence-artifact)
   anchors: []
   utility: none
   digest: An explicit weighted-price upper bound on the same-integer complete Euler tail at either original endpoint. -/

/-
The actual largest selected prime bounds the price. The sharp local upper
price is at most twice price times log(p), so the complete small-prime sum
is controlled by Chebyshev theta. A finite dyadic decomposition controls
the remaining reciprocal-square sum, keeping the last partial band and all
activation ties. The same integer's complete tail gains a logarithmic factor
compared with the original square-root estimate. No final Robin sign or RH
conclusion is asserted here.
-/

import D5.S3.Arith.Robin.OriginalEndpointPrimeTail
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail

private theorem upperPrice_le_two_mul_price {q : ℝ} (hq : 0 < q)
    {p : ℕ} (hp : p.Prime) :
    upperPrice q p ≤ 2 * (q * Real.log p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  let z := Real.exp (q * Real.log p)
  have hz : 1 < z := Real.one_lt_exp_iff.mpr (mul_pos hq hlogp)
  have hz0 : 0 < z := by linarith
  have hden : 0 < (p : ℝ) - 1 := by linarith
  have hnum : 0 < (p : ℝ) * z - 1 := by nlinarith
  have hprod : 1 ≤ ((p : ℝ) - 1) * z := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (p : ℝ) - 1 by linarith) hz0.le
    linarith
  have hfactor : ((p : ℝ) - 1) * z ^ 2 - ((p : ℝ) * z - 1) =
      (z - 1) * (((p : ℝ) - 1) * z - 1) := by ring
  have hsq : ((p : ℝ) * z - 1) / ((p : ℝ) - 1) ≤ z ^ 2 := by
    apply (div_le_iff₀ hden).2
    have h := mul_nonneg (sub_nonneg.mpr hz.le) (sub_nonneg.mpr hprod)
    rw [← hfactor] at h
    linarith
  have hlog := Real.log_le_log (div_pos hnum hden) hsq
  simpa [upperPrice, z, Real.log_pow] using hlog

/-- A finite subset of a dyadic prime band; no support-prefix hypothesis. -/
private theorem prime_band_inverse_sq_le {r a : ℝ} (hr : 1 < r) (hra : r ≤ a)
    (B : Finset ℕ)
    (hB : ∀ p ∈ B, p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ 2 * a) :
    (∑ p ∈ B, 1 / (p : ℝ) ^ 2) ≤
      2 * Real.log 4 / (a * Real.log r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have ha0 : 0 < a := hr0.trans_le hra
  have hlogr : 0 < Real.log r := Real.log_pos hr
  have hden : 0 < a ^ 2 * Real.log r := mul_pos (pow_pos ha0 _) hlogr
  have hsub : B ⊆ Nat.primesLE ⌊2 * a⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hB p hp).2.2, (hB p hp).1⟩
  have hlogsum : (∑ p ∈ B, Real.log p) ≤ Chebyshev.theta (2 * a) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    exact Real.log_nonneg (by
      exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have hpoint (p : ℕ) (hp : p ∈ B) :
      1 / (p : ℝ) ^ 2 ≤ Real.log p / (a ^ 2 * Real.log r) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hB p hp).1.pos
    have hpa : a ≤ (p : ℝ) := (hB p hp).2.1.le
    have hpSq : a ^ 2 ≤ (p : ℝ) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self ha0.le hpa
    have hlogs : Real.log r ≤ Real.log p :=
      Real.log_le_log hr0 (hra.trans hpa)
    calc
      1 / (p : ℝ) ^ 2 ≤ 1 / a ^ 2 :=
        one_div_le_one_div_of_le (pow_pos ha0 _) hpSq
      _ = Real.log r / (a ^ 2 * Real.log r) := by
        field_simp [ha0.ne', hlogr.ne']
      _ ≤ Real.log p / (a ^ 2 * Real.log r) :=
        (div_le_div_iff_of_pos_right hden).mpr hlogs
  calc
    (∑ p ∈ B, 1 / (p : ℝ) ^ 2) ≤
        ∑ p ∈ B, Real.log p / (a ^ 2 * Real.log r) :=
      sum_le_sum hpoint
    _ = (∑ p ∈ B, Real.log p) / (a ^ 2 * Real.log r) := by
      rw [sum_div]
    _ ≤ Chebyshev.theta (2 * a) / (a ^ 2 * Real.log r) :=
      (div_le_div_iff_of_pos_right hden).mpr hlogsum
    _ ≤ (Real.log 4 * (2 * a)) / (a ^ 2 * Real.log r) :=
      (div_le_div_iff_of_pos_right hden).mpr
        (Chebyshev.theta_le_log4_mul_x (by positivity : 0 ≤ 2 * a))
    _ = 2 * Real.log 4 / (a * Real.log r) := by
      field_simp [ha0.ne', hlogr.ne']
      <;> ring

/-- Finite induction covers the last partially filled dyadic band exactly. -/
private theorem prime_inverse_sq_dyadic {r : ℝ} (hr : 1 < r) (J : ℕ) :
    ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ r < (p : ℝ) ∧ (p : ℝ) ≤ (2 : ℝ) ^ J * r) →
      (∑ p ∈ S, 1 / (p : ℝ) ^ 2) ≤
        (2 * Real.log 4 / (r * Real.log r)) *
          ∑ j ∈ range J, (1 / (2 : ℝ)) ^ j := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hlogr : 0 < Real.log r := Real.log_pos hr
  induction J with
  | zero =>
      intro S hS
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hle : (p : ℝ) ≤ r := by simpa using (hS p hp).2.2
        exact (not_lt_of_ge hle) (hS p hp).2.1
      simp [hempty]
  | succ J ih =>
      intro S hS
      let a : ℝ := (2 : ℝ) ^ J * r
      let small := S.filter (fun p : ℕ => (p : ℝ) ≤ a)
      let large := S.filter (fun p : ℕ => a < (p : ℝ))
      have hra : r ≤ a := by
        have htwo : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
        simpa only [one_mul, a] using mul_le_mul_of_nonneg_right htwo hr0.le
      have hsmall : (∑ p ∈ small, 1 / (p : ℝ) ^ 2) ≤
          (2 * Real.log 4 / (r * Real.log r)) *
            ∑ j ∈ range J, (1 / (2 : ℝ)) ^ j := by
        apply ih small
        intro p hp
        obtain ⟨hpS, hpa⟩ := mem_filter.mp hp
        exact ⟨(hS p hpS).1, (hS p hpS).2.1, hpa⟩
      have hlarge : (∑ p ∈ large, 1 / (p : ℝ) ^ 2) ≤
          2 * Real.log 4 / (a * Real.log r) := by
        apply prime_band_inverse_sq_le hr hra large
        intro p hp
        obtain ⟨hpS, hpa⟩ := mem_filter.mp hp
        refine ⟨(hS p hpS).1, hpa, ?_⟩
        calc
          (p : ℝ) ≤ (2 : ℝ) ^ (J + 1) * r := (hS p hpS).2.2
          _ = 2 * a := by dsimp only [a]; rw [pow_succ]; ring
      have hsplit : (∑ p ∈ S, 1 / (p : ℝ) ^ 2) =
          (∑ p ∈ small, 1 / (p : ℝ) ^ 2) +
            ∑ p ∈ large, 1 / (p : ℝ) ^ 2 := by
        have h := sum_filter_add_sum_filter_not S
          (fun p : ℕ => (p : ℝ) ≤ a) (fun p : ℕ => 1 / (p : ℝ) ^ 2)
        simpa only [small, large, not_le] using h.symm
      have hscale : 2 * Real.log 4 / (a * Real.log r) =
          (2 * Real.log 4 / (r * Real.log r)) * (1 / (2 : ℝ)) ^ J := by
        dsimp only [a]
        simp only [one_div, inv_pow]
        field_simp [hr0.ne', hlogr.ne', pow_ne_zero J (by norm_num : (2 : ℝ) ≠ 0)]
        <;> ring
      calc
        (∑ p ∈ S, 1 / (p : ℝ) ^ 2) =
            (∑ p ∈ small, 1 / (p : ℝ) ^ 2) +
              ∑ p ∈ large, 1 / (p : ℝ) ^ 2 := hsplit
        _ ≤ (2 * Real.log 4 / (r * Real.log r)) *
              (∑ j ∈ range J, (1 / (2 : ℝ)) ^ j) +
            2 * Real.log 4 / (a * Real.log r) := add_le_add hsmall hlarge
        _ = (2 * Real.log 4 / (r * Real.log r)) *
              ∑ j ∈ range (J + 1), (1 / (2 : ℝ)) ^ j := by
          rw [sum_range_succ, hscale]
          ring

/-- Every original positive-price endpoint, with its complete same-integer
Euler tail and all activation ties retained, has the explicit upper scale. -/
theorem endpoint_tail_le_nine_log4_sqrt_log {q : ℝ} (hq : 0 < q) {N : ℕ}
    (hN : N = strictInteger q ∨ N = maximalInteger q)
    (hu : 4 ≤ largestPrime N) :
    tail N ≤ (9 * Real.log 4) /
      (Real.sqrt (largestPrime N : ℝ) * Real.log (largestPrime N : ℝ)) := by
  classical
  have hpositive : 1 ≤ N := by
    rcases hN with rfl | rfl
    · exact strictInteger_pos hq
    · exact (maximalInteger_spec hq).1
  let S := N.primeFactors
  let u : ℝ := largestPrime N
  let s : ℝ := Real.sqrt u
  let r : ℝ := 2 * s
  have huR : (4 : ℝ) ≤ u := by
    change (4 : ℝ) ≤ (largestPrime N : ℝ)
    exact_mod_cast hu
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
  have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
  have hsTwo : (2 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by nlinarith only [huR])
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hrOne : 1 < r := by dsimp only [r]; linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogr : 0 < Real.log r := Real.log_pos hrOne
  have hlogs : Real.log s = Real.log u / 2 := Real.log_sqrt hu0.le
  have hlogsr : Real.log s ≤ Real.log r :=
    Real.log_le_log hs0 (by dsimp only [r]; linarith)
  have hden : s * Real.log u ≤ r * Real.log r := by
    rw [hlogs] at hlogsr
    have hmul := mul_le_mul_of_nonneg_left (show Real.log u ≤ 2 * Real.log r by linarith) hs0.le
    dsimp only [r]
    nlinarith [hmul]
  have hrus : r / u = 2 / s := by
    dsimp only [r]
    rw [← hs2]
    field_simp [hs0.ne']
    <;> ring
  have hne : S.Nonempty := by
    by_contra h
    have hempty : N.primeFactors = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : largestPrime N = 0 := by simp [largestPrime, hempty]
    omega
  obtain ⟨v, hv, hvu⟩ := exists_mem_eq_sup S hne id
  have huMem : largestPrime N ∈ S := by
    have heq : largestPrime N = v := hvu
    exact heq.symm ▸ hv
  have huPrime : (largestPrime N).Prime := Nat.prime_of_mem_primeFactors huMem
  have hactive (p : ℕ) (hp : p ∈ S) : 1 ≤ N.factorization p :=
    (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
      (by omega) (Nat.dvd_of_mem_primeFactors hp)
  have hmax (p : ℕ) (hp : p ∈ S) : (p : ℝ) ≤ u := by
    change (p : ℝ) ≤ (largestPrime N : ℝ)
    exact_mod_cast (le_sup (f := id) hp : p ≤ largestPrime N)
  have hselected : q ≤ goldenLayerMarginal (largestPrime N) 1 := by
    have ha := hactive (largestPrime N) huMem
    rcases hN with rfl | rfl
    · exact ((strict_layer_iff hq huPrime (by omega : 1 ≤ (1 : ℕ))).mp ha).le
    · exact (weak_layer_iff hq huPrime (by omega : 1 ≤ (1 : ℕ))).mp ha
  have hprice : q * Real.log u ≤ Real.log (1 + 1 / u) := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv huPrime] at hselected
    exact (le_div_iff₀ hlogu).mp hselected
  have hloginc : Real.log (1 + 1 / u) ≤ 1 / u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / u by positivity)
    linarith
  have hqBound : q ≤ 1 / (u * Real.log u) := by
    calc
      q ≤ (1 / u) / Real.log u := (le_div_iff₀ hlogu).2 (hprice.trans hloginc)
      _ = 1 / (u * Real.log u) := by ring
  let small := S.filter (fun p : ℕ => (p : ℝ) ≤ r)
  let large := S.filter (fun p : ℕ => r < (p : ℝ))
  have hsmallSub : small ⊆ Nat.primesLE ⌊r⌋₊ := by
    intro p hp
    obtain ⟨hpS, hpr⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hpr, Nat.prime_of_mem_primeFactors hpS⟩
  have hsmallLog : (∑ p ∈ small, Real.log p) ≤ Chebyshev.theta r := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    apply sum_le_sum_of_subset_of_nonneg hsmallSub
    intro p hp hnot
    exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have hsmall : (∑ p ∈ small, layerTail N p) ≤
      4 * Real.log 4 / (s * Real.log u) := by
    calc
      (∑ p ∈ small, layerTail N p) ≤ ∑ p ∈ small, 2 * q * Real.log p := by
        apply sum_le_sum
        intro p hp
        have hpS := (mem_filter.mp hp).1
        have hlocal := (endpoint_local hq hN (Nat.prime_of_mem_primeFactors hpS)
          (hactive p hpS)).2.2.1
        exact hlocal.trans (by simpa only [mul_assoc] using upperPrice_le_two_mul_price hq (Nat.prime_of_mem_primeFactors hpS))
      _ = 2 * q * (∑ p ∈ small, Real.log p) := by rw [mul_sum]
      _ ≤ 2 * q * Chebyshev.theta r := mul_le_mul_of_nonneg_left hsmallLog (by positivity)
      _ ≤ 2 * q * (Real.log 4 * r) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hr0.le) (by positivity)
      _ = q * (2 * (Real.log 4 * r)) := by ring
      _ ≤ (1 / (u * Real.log u)) * (2 * (Real.log 4 * r)) :=
        mul_le_mul_of_nonneg_right hqBound (by positivity)
      _ = (2 * Real.log 4) * (r / u) / Real.log u := by
        field_simp [hu0.ne', hlogu.ne']
        <;> ring
      _ = 4 * Real.log 4 / (s * Real.log u) := by
        rw [hrus]
        field_simp [hs0.ne', hlogu.ne']
        <;> ring
  have hcover : u ≤ (2 : ℝ) ^ (largestPrime N) * r := by
    have hpow : u ≤ (2 : ℝ) ^ (largestPrime N) := by
      change (largestPrime N : ℝ) ≤ (2 : ℝ) ^ (largestPrime N)
      exact_mod_cast (largestPrime N).lt_two_pow_self.le
    have hmul : (2 : ℝ) ^ (largestPrime N) ≤ (2 : ℝ) ^ (largestPrime N) * r := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrOne.le
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (largestPrime N))
    exact hpow.trans hmul
  have hlargeSq : (∑ p ∈ large, 1 / (p : ℝ) ^ 2) ≤
      4 * Real.log 4 / (r * Real.log r) := by
    have hd := prime_inverse_sq_dyadic hrOne (largestPrime N) large (by
      intro p hp
      obtain ⟨hpS, hpr⟩ := mem_filter.mp hp
      exact ⟨Nat.prime_of_mem_primeFactors hpS, hpr, (hmax p hpS).trans hcover⟩)
    calc
      (∑ p ∈ large, 1 / (p : ℝ) ^ 2) ≤
          (2 * Real.log 4 / (r * Real.log r)) *
            ∑ j ∈ range (largestPrime N), (1 / (2 : ℝ)) ^ j := hd
      _ ≤ (2 * Real.log 4 / (r * Real.log r)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le (largestPrime N)) (by positivity)
      _ = 4 * Real.log 4 / (r * Real.log r) := by ring
  have hlarge : (∑ p ∈ large, layerTail N p) ≤
      5 * Real.log 4 / (s * Real.log u) := by
    calc
      (∑ p ∈ large, layerTail N p) ≤ ∑ p ∈ large, (5 / 4 : ℝ) / (p : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p hp
        have hpS := (mem_filter.mp hp).1
        exact (endpoint_local hq hN (Nat.prime_of_mem_primeFactors hpS)
          (hactive p hpS)).2.2.2.2
      _ = (5 / 4 : ℝ) * ∑ p ∈ large, 1 / (p : ℝ) ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p hp
        ring
      _ ≤ (5 / 4 : ℝ) * (4 * Real.log 4 / (r * Real.log r)) :=
        mul_le_mul_of_nonneg_left hlargeSq (by norm_num)
      _ = 5 * Real.log 4 / (r * Real.log r) := by ring
      _ ≤ 5 * Real.log 4 / (s * Real.log u) := by
        apply (div_le_div_iff₀ (mul_pos hr0 hlogr) (mul_pos hs0 hlogu)).2
        exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hsplit : tail N = (∑ p ∈ small, layerTail N p) + ∑ p ∈ large, layerTail N p := by
    have h := sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ r) (layerTail N)
    simpa only [tail, S, small, large, not_le] using h.symm
  change tail N ≤ (9 * Real.log 4) / (s * Real.log u)
  calc
    tail N = (∑ p ∈ small, layerTail N p) + ∑ p ∈ large, layerTail N p := hsplit
    _ ≤ 4 * Real.log 4 / (s * Real.log u) + 5 * Real.log 4 / (s * Real.log u) :=
      add_le_add hsmall hlarge
    _ = (9 * Real.log 4) / (s * Real.log u) := by ring

end D5.S3.Arith.Robin.OriginalEndpointPrimeTailWeightedUpperScale

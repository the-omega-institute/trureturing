/- GID: D5/S3/Arith/Robin/EulerLayerPhaseSeparation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/EulerLayerPhaseSeparation
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact Euler phases force occupation in the same strict integer inventory. -/

import D5.S3.Arith.GoldenLayerMarginalDecay
import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.EulerLayerPhaseSeparation

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount

lemma price_strictAnti {x y : ℝ} (hx : 1 < x) (hxy : x < y) :
    1 / (y * Real.log y) < 1 / (x * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have hlog := Real.log_lt_log hx0 hxy
  apply one_div_lt_one_div_of_lt (mul_pos hx0 hl)
  nlinarith [mul_pos (sub_pos.mpr hxy) hl]

-- Proof-local normalization of the existing Euler ratio; no new ratio identity is retained.
private lemma marginal_gt_geometric {q k : ℕ} (hq : q.Prime) (hk : 1 ≤ k) :
    (1 - (q : ℝ)⁻¹) / ((q : ℝ) ^ k * Real.log q) < goldenLayerMarginal q k := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hi0 : 0 < (q : ℝ)⁻¹ := inv_pos.mpr hq0
  have hi1 : (q : ℝ)⁻¹ < 1 := (inv_lt_one₀ hq0).mpr hq1
  have ha0 : 0 < (q : ℝ)⁻¹ ^ k := pow_pos hi0 k
  have ha1 : (q : ℝ)⁻¹ ^ k < 1 := pow_lt_one₀ hi0.le hi1 (by omega)
  have hb1 : (q : ℝ)⁻¹ ^ (k+1) < 1 := pow_lt_one₀ hi0.le hi1 (by omega)
  have hn0 : 0 < (q : ℝ) ^ k := pow_pos hq0 k
  have hl0 : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hratio := Real.one_sub_inv_le_log_of_pos
    (div_pos (sub_pos.mpr hb1) (sub_pos.mpr ha1))
  have hstrict : (1 - (q : ℝ)⁻¹) / (q : ℝ) ^ k <
      1 - (((1 - (q : ℝ)⁻¹ ^ (k+1)) / (1 - (q : ℝ)⁻¹ ^ k)))⁻¹ := by
    rw [inv_div, lt_sub_iff_add_lt, div_add_div _ _ hn0.ne' (sub_pos.mpr hb1).ne',
      div_lt_one (mul_pos hn0 (sub_pos.mpr hb1))]
    have heq : (q : ℝ) ^ k * (q : ℝ)⁻¹ ^ k = 1 := by
      rw [inv_pow, mul_inv_cancel₀ hn0.ne']
    rw [pow_succ] at *
    nlinarith [mul_pos ha0 (sub_pos.mpr hi1), mul_pos hi0 (sub_pos.mpr hi1)]
  unfold goldenLayerMarginal
  rw [div_mul_eq_div_div]
  exact (div_lt_div_iff_of_pos_right hl0).mpr (hstrict.trans_le hratio)

private lemma coefficient_one {q k : ℕ} (hq : q.Prime) (hk : 2 ≤ k) :
    1 ≤ (k : ℝ) * (1 - (q : ℝ)⁻¹) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hi : (q : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq2
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

private lemma coefficient_margin {q k : ℕ} (hq : q.Prime) (hk : 2 ≤ k)
    (hn : (16 : ℝ) ≤ (q : ℝ) ^ k) :
    (8 / 5 : ℝ) ≤ (k : ℝ) * (1 - (q : ℝ)⁻¹) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  by_cases hk4 : 4 ≤ k
  · have hi : (q : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq2
    have hk4r : (4 : ℝ) ≤ k := by exact_mod_cast hk4
    nlinarith
  · have hcases : k = 2 ∨ k = 3 := by omega
    rcases hcases with rfl | rfl
    · have hq5 : 5 ≤ q := by
        by_contra h
        have hq4 : q ≤ 4 := by omega
        interval_cases q <;> norm_num at *
      have hq5r : (5 : ℝ) ≤ q := by exact_mod_cast hq5
      have hi : (q : ℝ)⁻¹ ≤ 1 / 5 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hq5r
      norm_num
      linarith
    · have hq3 : 3 ≤ q := by
        by_contra h
        have hqeq : q = 2 := by have := hq.two_le; omega
        subst q
        norm_num at hn
      have hq3r : (3 : ℝ) ≤ q := by exact_mod_cast hq3
      have hi : (q : ℝ)⁻¹ ≤ 1 / 3 := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hq3r
      norm_num
      linarith

private lemma marginal_gt_power_price {q k : ℕ} (hq : q.Prime) (hk : 2 ≤ k) :
    1 / ((q : ℝ) ^ k * Real.log ((q : ℝ) ^ k)) < goldenLayerMarginal q k := by
  have hl : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hn : 0 < (q : ℝ) ^ k := pow_pos (by exact_mod_cast hq.pos) k
  have hcoef := coefficient_one hq hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply lt_of_le_of_lt _ (marginal_gt_geometric hq (by omega))
  rw [Real.log_pow, div_le_div_iff₀ (mul_pos hn (mul_pos hk0 hl)) (mul_pos hn hl)]
  nlinarith [mul_nonneg (mul_pos hn hl).le (sub_nonneg.mpr hcoef)]

private lemma clock_lt_of_price_lt {q k : ℕ} {tau x : ℝ}
    (_htau : 1 < tau) (hx : 1 < x)
    (hclock : 1 / (tau * Real.log tau) = goldenLayerMarginal q k)
    (hprice : 1 / (x * Real.log x) < goldenLayerMarginal q k) : tau < x := by
  by_contra h
  rcases eq_or_lt_of_le (le_of_not_gt h) with heq | hlt
  · rw [heq, hclock] at hprice
    exact lt_irrefl _ hprice
  · have ha := price_strictAnti hx hlt
    rw [hclock] at ha
    exact (not_lt_of_ge ha.le) hprice

/-- The actual prime/power margin places every higher layer of size at least sixteen
strictly before three quarters of its reference location. -/
theorem higher_layer_price_separation {q k : ℕ} (hq : q.Prime) (hk : 2 ≤ k)
    (hn : (16 : ℝ) ≤ (q : ℝ) ^ k) :
    1 / ((3 * (q : ℝ) ^ k / 4) * Real.log (3 * (q : ℝ) ^ k / 4)) <
      goldenLayerMarginal q k ∧
    (∀ tau : ℝ, 1 < tau →
      1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < 3 * (q : ℝ) ^ k / 4) := by
  let n : ℝ := (q : ℝ) ^ k
  have hn16 : 16 ≤ n := hn
  have hn0 : 0 < n := by linarith
  have hl : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hln : 0 < Real.log n := Real.log_pos (by linarith)
  have hx0 : 0 < 3 * n / 4 := by positivity
  have hlx : 0 < Real.log (3 * n / 4) := Real.log_pos (by linarith)
  have hnum : (4 / 3 : ℝ) ^ 6 < n := lt_of_lt_of_le (by norm_num) hn16
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < (4 / 3 : ℝ) ^ 6) hnum
  rw [Real.log_pow] at hlog
  have hshift : Real.log (3 * n / 4) = Real.log n - Real.log (4 / 3 : ℝ) := by
    have heq : 3 * n / 4 = n / (4 / 3) := by ring
    rw [heq, Real.log_div hn0.ne' (by norm_num)]
  have hlogs : 5 * Real.log n < 6 * Real.log (3 * n / 4) := by
    rw [hshift]
    norm_num at hlog
    linarith
  have hprice : 1 / ((3 * n / 4) * Real.log (3 * n / 4)) <
      (8 / 5 : ℝ) / (n * Real.log n) := by
    rw [div_lt_div_iff₀ (mul_pos hx0 hlx) (mul_pos hn0 hln)]
    nlinarith [mul_pos hn0 (sub_pos.mpr hlogs)]
  have hm := coefficient_margin hq hk hn
  have hnorm : (8 / 5 : ℝ) / (n * Real.log n) ≤
      (1 - (q : ℝ)⁻¹) / (n * Real.log q) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hlogn : Real.log n = (k : ℝ) * Real.log q := Real.log_pow _ _
    rw [hlogn, div_le_div_iff₀ (mul_pos hn0 (mul_pos hk0 hl)) (mul_pos hn0 hl)]
    nlinarith [mul_nonneg (mul_pos hn0 hl).le (sub_nonneg.mpr hm)]
  have hresult := hprice.trans_le hnorm |>.trans (marginal_gt_geometric hq (by omega))
  refine ⟨hresult, ?_⟩
  intro tau htau hclock
  exact clock_lt_of_price_lt htau (by dsimp [n] at hn16; linarith) hclock hresult

private lemma window_endpoint {t : ℝ} (ht : 243 ≤ t) :
    t + t^(4 / 5 : ℝ) ≤ 4 * t / 3 := by
  have ht0 : 0 < t := by linarith
  have hbase := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 243) ht
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hroot : (243 : ℝ) ^ (1 / 5 : ℝ) = 3 := by
    rw [show (243 : ℝ) = 3^5 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hroot] at hbase
  have hprod : t^(4 / 5 : ℝ) * t^(1 / 5 : ℝ) = t := by
    rw [← Real.rpow_add ht0]
    norm_num
  have hh0 := Real.rpow_pos_of_pos ht0 (4 / 5 : ℝ)
  nlinarith

/-- Both literal higher-layer window implications, together with the strict
price comparison used to occupy the same integer's reference layers. -/
theorem higher_layer_forward_window {q k : ℕ} (hq : q.Prime) (hk : 2 ≤ k)
    {t : ℝ} (ht : 243 ≤ t) :
    (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ) →
      1 / (t * Real.log t) < goldenLayerMarginal q k) ∧
    ∀ tau : ℝ, 1 < tau →
      1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < (q : ℝ) ^ k ∧
      (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ) → tau < t) ∧
      (t ≤ tau → tau ≤ t + t^(4 / 5 : ℝ) → t + t^(4 / 5 : ℝ) < (q : ℝ) ^ k) := by
  have hB := window_endpoint ht
  have ht1 : 1 < t := by linarith
  have hn1 : 1 < (q : ℝ) ^ k :=
    one_lt_pow₀ (by exact_mod_cast hq.one_lt) (by omega)
  have hphase (hn16 : (16 : ℝ) ≤ (q : ℝ) ^ k) :=
    higher_layer_price_separation hq hk hn16
  have hactive (hleft : t < (q : ℝ) ^ k)
      (hright : (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ)) :
      1 / (t * Real.log t) < goldenLayerMarginal q k := by
    have hn16 : (16 : ℝ) ≤ (q : ℝ) ^ k := by linarith
    have hx1 : 1 < 3 * (q : ℝ) ^ k / 4 := by linarith
    have hxt : 3 * (q : ℝ) ^ k / 4 ≤ t := by linarith
    rcases eq_or_lt_of_le hxt with heq | hlt
    · simpa only [heq] using (hphase hn16).1
    · exact (price_strictAnti hx1 hlt).trans (hphase hn16).1
  refine ⟨hactive, ?_⟩
  intro tau htau hclock
  have hsmall := clock_lt_of_price_lt htau hn1 hclock (marginal_gt_power_price hq hk)
  refine ⟨hsmall, ?_, ?_⟩
  · intro hleft hright
    have hn16 : (16 : ℝ) ≤ (q : ℝ) ^ k := by linarith
    have hc := (hphase hn16).2 tau htau hclock
    linarith
  · intro hleft _hright
    by_contra h
    have hnB : (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ) := le_of_not_gt h
    have hnt : t < (q : ℝ) ^ k := hleft.trans_lt hsmall
    have hn16 : (16 : ℝ) ≤ (q : ℝ) ^ k := by linarith
    have hc := (hphase hn16).2 tau htau hclock
    linarith

/-- The literal strict positive-layer count law forces higher reference powers
in the forward window to divide the same positive integer, and its first primes
have valuation zero. The associated higher clocks obey both literal implications. -/
theorem strict_inventory_forward_window {U : ℕ} (hU : 0 < U) {t : ℝ} (ht : 243 ≤ t)
    (hstrict : ∀ q : ℕ, U.factorization q =
      optimalLayerCount (1 / (t * Real.log t)) q) :
    (∀ q k : ℕ, q.Prime → 2 ≤ k → t < (q : ℝ) ^ k →
      (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ) → k ≤ U.factorization q ∧ q ^ k ∣ U) ∧
    (∀ q : ℕ, q.Prime → t < (q : ℝ) → (q : ℝ) ≤ t + t^(4 / 5 : ℝ) →
      U.factorization q = 0) ∧
    (∀ q k : ℕ, q.Prime → 2 ≤ k → ∀ tau : ℝ, 1 < tau →
      1 / (tau * Real.log tau) = goldenLayerMarginal q k →
      tau < (q : ℝ) ^ k ∧
      (t < (q : ℝ) ^ k → (q : ℝ) ^ k ≤ t + t^(4 / 5 : ℝ) → tau < t) ∧
      (t ≤ tau → tau ≤ t + t^(4 / 5 : ℝ) → t + t^(4 / 5 : ℝ) < (q : ℝ) ^ k)) := by
  have ht1 : 1 < t := by linarith
  have hprice : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht1))
  refine ⟨?_, ?_, ?_⟩
  · intro q k hq hk hleft hright
    have hgain := (higher_layer_forward_window hq hk ht).1 hleft hright
    have hmem : k ∈ {j : ℕ | 1 ≤ j ∧ q.Prime ∧
        1 / (t * Real.log t) < goldenLayerMarginal q j} := ⟨by omega, hq, hgain⟩
    rw [positive_layers_eq_count_interval hprice hq] at hmem
    have hle : k ≤ U.factorization q := by rw [hstrict]; exact hmem.2
    exact ⟨hle, (hq.pow_dvd_iff_le_factorization (Nat.ne_of_gt hU)).mpr hle⟩
  · intro q hq hleft _hright
    have hm := golden_layer_marginal_le_inv_pow hq (a := 1) le_rfl
    have hm' : goldenLayerMarginal q 1 ≤ 1 / ((q : ℝ) * Real.log q) := by
      simpa only [pow_one, div_mul_eq_div_div, one_div] using hm
    have hnot : ¬ 1 / (t * Real.log t) < goldenLayerMarginal q 1 := by
      exact not_lt_of_ge ((hm'.trans (price_strictAnti ht1 hleft).le))
    rw [hstrict]
    by_contra h
    have hc : 1 ≤ optimalLayerCount (1 / (t * Real.log t)) q := by omega
    have hmem : 1 ∈ Set.Icc 1 (optimalLayerCount (1 / (t * Real.log t)) q) :=
      ⟨le_rfl, hc⟩
    rw [← positive_layers_eq_count_interval hprice hq] at hmem
    exact hnot hmem.2.2
  · intro q k hq hk
    exact (higher_layer_forward_window hq hk ht).2

#print axioms higher_layer_price_separation
#print axioms higher_layer_forward_window
#print axioms strict_inventory_forward_window

end D5.S3.Arith.Robin.EulerLayerPhaseSeparation

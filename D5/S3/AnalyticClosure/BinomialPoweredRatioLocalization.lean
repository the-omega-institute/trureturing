/- GID: D5/S3/AnalyticClosure/BinomialPoweredRatioLocalization
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialPoweredRatioLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Localization of maxima with the actual powered binomial sum denominator. -/

import D5.S3.AnalyticClosure.BinomialMaximumLocalization
import Mathlib.Algebra.Order.Chebyshev

open Filter Real Finset
open scoped Topology
open D5.S3.AnalyticClosure.BinomialMaximumLocalization

namespace D5.S3.AnalyticClosure.BinomialPoweredRatioLocalization

/-- Both numerator and denominator are sums of powers. -/
noncomputable def poweredRatio (a : ℝ) (l m r : ℕ) : ℝ :=
  (∑ i ∈ range (r + 1), ((m.choose i : ℝ) * a ^ i) ^ l) /
    ∑ i ∈ range (r + 1), ((r.choose i : ℝ) * a ^ i) ^ l

/-- Every choice among the actual global maxima has the same limiting slope.
The power-mean denominator bound costs only a polynomial, which is absorbed by
the exponential separation. Ties are unrestricted. -/
theorem actual_maximizer_slope (a : ℝ) (ha : 0 < a) (l : ℕ) (hl : 0 < l)
    (r : ℕ → ℕ) (hr : ∀ m, r m ≤ m)
    (hmax : ∀ m j, j ≤ m → poweredRatio a l m j ≤ poweredRatio a l m (r m)) :
    Tendsto (fun m : ℕ => (r m : ℝ) / m) atTop (𝓝 (a / (1 + 2 * a))) := by
  have hcompare (m j : ℕ) : prefixValue a l m j ≤ poweredRatio a l m j ∧
      poweredRatio a l m j ≤ (j + 1 : ℝ) ^ l * prefixValue a l m j := by
    let f (i : ℕ) := (j.choose i : ℝ) * a ^ i
    let D := ∑ i ∈ range (j + 1), f i ^ l
    let S := (1 + a) ^ j
    let N := ∑ i ∈ range (j + 1), ((m.choose i : ℝ) * a ^ i) ^ l
    have hf (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
    have hS : ∑ i ∈ range (j + 1), f i = S := by
      simpa [f, S, mul_comm, mul_left_comm, mul_assoc, add_comm] using
        (add_pow a 1 j).symm
    have hSpos : 0 < S := by dsimp [S]; positivity
    have hDpos : 0 < D := by
      have ht := single_le_sum (s := range (j + 1)) (f := fun i => f i ^ l)
        (fun i _ => pow_nonneg (hf i) l) (show 0 ∈ range (j + 1) by simp)
      have hf0 : f 0 = 1 := by simp [f]
      rw [hf0, one_pow] at ht
      exact lt_of_lt_of_le zero_lt_one ht
    have hN : 0 ≤ N := by dsimp [N]; positivity
    have hDupper : D ≤ S ^ l := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hi (i : ℕ) (hi : i ∈ range (j + 1)) : f i ≤ S := by
        rw [← hS]
        exact single_le_sum (fun k _ => hf k) hi
      calc
        D = ∑ i ∈ range (j + 1), f i * f i ^ t := by simp [D, ht, pow_succ, mul_comm]
        _ ≤ ∑ i ∈ range (j + 1), f i * S ^ t :=
          sum_le_sum fun i hi' => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hf i) (hi i hi') t) (hf i)
        _ = S ^ l := by rw [← sum_mul, hS, ht, pow_succ]; ring
    have hDlower : S ^ l ≤ (j + 1 : ℝ) ^ l * D := by
      have hj := pow_sum_le_card_mul_sum_pow
        (s := range (j + 1)) (f := f) (fun i _ => hf i) (l - 1)
      rw [Nat.sub_add_cancel hl, hS] at hj
      simp only [card_range, Nat.cast_add, Nat.cast_one] at hj
      exact hj.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
          (Nat.sub_le l 1))
        hDpos.le)
    change N / (1 + a) ^ (j * l) ≤ N / D ∧
      N / D ≤ (j + 1 : ℝ) ^ l * (N / (1 + a) ^ (j * l))
    rw [pow_mul]
    change N / S ^ l ≤ N / D ∧ N / D ≤ (j + 1 : ℝ) ^ l * (N / S ^ l)
    constructor
    · exact div_le_div_of_nonneg_left hN hDpos hDupper
    · apply (div_le_iff₀ hDpos).mpr
      have hmul := mul_le_mul_of_nonneg_left hDlower hN
      have hquot := (le_div_iff₀ (pow_pos hSpos l)).mpr hmul
      convert hquot using 1 <;> ring
  let q := a / (1 + 2 * a)
  let L := (1 - ((1 + a)⁻¹) ^ l)⁻¹
  let B := (1 + 2 * a) / (1 + a)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).2; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hinv : (1 + a)⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one (by positivity)).2 (by linarith)
  have hL : 0 < L :=
    inv_pos.mpr (sub_pos.mpr (pow_lt_one₀ (by positivity) hinv (by omega)))
  have hfloor := floor_comparison a ha l hl
  change Tendsto (fun m : ℕ => prefixValue a l m ⌊(m : ℝ) * q⌋₊ /
    B ^ (m * l) * sqrt (2 * π * m * q * (1 - q)) ^ l) atTop (𝓝 L) at hfloor
  have hlow := hfloor.eventually (lt_mem_nhds (show L / 2 < L by linarith))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let c := min (ε ^ 2 / 2) (ε * log (1 + a) / 2)
  have hc : 0 < c := lt_min (by positivity)
    (div_pos (mul_pos hε (log_pos (by linarith))) (by norm_num))
  have hlc : 0 < (l : ℝ) * c := mul_pos (by exact_mod_cast hl) hc
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  let C := 2 * π * q * (1 - q)
  have hC : 0 < C := by dsimp [C]; positivity
  have hupper : Tendsto (fun m : ℕ =>
      (2 * m : ℝ) ^ (l + 1) * exp (-(l : ℝ) * m * c) *
        sqrt (2 * π * m * q * (1 - q)) ^ l) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((l + 1 : ℕ) + (l : ℝ) / 2) ((l : ℝ) * c) hlc).comp hm).const_mul
        ((2 : ℝ) ^ (l + 1) * sqrt C ^ l)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hid : 2 * π * (m : ℝ) * q * (1 - q) = C * m := by dsimp [C]; ring
    dsimp only [Function.comp_apply]
    rw [hid, sqrt_mul hC.le]
    simp only [mul_pow, sqrt_eq_rpow (m : ℝ)]
    rw [← rpow_mul_natCast hmR.le]
    rw [show (1 / 2 : ℝ) * l = (l : ℝ) / 2 by ring,
      rpow_add hmR, rpow_natCast]
    rw [show -(l : ℝ) * m * c = -((l : ℝ) * c) * m by ring]
    ring
  have hup := hupper.eventually (gt_mem_nhds (show (0 : ℝ) < L / 2 by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlow.and (hup.and (eventually_gt_atTop 0)))
  refine ⟨N, fun m hmN => ?_⟩
  rw [Real.dist_eq]
  by_contra hnot
  have hfar : ε ≤ |(r m : ℝ) / m - q| := le_of_not_gt hnot
  have hsep := separated_prefix_bound a ha l ε hε m (r m) (hN m hmN).2.2 (hr m) hfar
  have hfloorm : ⌊(m : ℝ) * q⌋₊ ≤ m :=
    Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
  have hcmp := (hcompare m ⌊(m : ℝ) * q⌋₊).1.trans
    ((hmax m _ hfloorm).trans (hcompare m (r m)).2)
  have hpoly : (r m + 1 : ℝ) ^ l ≤ (m + 1 : ℝ) ^ l :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right (hr m) 1) l
  have hpref0 : 0 ≤ prefixValue a l m (r m) := by unfold prefixValue; positivity
  have hcmp' := hcmp.trans (mul_le_mul_of_nonneg_right hpoly hpref0)
  have hdiv := div_le_div_of_nonneg_right hcmp' (pow_pos hB (m * l)).le
  rw [mul_div_assoc] at hdiv
  have hsep' := mul_le_mul_of_nonneg_left hsep (show 0 ≤ (m + 1 : ℝ) ^ l by positivity)
  have hbound := hdiv.trans hsep'
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (hN m hmN).2.2
  have hpow : (m + 1 : ℝ) ^ (l + 1) ≤ (2 * m : ℝ) ^ (l + 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hbound' : prefixValue a l m ⌊(m : ℝ) * q⌋₊ / B ^ (m * l) ≤
      (2 * m : ℝ) ^ (l + 1) * exp (-(l : ℝ) * m * c) := by
    calc
      _ ≤ (m + 1 : ℝ) ^ l * ((m + 1 : ℝ) * exp (-(l : ℝ) * m * c)) := hbound
      _ = (m + 1 : ℝ) ^ (l + 1) * exp (-(l : ℝ) * m * c) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_right hbound'
    (show 0 ≤ sqrt (2 * π * m * q * (1 - q)) ^ l by positivity)
  have hlo := (hN m hmN).1
  have hhi := (hN m hmN).2.1
  change _ < L / 2 at hhi
  linarith

end D5.S3.AnalyticClosure.BinomialPoweredRatioLocalization

/- GID: D5/S3/AnalyticClosure/BinomialPowerNormalization
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BinomialPowerNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All positive integer powers of binomial masses, with exact normalization. -/

import D5.S3.AnalyticClosure.BinomialLocalGaussian

open Filter Real Finset
open scoped Topology
open D5.S3.AnalyticClosure.BinomialLocalGaussian

namespace D5.S3.AnalyticClosure.BinomialPowerNormalization

/-- For every fixed `0 < p < 1` and positive integer `l`, the sum of powers of
binomial masses has its full Gaussian normalization along all natural numbers.
The central relative error is summed against Gaussian weights; the complementary
window is controlled after multiplication by the required real power of `n`. -/
theorem binomial_power_normalization (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : ℕ) (hl : 0 < l) :
    Tendsto (fun n : ℕ => (∑ i ∈ range (n+1), binomialMass p n i ^ l) /
      ((2*π*n*p*(1-p)) ^ ((1-(l : ℝ))/2) / sqrt l)) atTop (𝓝 1) := by
  have normalization_scaled (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : ℕ) (hl : 0 < l) :
      Tendsto (fun n : ℕ =>
        (sqrt (2*π*n*p*(1-p)))^l * (∑ i ∈ range (n+1), binomialMass p n i ^ l) /
          sqrt n) atTop (𝓝 (sqrt (π / ((l : ℝ)/(2*p*(1-p)))))) := by
    have weighted_error (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (l : ℕ) (hl : 0 < l) :
        Tendsto (fun n : ℕ =>
          ((∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
              |(i : ℝ) - n*p| ≤ (n : ℝ) ^ (7 / 12 : ℝ)),
            (binomialMass p n i * sqrt (2*π*n*p*(1-p)))^l) -
          ∑ i ∈ (range (n + 1)).filter (fun i : ℕ =>
              |(i : ℝ) - n*p| ≤ (n : ℝ) ^ (7 / 12 : ℝ)),
            exp (-((l : ℝ)/(2*p*(1-p))) * (((i : ℝ)-n*p)/sqrt n)^2)) / sqrt n)
          atTop (𝓝 0) := by
      let c : ℝ := (l : ℝ)/(2*p*(1-p))
      have hc : 0 < c := div_pos (by exact_mod_cast hl) (by positivity)
      let W (n : ℕ) := (range (n + 1)).filter (fun i : ℕ =>
        |(i : ℝ) - n*p| ≤ (n : ℝ) ^ (7 / 12 : ℝ))
      let G (n i : ℕ) := exp (-c * (((i : ℝ)-n*p)/sqrt n)^2)
      let R (n i : ℕ) := binomialMass p n i * sqrt (2*π*n*p*(1-p)) *
        exp (((i : ℝ)-n*p)^2/(2*n*p*(1-p)))
      have hg := gaussian_window_sum_limit p c hp hp1 hc
      have hgb : ∀ᶠ n : ℕ in atTop, (∑ i ∈ W n, G n i) / sqrt n < sqrt (π/c)+1 :=
        hg.eventually (gt_mem_nhds (by linarith))
      have hid (n i : ℕ) (hn : 0 < n) :
          (binomialMass p n i * sqrt (2*π*n*p*(1-p)))^l = R n i ^ l * G n i := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have he : -c * (((i : ℝ)-n*p)/sqrt n)^2 =
            -(l : ℝ) * (((i : ℝ)-n*p)^2/(2*n*p*(1-p))) := by
          dsimp [c]
          rw [div_pow, sq_sqrt hnR.le]
          field_simp
          <;> ring
        dsimp [R, G]
        rw [he]
        simp only [mul_pow, ← exp_nat_mul]
        simp only [mul_assoc, ← exp_add, neg_mul, add_neg_cancel, exp_zero, mul_one]
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      have hb : 0 < sqrt (π/c)+1 := by positivity
      have hd : 0 < ε / (sqrt (π/c)+1) := div_pos hε hb
      have hcont : ContinuousAt (fun x : ℝ => x^l) 1 := continuousAt_id.pow l
      obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hcont (ε/(sqrt (π/c)+1)) hd
      obtain ⟨N, hN⟩ := local_gaussian_window p hp hp1 δ hδ
      obtain ⟨M, hM⟩ := eventually_atTop.mp hgb
      refine ⟨max 1 (max N M), fun n hn => ?_⟩
      have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_left _ _) hn)
      have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
      have hnM : M ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
      have hR (i : ℕ) (hi : i ∈ W n) : |R n i^l - 1| < ε/(sqrt (π/c)+1) := by
        have ht := hδbound (hN n hnN i (mem_filter.mp hi).2)
        simpa only [Real.dist_eq, one_pow] using ht
      have hs : |∑ i ∈ W n, (R n i^l - 1)*G n i| ≤
          (ε/(sqrt (π/c)+1)) * ∑ i ∈ W n, G n i := by
        calc
          _ ≤ ∑ i ∈ W n, |(R n i^l-1)*G n i| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ W n, (ε/(sqrt (π/c)+1))*G n i := by
            apply sum_le_sum
            intro i hi
            rw [abs_mul, abs_of_pos (exp_pos _)]
            exact mul_le_mul_of_nonneg_right (hR i hi).le (exp_pos _).le
          _ = _ := (mul_sum _ _ _).symm
      rw [Real.dist_eq, sub_zero]
      change |((∑ i ∈ W n, (binomialMass p n i * sqrt (2*π*n*p*(1-p)))^l) -
        ∑ i ∈ W n, G n i) / sqrt n| < ε
      have heq : (∑ i ∈ W n, (binomialMass p n i * sqrt (2*π*n*p*(1-p)))^l) -
          ∑ i ∈ W n, G n i = ∑ i ∈ W n, (R n i^l-1)*G n i := by
        rw [← sum_sub_distrib]
        apply sum_congr rfl
        intro i hi
        rw [hid n i hn0]
        ring
      rw [heq, abs_div, abs_of_nonneg (sqrt_nonneg _)]
      calc
        _ ≤ ((ε/(sqrt (π/c)+1)) * ∑ i ∈ W n, G n i) / sqrt n :=
          div_le_div_of_nonneg_right hs (sqrt_nonneg _)
        _ = (ε/(sqrt (π/c)+1)) * ((∑ i ∈ W n, G n i) / sqrt n) := by ring
        _ < (ε/(sqrt (π/c)+1)) * (sqrt (π/c)+1) :=
          mul_lt_mul_of_pos_left (hM n hnM) hd
        _ = ε := div_mul_cancel₀ _ hb.ne'
    let W (n : ℕ) := (range (n+1)).filter (fun i : ℕ =>
      |(i : ℝ)-n*p| ≤ (n : ℝ) ^ (7/12 : ℝ))
    let T (n : ℕ) := (range (n+1)).filter (fun i : ℕ =>
      (n : ℝ) ^ (7/12 : ℝ) < |(i : ℝ)-n*p|)
    have hc : 0 < (l : ℝ)/(2*p*(1-p)) := by positivity
    have hg := gaussian_window_sum_limit p _ hp hp1 hc
    have he := (weighted_error p hp hp1 l hl).add hg
    simp only [zero_add] at he
    have hcentral : Tendsto (fun n : ℕ => (sqrt (2*π*n*p*(1-p)))^l *
        (∑ i ∈ W n, binomialMass p n i ^ l) / sqrt n)
        atTop (𝓝 (sqrt (π / ((l : ℝ)/(2*p*(1-p)))))) := by
      apply he.congr'
      filter_upwards with n
      dsimp [W]
      rw [← add_div, sub_add_cancel, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [mul_pow, mul_comm]
    have htail := (binomial_power_tail p hp hp1 l hl (((l : ℝ)-1)/2)).const_mul
      ((sqrt (2*π*p*(1-p)))^l)
    simp only [mul_zero] at htail
    have htail' : Tendsto (fun n : ℕ => (sqrt (2*π*n*p*(1-p)))^l *
        (∑ i ∈ T n, binomialMass p n i ^ l) / sqrt n) atTop (𝓝 0) := by
      apply htail.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hC : 0 ≤ 2*π*p*(1-p) := by positivity
      have hprod : 2*π*(n : ℝ)*p*(1-p) = (2*π*p*(1-p))*n := by ring
      rw [hprod, sqrt_mul hC, mul_pow]
      simp only [sqrt_eq_rpow]
      rw [← rpow_mul_natCast hnR.le]
      have hex : (n : ℝ) ^ ((1/2 : ℝ)*l) / (n : ℝ) ^ (1/2 : ℝ) =
          (n : ℝ) ^ (((l : ℝ)-1)/2) := by
        rw [← rpow_sub hnR]
        congr 1
        ring
      dsimp [T]
      rw [← hex]
      ring
    have h := hcentral.add htail'
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards with n
    have hs := sum_filter_add_sum_filter_not (range (n+1))
      (fun i : ℕ => |(i : ℝ)-n*p| ≤ (n : ℝ) ^ (7/12 : ℝ))
      (fun i : ℕ => binomialMass p n i ^ l)
    simp only [not_le] at hs
    dsimp [W, T]
    rw [← add_div, ← mul_add, hs]
  let C : ℝ := 2*π*p*(1-p)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hL : 0 < sqrt (C/(l : ℝ)) := sqrt_pos.mpr (div_pos hC hlR)
  have he : π / ((l : ℝ)/(2*p*(1-p))) = C/(l : ℝ) := by
    dsimp [C]
    field_simp
  have h := normalization_scaled p hp hp1 l hl
  rw [he] at h
  have h' := h.div_const (sqrt (C/(l : ℝ)))
  rw [div_self hL.ne'] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : 2*π*(n : ℝ)*p*(1-p) = C*n := by dsimp [C]; ring
  rw [hprod]
  have hA : 0 < (C*n) ^ ((1-(l : ℝ))/2) / sqrt l := by positivity
  have hs : sqrt (C*n)^l * ((C*n) ^ ((1-(l : ℝ))/2) / sqrt l) =
      sqrt (C/(l : ℝ)) * sqrt n := by
    rw [← mul_div_assoc, sqrt_eq_rpow, ← rpow_mul_natCast (mul_pos hC hnR).le,
      ← rpow_add (mul_pos hC hnR)]
    have hpow : (1/2 : ℝ)*l + (1-(l : ℝ))/2 = 1/2 := by ring
    rw [hpow, ← sqrt_eq_rpow, sqrt_mul hC.le, sqrt_div hC.le]
    ring
  have hN : sqrt (n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have hS : sqrt (l : ℝ) ≠ 0 := (sqrt_pos.mpr hlR).ne'
  have hP : (C*n) ^ ((1-(l : ℝ))/2) ≠ 0 := (rpow_pos_of_pos (mul_pos hC hnR) _).ne'
  field_simp
  field_simp at hs
  linear_combination (∑ i ∈ range (n+1), binomialMass p n i ^ l) * hs

end D5.S3.AnalyticClosure.BinomialPowerNormalization

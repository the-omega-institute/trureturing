/- GID: D5/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/HNPCorrectionLiftAdvantage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict domination of Bernstein corrections after common elevation. -/

/- Portions adapted from TauCetiProject/TauCeti, commit
   eae7f76da7948d09c56f491e3315d690f7227b29.
   Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
   Released under Apache 2.0; the license is retained in
   docs/reports/licenses/TauCeti-Apache-2.0.txt.
   The local moment helpers can be replaced when the project's pinned Mathlib
   supplies the corresponding weighted Vandermonde and hypergeometric moments. -/

import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

noncomputable section
open Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

/-- Hypergeometric weights for elevating a Bernstein vector from degree `K` to `N`. -/
def weight (N K n k : ℕ) : ℝ :=
  (K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) / (N.choose n : ℝ)

/-- A coefficient of the elevated vector. -/
def lift (N K n : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), weight N K n k * v k

private theorem desc_factorial_mul_choose {m i : ℕ} (hmi : m ≤ i) (A : ℕ) :
    i.descFactorial m * A.choose i = A.descFactorial m * (A - m).choose (i - m) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (i.choose m) (A.choose i), Nat.choose_mul hmi]

/-- **Vandermonde's convolution weighted by a falling factorial of the summation index.**

Weighting the `i`th summand of `∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` by `(i)ₘ` multiplies
the value by `(A)ₘ` and lowers both indices by `m`. After division by `C(A + B, r)`, the cases
`m = 1` and `m = 2` give the first two factorial moments of a hypergeometric law. -/
private theorem sum_desc_factorial_choose {m r : ℕ} (hmr : m ≤ r) (A B : ℕ) :
    ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A + B - m).choose (r - m) := by
  -- Only the indices `m ≤ i` contribute, since `(i)ₘ` vanishes below `m`.
  have hsub : Ico m (r + 1) ⊆ range (r + 1) := fun i hi => mem_range.2 (mem_Ico.1 hi).2
  have hvanish : ∀ i ∈ range (r + 1), i ∉ Ico m (r + 1) →
      i.descFactorial m * (A.choose i * B.choose (r - i)) = 0 := by
    intro i hi hni
    simp only [mem_range] at hi
    simp only [mem_Ico, not_and, not_lt] at hni
    simp [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : i < m)]
  -- After shifting the index by `m`, the weight becomes the constant `(A)ₘ` and what is left
  -- is the unweighted convolution of `A - m` with `B`.
  have key : ∑ i ∈ range (r + 1), i.descFactorial m * (A.choose i * B.choose (r - i)) =
      A.descFactorial m * (A - m + B).choose (r - m) := by
    have hrange : r + 1 - m = r - m + 1 := by omega
    rw [← Finset.sum_subset hsub hvanish, Finset.sum_Ico_eq_sum_range,
      hrange, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ (A - m).choose i * B.choose j) (r - m), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hri : r - (m + i) = r - m - i := by omega
    rw [hri, ← Nat.mul_assoc, desc_factorial_mul_choose (Nat.le_add_right m i) A,
      Nat.add_sub_cancel_left, Nat.mul_assoc]
  -- The two ways of subtracting `m` agree unless `A < m`, where `(A)ₘ` is zero anyway.
  rcases le_or_gt m A with hmA | hmA
  · have hsub_add : A + B - m = A - m + B := by omega
    rwa [hsub_add]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmA] at key ⊢
    simpa using key

private theorem sum_range_mul_choose_mul_choose {N K n : ℕ} (hK : K ≤ N) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), k * K.choose k * (N - K).choose (n - k) =
      K * (N - 1).choose (n - 1) := by
  have h := sum_desc_factorial_choose (m := 1) hn K (N - K)
  rw [Nat.add_sub_of_le hK] at h
  simpa [Nat.descFactorial_one, Nat.mul_assoc] using h

private theorem sum_range_mul_pred_mul_choose_mul_choose {N K n : ℕ} (hK : K ≤ N) (hn : 2 ≤ n) :
    ∑ k ∈ Finset.range (n + 1),
        k * (k - 1) * K.choose k * (N - K).choose (n - k) =
      K * (K - 1) * (N - 2).choose (n - 2) := by
  have h := sum_desc_factorial_choose (m := 2) hn K (N - K)
  rw [Nat.add_sub_of_le hK] at h
  simpa [Nat.descFactorial_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private theorem sum_hypergeometricWeight_toReal_mul {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hN : 0 < N) :
    ∑ k ∈ Finset.range (n + 1),
        weight N K n k * (k : ℝ) =
      (n : ℝ) * (K : ℝ) / (N : ℝ) := by
  by_cases hn0 : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hchooseN : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hn
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) /
          (N.choose n : ℝ)) * (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rfl
    _ = ((∑ k ∈ Finset.range (n + 1),
        k * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) / (N.choose n : ℝ) := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ((K * (N - 1).choose (n - 1) : ℕ) : ℝ) / (N.choose n : ℝ) := by
      rw [sum_range_mul_choose_mul_choose hK hnpos]
    _ = (n : ℝ) * (K : ℝ) / (N : ℝ) := by
      have hchoose : N * (N - 1).choose (n - 1) = N.choose n * n := by
        simpa [Nat.descFactorial_one, Nat.mul_comm] using
          (desc_factorial_mul_choose (m := 1) hnpos N).symm
      have hchooseR : (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) =
          (N.choose n : ℝ) * (n : ℝ) := by
        exact_mod_cast hchoose
      push_cast
      field_simp
      linear_combination (K : ℝ) * hchooseR

private theorem cast_mul_pred_mul_choose_pred_pred {N n : ℕ} (hn2 : 2 ≤ n) (hn : n ≤ N) :
    (N : ℝ) * ((N : ℝ) - 1) * ((N - 2).choose (n - 2) : ℝ) =
      (N.choose n : ℝ) * (n : ℝ) * ((n : ℝ) - 1) := by
  have hnat : (n - 1) * n * N.choose n = (N - 1) * N * (N - 2).choose (n - 2) := by
    simpa [Nat.descFactorial_succ, Nat.mul_assoc] using
      desc_factorial_mul_choose (m := 2) hn2 N
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hreal : ((n : ℝ) - 1) * (n : ℝ) * (N.choose n : ℝ) =
      ((N : ℝ) - 1) * (N : ℝ) * ((N - 2).choose (n - 2) : ℝ) := by
    rw [← hn1, ← hN1]
    exact_mod_cast hnat
  linear_combination -hreal

private theorem sum_hypergeometricWeight_toReal_mul_pred {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hN : 1 < N) :
    ∑ k ∈ Finset.range (n + 1),
        weight N K n k * (k : ℝ) * ((k : ℝ) - 1) =
      (n : ℝ) * ((n : ℝ) - 1) * (K : ℝ) * ((K : ℝ) - 1) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  by_cases hn2 : 2 ≤ n
  · -- Normalize the weights by `N.choose n`, apply the second-factorial-moment
    -- Vandermonde identity, and cancel the denominator using two choose recurrences.
    have hchooseN : (N.choose n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hn
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) /
            (N.choose n : ℝ)) * (k : ℝ) * ((k : ℝ) - 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        rfl
      _ = ((∑ k ∈ Finset.range (n + 1),
          k * (k - 1) * K.choose k * (N - K).choose (n - k) : ℕ) : ℝ) /
            (N.choose n : ℝ) := by
        push_cast
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k hk
        cases k with
        | zero => simp
        | succ k =>
            simp only [Nat.cast_succ, Nat.succ_sub_one]
            ring
      _ = ((K * (K - 1) * (N - 2).choose (n - 2) : ℕ) : ℝ) /
            (N.choose n : ℝ) := by
        rw [sum_range_mul_pred_mul_choose_mul_choose hK hn2]
      _ = (n : ℝ) * ((n : ℝ) - 1) * (K : ℝ) * ((K : ℝ) - 1) /
          ((N : ℝ) * ((N : ℝ) - 1)) := by
        have hKpred : (K : ℝ) * ((K - 1 : ℕ) : ℝ) =
            (K : ℝ) * ((K : ℝ) - 1) := by
          cases K <;> norm_num [Nat.cast_sub]
        have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
        push_cast
        rw [hKpred]
        field_simp [hNm1]
        linear_combination (K : ℝ) * ((K : ℝ) - 1) *
          cast_mul_pred_mul_choose_pred_pred hn2 hn
  · -- When `n` is zero or one, the falling factorial `k * (k - 1)` vanishes on the support.
    have hnle : n ≤ 1 := by omega
    interval_cases n <;> norm_num [Finset.sum_range_succ, weight]



lemma weight_nonneg (N K n k : ℕ) : 0 ≤ weight N K n k := by
  unfold weight
  positivity

lemma weight_eq_zero {N K n k : ℕ} (h : K < k ∨ N - K < n - k) :
    weight N K n k = 0 := by
  rcases h with h | h <;> simp [weight, Nat.choose_eq_zero_of_lt h]

lemma weight_sum {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N) :
    ∑ k ∈ range (n + 1), weight N K n k = 1 := by
  have h : ∑ k ∈ range (n + 1), K.choose k * (N - K).choose (n - k) =
      N.choose n := by
    have hv := Nat.add_choose_eq K (N - K) n
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
    simpa only [Nat.add_sub_of_le hK] using hv.symm
  have hc : (N.choose n : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hn
  unfold weight
  rw [← Finset.sum_div]
  have hR : ∑ k ∈ range (n + 1), (K.choose k : ℝ) *
      ((N - K).choose (n - k) : ℝ) = (N.choose n : ℝ) := by exact_mod_cast h
  rw [hR, div_self hc]

private lemma weight_product {N K L t i k : ℕ} (hLK : L ≤ K)
    (ht : t ≤ N) (hki : k ≤ i) :
    weight N K t i * weight K L i k =
      (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) *
        ((N - K).choose (t - i) : ℝ) / (N.choose t : ℝ) := by
  by_cases hi : i ≤ K
  · have hCi : (K.choose i : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hi
    have hCt : (N.choose t : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero ht
    unfold weight
    field_simp
  · have hKi : K.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz : L.choose k * (K - L).choose (i - k) = 0 := by
      by_cases hk : k ≤ L
      · rw [Nat.choose_eq_zero_of_lt (show K - L < i - k by omega), Nat.mul_zero]
      · rw [Nat.choose_eq_zero_of_lt (show L < k by omega), Nat.zero_mul]
    have hzR : (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) = 0 := by
      exact_mod_cast hz
    simp [weight, hKi, hzR]

/-- Successive Bernstein elevations have exactly the direct coefficients. -/
private lemma lift_compose {N K L t : ℕ} (hLK : L ≤ K) (hKN : K ≤ N)
    (ht : t ≤ N) (v : ℕ → ℝ) :
    lift N K t (fun i => lift K L i v) = lift N L t v := by
  have htri :
      (∑ i ∈ range (t + 1), ∑ k ∈ range (i + 1),
        (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) *
          ((N - K).choose (t - i) : ℝ) / (N.choose t : ℝ) * v k) =
      ∑ k ∈ range (t + 1), ∑ i ∈ Ico k (t + 1),
        (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) *
          ((N - K).choose (t - i) : ℝ) / (N.choose t : ℝ) * v k := by
    simpa only [Nat.Ico_zero_eq_range] using
      (sum_Ico_Ico_comm 0 (t + 1) (fun k i =>
        (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) *
          ((N - K).choose (t - i) : ℝ) / (N.choose t : ℝ) * v k)).symm
  calc
    _ = ∑ i ∈ range (t + 1), ∑ k ∈ range (i + 1),
        (L.choose k : ℝ) * ((K - L).choose (i - k) : ℝ) *
          ((N - K).choose (t - i) : ℝ) / (N.choose t : ℝ) * v k := by
      unfold lift
      simp only [mul_sum]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro k hk
      rw [← mul_assoc, weight_product hLK ht (by simpa using hk)]
    _ = _ := htri
    _ = lift N L t v := by
      unfold lift
      apply sum_congr rfl
      intro k hk
      have hkt : k ≤ t := by simpa using hk
      rw [sum_Ico_eq_sum_range]
      have hlen : t + 1 - k = t - k + 1 := by omega
      rw [hlen]
      have hv : ∑ j ∈ range (t - k + 1),
          (K - L).choose j * (N - K).choose (t - k - j) = (N - L).choose (t - k) := by
        have h := Nat.add_choose_eq (K - L) (N - K) (t - k)
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
        have he : K - L + (N - K) = N - L := by omega
        simpa only [he] using h.symm
      have hvR : ∑ j ∈ range (t - k + 1),
          ((K - L).choose j : ℝ) * ((N - K).choose (t - k - j) : ℝ) =
          ((N - L).choose (t - k) : ℝ) := by exact_mod_cast hv
      calc
        _ = ((L.choose k : ℝ) * v k / (N.choose t : ℝ)) *
            ∑ j ∈ range (t - k + 1),
              ((K - L).choose j : ℝ) * ((N - K).choose (t - k - j) : ℝ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j hj
          have hjk : k + j - k = j := by omega
          have htj : t - (k + j) = t - k - j := by omega
          rw [hjk, htj]
          ring
        _ = _ := by rw [hvR]; unfold weight; ring

/-- The quadratic profile sampled on the degree `K` grid, divided by `K`.
The natural subtraction makes it zero outside that grid. -/
def sample (K k : ℕ) : ℝ := (k : ℝ) * ((K - k : ℕ) : ℝ) / (K : ℝ) ^ 3

/-- The HNP correction samples. -/
def correction (ρ θ : ℝ) (K k : ℕ) : ℝ :=
  θ / (K : ℝ) ^ ρ + sample K k ^ (ρ / 2)

private lemma sample_nonneg (K k : ℕ) : 0 ≤ sample K k := by
  unfold sample
  positivity

private lemma sample_moment {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hK2 : 2 ≤ K) :
    lift N K n (sample K) =
      ((K : ℝ) - 1) / (K : ℝ) ^ 2 *
        ((n : ℝ) * ((N : ℝ) - n) / ((N : ℝ) * ((N : ℝ) - 1))) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hN : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hmean := sum_hypergeometricWeight_toReal_mul hK hn (by omega)
  have hsecond := sum_hypergeometricWeight_toReal_mul_pred hK hn hN
  have hterm (k : ℕ) : weight N K n k * sample K k =
      (((K : ℝ) - 1) * (weight N K n k * k) -
        weight N K n k * k * ((k : ℝ) - 1)) / (K : ℝ) ^ 3 := by
    by_cases hk : k ≤ K
    · simp only [sample, Nat.cast_sub hk]
      ring
    · rw [weight_eq_zero (Or.inl (Nat.lt_of_not_ge hk))]
      simp
  simp only [lift, hterm, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hmean, hsecond]
  have hNm : (N : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hNm]
  ring

private lemma sample_moment_lower {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    (hK2 : 2 ≤ K) :
    ((n : ℝ) / N * (1 - (n : ℝ) / N)) / (2 * K) ≤
      lift N K n (sample K) := by
  rw [sample_moment hK hn hK2]
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast (hK2.trans hK)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hcoeff : (1 : ℝ) / (2 * K) ≤ ((K : ℝ) - 1) / K ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hvar : (n : ℝ) / N * (1 - (n : ℝ) / N) ≤
      (n : ℝ) * ((N : ℝ) - n) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    have hN0 : (0 : ℝ) < N := by linarith
    have hNm : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    field_simp
    nlinarith
  have hq0 : 0 ≤ (n : ℝ) / N * (1 - (n : ℝ) / N) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr ((div_le_one (by positivity)).2 hnN))
  calc
    _ = (1 / (2 * K)) * ((n : ℝ) / N * (1 - (n : ℝ) / N)) := by ring
    _ ≤ (((K : ℝ) - 1) / K ^ 2) *
        ((n : ℝ) * ((N : ℝ) - n) / ((N : ℝ) * ((N : ℝ) - 1))) :=
      mul_le_mul hcoeff hvar hq0 (div_nonneg (by linarith) (sq_nonneg _))

private lemma correction_lift_lower {N K n : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (hn : n ≤ N) (hK2 : 2 ≤ K) (hρ : 2 ≤ ρ) :
    θ / (K : ℝ) ^ ρ +
      (((n : ℝ) / N * (1 - (n : ℝ) / N)) / (2 * K)) ^ (ρ / 2) ≤
      lift N K n (correction ρ θ K) := by
  have hJ := (convexOn_rpow (show 1 ≤ ρ / 2 by linarith)).map_sum_le
    (t := range (n + 1)) (w := weight N K n) (p := sample K)
    (fun _ _ => weight_nonneg _ _ _ _) (weight_sum hK hn)
    (fun k _ => sample_nonneg K k)
  simp only [smul_eq_mul] at hJ
  have hpow := Real.rpow_le_rpow (show 0 ≤
      ((n : ℝ) / N * (1 - (n : ℝ) / N)) / (2 * K) by
        apply div_nonneg _ (by positivity)
        apply mul_nonneg (by positivity)
        exact sub_nonneg.mpr (div_le_one_of_le₀ (by exact_mod_cast hn) (by positivity)))
    (sample_moment_lower hK hn hK2) (show 0 ≤ ρ / 2 by linarith)
  unfold lift correction
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, weight_sum hK hn, one_mul]
  exact add_le_add_right (hpow.trans hJ) _


private lemma sample_upper_on_support {N K n k : ℕ} (hK : K ≤ N)
    (hKpos : 0 < K) (hn : n ≤ N) (hNK : N ≤ 2 * K) (hk : k ≤ n)
    (hkK : k ≤ K) (hrest : n - k ≤ N - K) :
    sample K k ≤ 4 * ((n : ℝ) / N * (1 - (n : ℝ) / N)) / K := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (hKpos.trans_le hK)
  have hNK' : (N : ℝ) ≤ 2 * K := by exact_mod_cast hNK
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hother : K - k ≤ N - n := by omega
  have hotherR : (K : ℝ) - k ≤ (N : ℝ) - n := by
    exact_mod_cast (show (K - k : ℕ) ≤ N - n from hother)
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ K := by exact_mod_cast hkK
  have hleft : (k : ℝ) / K ≤ 2 * ((n : ℝ) / N) := by
    apply (div_le_iff₀ hK0).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hNK' (show (0 : ℝ) ≤ n by positivity),
      mul_le_mul_of_nonneg_right hkn hN0.le]
  have hright : ((K : ℝ) - k) / K ≤ 2 * (1 - (n : ℝ) / N) := by
    apply (div_le_iff₀ hK0).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hotherR hN0.le,
      mul_le_mul_of_nonneg_left hNK' (sub_nonneg.mpr hnN)]
  have hprod := mul_le_mul hleft hright
    (div_nonneg (sub_nonneg.mpr hkR) hK0.le) (by positivity)
  have hdiv := div_le_div_of_nonneg_right hprod hK0.le
  calc
    sample K k = ((k : ℝ) / K * (((K : ℝ) - k) / K)) / K := by
      unfold sample
      rw [Nat.cast_sub hkK]
      field
    _ ≤ (2 * ((n : ℝ) / N) * (2 * (1 - (n : ℝ) / N))) / K := hdiv
    _ = 4 * ((n : ℝ) / N * (1 - (n : ℝ) / N)) / K := by ring


private lemma correction_lift_upper {N K n : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (hn : n ≤ N) (hKpos : 0 < K) (hNK : N ≤ 2 * K)
    (hρ : 0 ≤ ρ) :
    lift N K n (correction ρ θ K) ≤
      θ / (K : ℝ) ^ ρ +
        (4 * ((n : ℝ) / N * (1 - (n : ℝ) / N)) / K) ^ (ρ / 2) := by
  have hbound : ∀ k ∈ range (n + 1),
      weight N K n k * sample K k ^ (ρ / 2) ≤
      weight N K n k *
        (4 * ((n : ℝ) / N * (1 - (n : ℝ) / N)) / K) ^ (ρ / 2) := by
    intro k hk
    by_cases hkK : k ≤ K
    · by_cases hrest : n - k ≤ N - K
      · apply mul_le_mul_of_nonneg_left _ (weight_nonneg _ _ _ _)
        exact Real.rpow_le_rpow (sample_nonneg _ _)
          (sample_upper_on_support hK hKpos hn hNK (by simpa using hk) hkK hrest)
          (by positivity)
      · simp [weight_eq_zero (Or.inr (Nat.lt_of_not_ge hrest))]
    · simp [weight_eq_zero (Or.inl (Nat.lt_of_not_ge hkK))]
  have hs := Finset.sum_le_sum hbound
  rw [← Finset.sum_mul, weight_sum hK hn, one_mul] at hs
  unfold lift correction
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, weight_sum hK hn, one_mul]
  exact add_le_add_right hs _

private lemma two_mul_rpow_le {x y a : ℝ} (hx : 0 ≤ x) (hxy : 2 * x ≤ y)
    (ha : 1 ≤ a) : 2 * x ^ a ≤ y ^ a := by
  have htwo : (2 : ℝ) ≤ 2 ^ a := Real.self_le_rpow_of_one_le (by norm_num) ha
  calc
    2 * x ^ a ≤ 2 ^ a * x ^ a := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hx _)
    _ = (2 * x) ^ a := (Real.mul_rpow (by norm_num) hx).symm
    _ ≤ y ^ a := Real.rpow_le_rpow (by positivity) hxy (by linarith)

/-- On a sufficiently separated grid, the actual coarse correction, elevated
 to the same degree as the fine correction, dominates twice the latter.
 The conclusion includes the two endpoint coefficients. -/
private theorem direct_correction_lift_advantage {n m r t : ℕ} {ρ θ : ℝ}
    (hn : 2 ≤ n) (hm : 16 * n ≤ m) (hr : r ≤ m) (ht : t ≤ m + r)
    (hρ : 2 ≤ ρ) (hθ : 0 ≤ θ) :
    2 * lift (m + r) m t (correction ρ θ m) ≤
      lift (m + r) n t (correction ρ θ n) := by
  have hnm : n ≤ m := by omega
  have hnN : n ≤ m + r := by omega
  have hmN : m ≤ m + r := by omega
  have hm0 : 0 < m := by omega
  have hlow := correction_lift_lower (θ := θ) hnN ht hn hρ
  have hupp := correction_lift_upper (θ := θ) hmN ht hm0 (by omega) (by linarith : 0 ≤ ρ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hNm : (0 : ℝ) < (m + r : ℕ) := by exact_mod_cast (show 0 < m + r by omega)
  have htm : (t : ℝ) ≤ (m + r : ℕ) := by exact_mod_cast ht
  let v : ℝ := (t : ℝ) / (m + r : ℕ) * (1 - (t : ℝ) / (m + r : ℕ))
  have hv : 0 ≤ v := mul_nonneg (by positivity)
    (sub_nonneg.mpr ((div_le_one hNm).2 htm))
  have hscale : (16 : ℝ) * n ≤ m := by exact_mod_cast hm
  have hpow : 2 * (4 * v / m) ^ (ρ / 2) ≤ (v / (2 * n)) ^ (ρ / 2) := by
    apply two_mul_rpow_le (by positivity) _ (by linarith)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hscale hv]
  have hden : 2 * (n : ℝ) ^ ρ ≤ (m : ℝ) ^ ρ :=
    two_mul_rpow_le hnR.le (by linarith) (by linarith)
  have hconst : 2 * (θ / (m : ℝ) ^ ρ) ≤ θ / (n : ℝ) ^ ρ := by
    have hnPow := Real.rpow_pos_of_pos hnR ρ
    have hmPow := Real.rpow_pos_of_pos hmR ρ
    apply (le_div_iff₀ hnPow).2
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hden hθ]
  have := mul_le_mul_of_nonneg_left hupp (by norm_num : (0 : ℝ) ≤ 2)
  dsimp [v] at hpow
  linarith

/-- A positive constant floor remains positive after elevation. -/
private lemma correction_lift_pos {N K t : ℕ} {ρ θ : ℝ}
    (hK : K ≤ N) (ht : t ≤ N) (hK0 : 0 < K) (hθ : 0 < θ) :
    0 < lift N K t (correction ρ θ K) := by
  unfold lift correction
  simp only [mul_add, sum_add_distrib, ← sum_mul, weight_sum hK ht, one_mul]
  apply add_pos_of_pos_of_nonneg
  · exact div_pos hθ (Real.rpow_pos_of_pos (by exact_mod_cast hK0) ρ)
  · exact sum_nonneg fun k _ => mul_nonneg (weight_nonneg _ _ _ _)
      (Real.rpow_nonneg (sample_nonneg K k) _)

/-- The original correction rises first from `n` to `n+r`, then to `m+r`.
It dominates the fine correction by a factor two, and strictly dominates it
when `theta` is positive, including both endpoint coefficients. -/
theorem correction_lift_advantage {n m r t : ℕ} {ρ θ : ℝ}
    (hn : 2 ≤ n) (hm : 16 * n ≤ m) (hr : r ≤ m) (ht : t ≤ m + r)
    (hρ : 2 ≤ ρ) (hθ : 0 ≤ θ) :
    (2 * lift (m + r) m t (correction ρ θ m) ≤
      lift (m + r) (n + r) t (fun i => lift (n + r) n i (correction ρ θ n))) ∧
    (0 < θ → lift (m + r) m t (correction ρ θ m) <
      lift (m + r) (n + r) t (fun i => lift (n + r) n i (correction ρ θ n))) := by
  rw [lift_compose (by omega) (by omega) ht]
  have h := direct_correction_lift_advantage hn hm hr ht hρ hθ
  refine ⟨h, fun hθ' => ?_⟩
  have hp := correction_lift_pos (ρ := ρ) (by omega : m ≤ m + r) ht (by omega : 0 < m) hθ'
  linarith

end D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage

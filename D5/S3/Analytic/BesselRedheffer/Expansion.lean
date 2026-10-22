/- GID: D5/S3/Analytic/BesselRedheffer/Expansion
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/Expansion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.Binomial, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Explicit sixth-order errors and a fourth-order obstruction to the Redheffer lower bound. -/

import D5.S3.Analytic.BesselRedheffer.Series
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Tactic

open scoped BigOperators Topology
open Polynomial
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series
namespace D5.S3.Analytic.BesselRedheffer.Expansion

private lemma binomial_coeff (a : ℝ) (n : ℕ) :
    Ring.choose (a + n - 1) n = (ascPochhammer ℝ n).eval a / n.factorial := by
  rw [← Ring.multichoose_eq]
  apply (eq_div_iff (by positivity : (n.factorial : ℝ) ≠ 0)).mpr
  rw [mul_comm, ← nsmul_eq_mul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
  rw [← ascPochhammer_smeval_cast ℝ, ← eval_eq_smeval]

private lemma binomial_lower {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) (hs1 : s < 1) :
    1 + a * s + a * (a + 1) / 2 * s ^ 2 ≤ 1 / (1 - s) ^ a := by
  have hm : s ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq, abs_of_nonneg hs,
      ENNReal.ofReal_lt_one] using hs1
  have hsum := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum_sub hm
  simp only [sub_zero, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    binomial_coeff] at hsum
  have hle := sum_le_hasSum (Finset.range 3) (fun n _ =>
    mul_nonneg (div_nonneg (ascPochhammer_pos n a ha).le (by positivity))
      (pow_nonneg hs n)) hsum
  convert hle using 1 <;>
    norm_num [Finset.sum_range_succ, ascPochhammer_succ_eval] <;> ring

private lemma coefficient_gap {b J : ℝ} (hb : 0 < b) (hJ : 0 < J) :
    1 / (8 * b ^ 2 * (b + 1) * (b + 2)) <
      1 / (32 * b ^ 2 * (b + 1) ^ 2) + 1 / (8 * b * (b + 1) * J) ↔
      J < 4 * b * (b + 1) * (b + 2) / (3 * b + 2) := by
  have h1 : 0 < b + 1 := by positivity
  have h2 : 0 < b + 2 := by positivity
  have h3 : 0 < 3 * b + 2 := by positivity
  rw [lt_div_iff₀ h3]
  constructor <;> intro h
  · field_simp at h
    nlinarith
  · apply (div_lt_iff₀ (by positivity : 0 < 8 * b ^ 2 * (b + 1) * (b + 2))).mpr
    field_simp
    nlinarith

private lemma energy_below_threshold {b : ℝ} (hb : 31 ≤ b) :
    (6 / 5 : ℝ) * b * (b + 6) <
      4 * b * (b + 1) * (b + 2) / (3 * b + 2) := by
  rw [lt_div_iff₀ (by positivity : 0 < 3 * b + 2)]
  have hpoly : 0 < b ^ 2 - 30 * b - 16 := by
    nlinarith [sq_nonneg (b - 31)]
  nlinarith [mul_pos (by linarith : 0 < b) hpoly]

/-- The energy estimate forces a strict fourth-order coefficient gap. -/
private theorem fourth_order_gap {ν J : ℝ} (hν : 30 ≤ ν) (hJ : 0 < J)
    (hbound : J ≤ (6 / 5 : ℝ) * (ν + 1) * (ν + 7)) :
    1 / (8 * (ν + 1) ^ 2 * (ν + 2) * (ν + 3)) <
      1 / (32 * (ν + 1) ^ 2 * (ν + 2) ^ 2) +
        1 / (8 * (ν + 1) * (ν + 2) * J) := by
  have ht := energy_below_threshold (b := ν + 1) (by linarith)
  have hg := (coefficient_gap (b := ν + 1) (J := J) (by linarith) hJ).mpr
    (hbound.trans_lt (by convert ht using 1 <;> ring))
  convert hg using 1 <;> ring

/-- The positive binomial series bounds the real power by its quadratic part. -/
private theorem redheffer_lower {b J x : ℝ} (hb : 0 < b) (hJ : 0 < J)
    (hx : x ^ 2 < J) :
    1 + x ^ 2 / (4 * b * (b + 1)) +
      (1 / (32 * b ^ 2 * (b + 1) ^ 2) + 1 / (8 * b * (b + 1) * J)) * x ^ 4 ≤
        (J / (J - x ^ 2)) ^ (J / (4 * b * (b + 1))) := by
  have ha : 0 < J / (4 * b * (b + 1)) := by positivity
  have hs : 0 ≤ x ^ 2 / J := by positivity
  have hs1 : x ^ 2 / J < 1 := (div_lt_one hJ).mpr hx
  have h := binomial_lower ha hs hs1
  have he : J / (J - x ^ 2) = (1 - x ^ 2 / J)⁻¹ := by field_simp <;> ring
  rw [he, Real.inv_rpow (by linarith : 0 ≤ 1 - x ^ 2 / J), one_div] at *
  convert h using 1 <;> field_simp <;> ring

private lemma pochhammer_one_le {b : ℝ} (hb : 1 ≤ b) (n : ℕ) :
    1 ≤ (ascPochhammer ℝ n).eval b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval]
    exact one_le_mul_of_one_le_of_one_le ih (by linarith [Nat.cast_nonneg (α := ℝ) n])

private lemma series_remainder {ν x : ℝ} (hν : 0 ≤ ν) (hx : |x| ≤ 1) :
    |nbessel ν x - (1 - x ^ 2 / (4 * (ν + 1)) +
      x ^ 4 / (32 * (ν + 1) * (ν + 2)))| ≤ x ^ 6 := by
  let f : ℕ → ℝ := fun k => (-(x ^ 2) / 4) ^ k /
    ((k.factorial : ℝ) * (ascPochhammer ℝ k).eval (ν + 1))
  have hden (k : ℕ) : 1 ≤ (k.factorial : ℝ) * (ascPochhammer ℝ k).eval (ν + 1) :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos k)
      (pochhammer_one_le (by linarith) k)
  have hxsq : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hf (k : ℕ) : |f (k + 3)| ≤ x ^ 6 / 64 * (1 / 4 : ℝ) ^ k := by
    dsimp [f]
    rw [abs_div, abs_pow, abs_div, abs_neg, abs_of_nonneg (sq_nonneg x)]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [abs_of_pos (lt_of_lt_of_le zero_lt_one (hden _))]
    calc
      _ ≤ (x ^ 2 / 4) ^ (k + 3) := div_le_self (by positivity) (hden _)
      _ = x ^ 6 / 64 * (x ^ 2 / 4) ^ k := by rw [pow_add]; ring
      _ ≤ _ := by gcongr <;> nlinarith
  have hg : Summable (fun k : ℕ => x ^ 6 / 64 * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left _
  have hsum := summable_nbessel (by linarith : -1 < ν) x
  have ht := (summable_nat_add_iff 3).mpr hsum
  have htail : |∑' k, f (k + 3)| ≤ x ^ 6 := by
    calc
      _ ≤ ∑' k, |f (k + 3)| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ht.norm
      _ ≤ ∑' k : ℕ, x ^ 6 / 64 * (1 / 4 : ℝ) ^ k := ht.abs.tsum_le_tsum hf hg
      _ = x ^ 6 / 48 := by rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num)]; ring
      _ ≤ x ^ 6 := by nlinarith [pow_nonneg (sq_nonneg x) 3]
  have he := hsum.sum_add_tsum_nat_add 3
  change (∑ k ∈ Finset.range 3, f k) + ∑' k, f (k + 3) = nbessel ν x at he
  have hpoly : (∑ k ∈ Finset.range 3, f k) =
      1 - x ^ 2 / (4 * (ν + 1)) + x ^ 4 / (32 * (ν + 1) * (ν + 2)) := by
    norm_num [f, Finset.sum_range_succ, ascPochhammer_succ_eval]
    field_simp
    <;> ring
  rw [← he, hpoly]
  simpa only [add_sub_cancel_left] using htail

private lemma quotient_remainder {F G a A c C r q t : ℝ}
    (ht : 0 ≤ t) (ht4 : t ≤ 1 / 4)
    (ha : 0 ≤ a ∧ a ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1)
    (hr : 0 ≤ r ∧ r ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (hA : A = a - r) (hC : C = c - a * r + q)
    (hF : |F - (1 - a * t + c * t ^ 2)| ≤ t ^ 3)
    (hG : |G - (1 - A * t + C * t ^ 2)| ≤ t ^ 3) :
    |G / F - (1 + r * t + q * t ^ 2)| ≤ 16 * t ^ 3 := by
  have ht1 : t ≤ 1 := by linarith
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht3 : t ^ 3 ≤ t := by nlinarith [mul_le_mul_of_nonneg_left ht2 ht]
  have hFp : 1 / 2 ≤ F := by
    have hFl := (abs_le.mp hF).1
    have hat : a * t ≤ t := mul_le_of_le_one_left ht ha.2
    have hct : 0 ≤ c * t ^ 2 := mul_nonneg hc.1 (sq_nonneg t)
    linarith
  have hF0 : 0 < F := by linarith
  let P := 1 + r * t + q * t ^ 2
  have hP0 : 0 ≤ P := by
    dsimp [P]
    nlinarith [mul_nonneg hr.1 ht, mul_nonneg hq.1 (sq_nonneg t)]
  have hP : |P| ≤ 3 := by
    rw [abs_of_nonneg hP0]
    have hrb : r * t ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hr.2 ht]
    have hqb : q * t ^ 2 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hq.2 (sq_nonneg t)]
    dsimp [P]
    linarith
  have hcr : |c * r - a * q| ≤ 2 := by
    calc
      _ ≤ |c * r| + |a * q| := abs_sub _ _
      _ ≤ 2 := by
        rw [abs_of_nonneg (mul_nonneg hc.1 hr.1), abs_of_nonneg (mul_nonneg ha.1 hq.1)]
        have hcr := (mul_le_mul_of_nonneg_right hc.2 hr.1).trans (by simpa using hr.2)
        have haq := (mul_le_mul_of_nonneg_right ha.2 hq.1).trans (by simpa using hq.2)
        linarith
  have hcq : |c * q| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hc.1 hq.1)]
    exact (mul_le_mul_of_nonneg_right hc.2 hq.1).trans (by simpa using hq.2)
  have he : F * P - G = (c * r - a * q) * t ^ 3 + c * q * t ^ 4 +
      (F - (1 - a * t + c * t ^ 2)) * P - (G - (1 - A * t + C * t ^ 2)) := by
    dsimp [P]
    rw [hA, hC]
    ring
  have herr : |F * P - G| ≤ 8 * t ^ 3 := by
    rw [he]
    calc
      _ ≤ |(c * r - a * q) * t ^ 3| + |c * q * t ^ 4| +
          |(F - (1 - a * t + c * t ^ 2)) * P| +
            |G - (1 - A * t + C * t ^ 2)| := by
        have h1 := abs_add_le ((c * r - a * q) * t ^ 3) (c * q * t ^ 4)
        have h2 := abs_add_le ((c * r - a * q) * t ^ 3 + c * q * t ^ 4)
          ((F - (1 - a * t + c * t ^ 2)) * P)
        have h3 := abs_sub ((c * r - a * q) * t ^ 3 + c * q * t ^ 4 +
          (F - (1 - a * t + c * t ^ 2)) * P) (G - (1 - A * t + C * t ^ 2))
        linarith
      _ ≤ 2 * t ^ 3 + t ^ 4 + t ^ 3 * 3 + t ^ 3 := by
        simp only [abs_mul, abs_pow, abs_of_nonneg ht]
        have hcq' : |c| * |q| ≤ 1 := by simpa only [abs_mul] using hcq
        gcongr <;> nlinarith [mul_le_mul_of_nonneg_right hcq' (pow_nonneg ht 4)]
      _ ≤ 8 * t ^ 3 := by
        have ht43 : t ^ 4 ≤ t ^ 3 := by
          calc
            t ^ 4 = t ^ 3 * t := by ring
            _ ≤ t ^ 3 * 1 := mul_le_mul_of_nonneg_left ht1 (pow_nonneg ht 3)
            _ = _ := by ring
        nlinarith [pow_nonneg ht 3]
  have heq : G / F - P = -(F * P - G) / F := by field_simp; ring
  rw [heq, abs_div, abs_neg, abs_of_pos hF0, div_le_iff₀ hF0]
  exact herr.trans (by nlinarith [mul_le_mul_of_nonneg_right hFp (pow_nonneg ht 3)])

/-- A uniform sixth-order remainder for the normalized Bessel ratio near zero. -/
private theorem ratio_remainder {ν x : ℝ} (hν : 0 ≤ ν) (hx : |x| ≤ 1 / 2) :
    |nbessel (ν + 1) x / nbessel ν x -
      (1 + x ^ 2 / (4 * (ν + 1) * (ν + 2)) +
        x ^ 4 / (8 * (ν + 1) ^ 2 * (ν + 2) * (ν + 3)))| ≤ 16 * x ^ 6 := by
  let b := ν + 1
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < b + 1 := by positivity
  have hb2 : 0 < b + 2 := by positivity
  have ha : 0 ≤ 1 / (4 * b) ∧ 1 / (4 * b) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith)
  have hc : 0 ≤ 1 / (32 * b * (b + 1)) ∧ 1 / (32 * b * (b + 1)) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      calc
        1 ≤ 32 * (1 : ℝ) * 1 := by norm_num
        _ ≤ 32 * b * (b + 1) := by gcongr <;> linarith
  have hr : 0 ≤ 1 / (4 * b * (b + 1)) ∧ 1 / (4 * b * (b + 1)) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      calc
        1 ≤ 4 * (1 : ℝ) * 1 := by norm_num
        _ ≤ 4 * b * (b + 1) := by gcongr <;> linarith
  have hq : 0 ≤ 1 / (8 * b ^ 2 * (b + 1) * (b + 2)) ∧
      1 / (8 * b ^ 2 * (b + 1) * (b + 2)) ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      calc
        1 ≤ 8 * (1 : ℝ) ^ 2 * 1 * 1 := by norm_num
        _ ≤ 8 * b ^ 2 * (b + 1) * (b + 2) := by gcongr <;> linarith
  have hA : 1 / (4 * (b + 1)) = 1 / (4 * b) - 1 / (4 * b * (b + 1)) := by
    field_simp
    <;> ring
  have hC : 1 / (32 * (b + 1) * (b + 2)) =
      1 / (32 * b * (b + 1)) - 1 / (4 * b) * (1 / (4 * b * (b + 1))) +
        1 / (8 * b ^ 2 * (b + 1) * (b + 2)) := by
    field_simp
    <;> ring
  have hF := series_remainder hν (hx.trans (by norm_num))
  have hG := series_remainder (ν := ν + 1) (by linarith) (hx.trans (by norm_num))
  have h := quotient_remainder (F := nbessel ν x) (G := nbessel (ν + 1) x)
    (a := 1 / (4 * b)) (A := 1 / (4 * (b + 1)))
    (c := 1 / (32 * b * (b + 1))) (C := 1 / (32 * (b + 1) * (b + 2)))
    (r := 1 / (4 * b * (b + 1))) (q := 1 / (8 * b ^ 2 * (b + 1) * (b + 2)))
    (t := x ^ 2) (sq_nonneg x) (by nlinarith [sq_abs x, abs_nonneg x])
    ha hc hr hq hA hC
    (by convert hF using 1 <;> (try dsimp only [b]) <;> first | ring | (congr 1 <;> ring))
    (by convert hG using 1 <;> (try dsimp only [b]) <;> first | ring | (congr 1 <;> ring))
  convert h using 1 <;> (try dsimp only [b]) <;> first | ring | (congr 1 <;> ring)

/-- The energy upper bound produces violations at every sufficiently small positive argument. -/
theorem failure_of_energy_bound {ν j : ℝ} (hν : 30 ≤ ν) (hj : 0 < j)
    (hbound : j ^ 2 ≤ (6 / 5 : ℝ) * (ν + 1) * (ν + 7)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, 0 < x → x < ε →
      x < j ∧ nbessel (ν + 1) x / nbessel ν x <
        (j ^ 2 / (j ^ 2 - x ^ 2)) ^ (j ^ 2 / (4 * (ν + 1) * (ν + 2))) := by
  let R := 1 / (8 * (ν + 1) ^ 2 * (ν + 2) * (ν + 3))
  let L := 1 / (32 * (ν + 1) ^ 2 * (ν + 2) ^ 2) +
    1 / (8 * (ν + 1) * (ν + 2) * j ^ 2)
  have hg : R < L := fourth_order_gap hν (sq_pos_of_pos hj) hbound
  let ε := min j (min (1 / 2) ((L - R) / 32))
  have hε : 0 < ε := lt_min hj (lt_min (by norm_num) (by linarith))
  refine ⟨ε, hε, ?_⟩
  intro x hx0 hxε
  have hxj : x < j := hxε.trans_le (min_le_left _ _)
  have hxhalf : x < 1 / 2 := hxε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxgap : x < (L - R) / 32 := hxε.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hxsq : x ^ 2 < j ^ 2 := by nlinarith
  have hRatio := (abs_le.mp (ratio_remainder (ν := ν) (by linarith)
    (by rw [abs_of_pos hx0]; linarith : |x| ≤ 1 / 2))).2
  have hLower := redheffer_lower (b := ν + 1) (J := j ^ 2)
    (by linarith) (sq_pos_of_pos hj) hxsq
  have hs : 0 < L - R - 16 * x ^ 2 := by nlinarith
  have hp : 0 < (L - R - 16 * x ^ 2) * x ^ 4 := mul_pos hs (pow_pos hx0 4)
  refine ⟨hxj, ?_⟩
  have hRatio' : nbessel (ν + 1) x / nbessel ν x -
      (1 + x ^ 2 / (4 * (ν + 1) * (ν + 2)) + R * x ^ 4) ≤ 16 * x ^ 6 := by
    convert hRatio using 1 <;> (try dsimp [R]) <;> ring
  have hLower' : 1 + x ^ 2 / (4 * (ν + 1) * (ν + 2)) + L * x ^ 4 ≤
      (j ^ 2 / (j ^ 2 - x ^ 2)) ^ (j ^ 2 / (4 * (ν + 1) * (ν + 2))) := by
    convert hLower using 1 <;> (try dsimp [L]) <;> congr 1 <;> ring
  nlinarith

end D5.S3.Analytic.BesselRedheffer.Expansion

/- GID: D5/S3/Analytic/ReciprocalGammaTuran/Boundary
   generality: G
   mirror-B: D5/B/S3/Analytic/ReciprocalGammaTuran/Boundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd]
   utility: none
   digest: Strictly negative second coefficients of reciprocal Gamma Turanians at boundary shifts. -/

import D5.S3.Analytic.ReciprocalGammaTuran.Series
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
open D5.S3.Analytic.ReciprocalGammaTuran.Defs
open D5.S3.Analytic.ReciprocalGammaTuran.Series
open Filter
open scoped BigOperators Real Topology
namespace D5.S3.Analytic.ReciprocalGammaTuran.Boundary

private lemma factor_compare {u n : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hn : 1 ≤ n) :
    (1 + u / n) * (1 - u / (n + 1) ^ 2) ≥ 1 + u / (n + 1) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n + 1 ≠ 0 := by linarith
  apply (le_of_sub_nonneg ?_)
  have he : (1 + u / n) * (1 - u / (n + 1) ^ 2) - (1 + u / (n + 1)) =
      u * (1 - u) / (n * (n + 1) ^ 2) := by field_simp; ring
  rw [he]
  positivity

private lemma product_lower {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (n : ℕ) :
    (1 - t ^ 2) * (1 - t ^ 2 / 4) / (1 + t ^ 2 / 2) *
      (1 + t ^ 2 / (n + 2)) ≤
        ∏ j ∈ Finset.range (n + 2), (1 - t ^ 2 / ((j : ℝ) + 1) ^ 2) := by
  have hu : 0 ≤ t ^ 2 := sq_nonneg _
  have hu1 : t ^ 2 < 1 := by nlinarith
  have hB : 0 ≤ (1 - t ^ 2) * (1 - t ^ 2 / 4) / (1 + t ^ 2 / 2) := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · positivity
  induction n with
  | zero => norm_num [Finset.prod_range_succ]; field_simp; nlinarith
  | succ n ih =>
    rw [show n + 1 + 2 = n + 2 + 1 by omega, Finset.prod_range_succ]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hn2 : 0 < (n : ℝ) + 3 := by positivity
    have hf : 0 ≤ 1 - t ^ 2 / ((n : ℝ) + 3) ^ 2 := by
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hc := factor_compare hu hu1.le hn
    push_cast at *
    calc
      _ ≤ ((1 - t ^ 2) * (1 - t ^ 2 / 4) / (1 + t ^ 2 / 2) *
          (1 + t ^ 2 / (n + 2))) * (1 - t ^ 2 / (n + 2 + 1) ^ 2) := by
        convert mul_le_mul_of_nonneg_left hc hB using 1 <;> ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right ih (by convert hf using 1 <;> ring_nf)

private lemma sine_lower {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Real.pi * t * (1 - t ^ 2) / (1 + t ^ 2) < Real.sin (Real.pi * t) := by
  let B := (1 - t ^ 2) * (1 - t ^ 2 / 4) / (1 + t ^ 2 / 2)
  have hs := (Real.tendsto_euler_sin_prod t).comp (tendsto_add_atTop_nat 2)
  have hb (n : ℕ) : Real.pi * t * B ≤ Real.pi * t *
      ∏ j ∈ Finset.range (n + 2), (1 - t ^ 2 / ((j : ℝ) + 1) ^ 2) := by
    have hp := product_lower ht ht1 n
    have hB : 0 ≤ B := by
      dsimp [B]
      have hu1 : t ^ 2 < 1 := by nlinarith
      apply div_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · positivity
    have : B ≤ B * (1 + t ^ 2 / (n + 2)) := by
      have : 0 ≤ t ^ 2 / ((n : ℝ) + 2) := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_left (this.trans hp) (by positivity)
  have hlim : Real.pi * t * B ≤ Real.sin (Real.pi * t) := ge_of_tendsto hs (Filter.Eventually.of_forall hb)
  have hu : 0 < t ^ 2 := sq_pos_of_pos ht
  have hu1 : t ^ 2 < 1 := by nlinarith
  have hB : (1 - t ^ 2) / (1 + t ^ 2) < B := by
    dsimp [B]
    apply (div_lt_div_iff₀ (by positivity : 0 < 1 + t ^ 2)
      (by positivity : 0 < 1 + t ^ 2 / 2)).2
    nlinarith [mul_pos hu (sq_pos_of_pos (sub_pos.mpr hu1))]
  have hh := mul_lt_mul_of_pos_left hB (mul_pos Real.pi_pos ht)
  have hh' : Real.pi * t * (1 - t ^ 2) / (1 + t ^ 2) < Real.pi * t * B := by
    simpa [mul_div_assoc] using hh
  exact hh'.trans_le hlim

private lemma d_two_eq {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    d t 2 =
      1 - (1 + t ^ 2) / (t * (1 - t ^ 2) * (Real.Gamma t * Real.Gamma (1 - t))) := by
  have hcoef : d t 2 =
      1 - (rgamma (-t) * rgamma (2 + t) +
        rgamma (1 - t) * rgamma (1 + t) + rgamma (2 - t) * rgamma t) := by
    rw [← turanCoeff_one_boundary]
    norm_num [turanCoeff, Finset.sum_range_succ]
    ring_nf
    simp [rgamma, Real.Gamma_zero, Real.Gamma_one]
  rw [hcoef]
  have hG : Real.Gamma t ≠ 0 := (Real.Gamma_pos_of_pos ht).ne'
  have hH : Real.Gamma (1 - t) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have htm : t ≠ 0 := ht.ne'
  have htm1 : 1 - t ≠ 0 := by linarith
  have htp1 : 1 + t ≠ 0 := by linarith
  have htm2 : 1 - t ^ 2 ≠ 0 := by nlinarith
  have hn := Real.Gamma_add_one (s := -t) (neg_ne_zero.mpr htm)
  have hp := Real.Gamma_add_one (s := t) htm
  have hpp := Real.Gamma_add_one (s := t + 1) (by linarith : t + 1 ≠ 0)
  have hmp := Real.Gamma_add_one (s := 1 - t) htm1
  have hneg : Real.Gamma (-t) = -(Real.Gamma (1 - t) / t) := by
    rw [show -t + 1 = 1 - t by ring] at hn
    rw [← neg_div]
    apply (eq_div_iff htm).2
    nlinarith
  have hpos : Real.Gamma (1 + t) = t * Real.Gamma t := by simpa [add_comm] using hp
  have hpos2 : Real.Gamma (2 + t) = (1 + t) * (t * Real.Gamma t) := by
    rw [show t + 1 + 1 = 2 + t by ring, hp] at hpp
    simpa [add_comm] using hpp
  have hneg2 : Real.Gamma (2 - t) = (1 - t) * Real.Gamma (1 - t) := by
    convert hmp using 1 <;> congr 1 <;> ring
  simp only [rgamma, hneg, hpos, hpos2, hneg2]
  field_simp
  <;> ring

/-- Every boundary shift strictly between zero and one has a negative second coefficient. -/
theorem d_two_neg {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    turanCoeff (fun _ => 1) (-t) t t 2 < 0 := by
  have hG := Real.Gamma_pos_of_pos ht
  have hH := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - t)
  have hu : t ^ 2 < 1 := by nlinarith
  have hspos : 0 < Real.sin (Real.pi * t) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos ht) (by nlinarith [Real.pi_pos])
  have href := (eq_div_iff hspos.ne').mp (Real.Gamma_mul_Gamma_one_sub t)
  have hsin := (div_lt_iff₀ (by positivity : 0 < 1 + t ^ 2)).mp (sine_lower ht ht1)
  have hsmall : t * (1 - t ^ 2) * (Real.Gamma t * Real.Gamma (1 - t)) < 1 + t ^ 2 := by
    apply (mul_lt_mul_iff_left₀ hspos).mp
    calc
      _ = (Real.Gamma t * Real.Gamma (1 - t) * Real.sin (Real.pi * t)) *
          (t * (1 - t ^ 2)) := by ring
      _ = Real.pi * t * (1 - t ^ 2) := by rw [href]; ring
      _ < (1 + t ^ 2) * Real.sin (Real.pi * t) := by simpa [mul_comm] using hsin
  rw [turanCoeff_one_boundary, d_two_eq ht ht1]
  apply sub_neg.mpr
  apply (lt_div_iff₀ (mul_pos (mul_pos ht (sub_pos.mpr hu)) (mul_pos hG hH))).2
  simpa using hsmall
end D5.S3.Analytic.ReciprocalGammaTuran.Boundary

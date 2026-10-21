/- GID: D5/S3/Analytic/GaussZeroBalanced/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Positive Gauss series, contiguous identities and the zero-balanced Riccati equation. -/

import D5.S3.Analytic.GaussZeroBalanced.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Topology
open Filter Set
open D5.S3.Analytic.GaussZeroBalanced.Defs

namespace D5.S3.Analytic.GaussZeroBalanced.Series

private lemma coefficient_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (n : ℕ) : 0 < ordinaryHypergeometricCoefficient a b c n := by
  unfold ordinaryHypergeometricCoefficient
  exact mul_pos (mul_pos (mul_pos (inv_pos.mpr (by positivity))
    (ascPochhammer_pos n a ha)) (ascPochhammer_pos n b hb))
      (inv_pos.mpr (ascPochhammer_pos n c hc))

private lemma radius_eq_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (ordinaryHypergeometricSeries ℝ a b c).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact ⟨by linarith, by linarith, by linarith⟩

private lemma hasSum_gauss {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : |x| < 1) :
    HasSum (fun n : ℕ => ordinaryHypergeometricCoefficient a b c n * x ^ n)
      (gauss a b c x) := by
  have h := (ordinaryHypergeometricSeries ℝ a b c).hasSum (x := x)
  rw [radius_eq_one ha hb hc] at h
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [Metric.mem_eball, edist_dist, Real.dist_eq, ENNReal.ofReal_lt_one] using hx
  simpa [ordinaryHypergeometricSeries_apply_eq, smul_eq_mul, gauss,
    ordinaryHypergeometric, ordinaryHypergeometricSeries, mul_comm] using h hmem

/-- Positive parameters give a Gauss series bounded below by its constant term. -/
theorem one_le_gauss {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 ≤ x) (hx1 : x < 1) : 1 ≤ gauss a b c x := by
  have hs := hasSum_gauss (x := x) ha hb hc (by simpa [abs_of_nonneg hx] using hx1)
  have h := hs.summable.le_tsum 0 (fun n _ =>
    mul_nonneg (coefficient_pos ha hb hc n).le (pow_nonneg hx n))
  simpa [hs.tsum_eq, ordinaryHypergeometricCoefficient] using h

/-- The Gauss series is strictly positive for positive parameters on the unit interval. -/
theorem gauss_pos {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 ≤ x) (hx1 : x < 1) : 0 < gauss a b c x :=
  lt_of_lt_of_le zero_lt_one (one_le_gauss ha hb hc hx hx1)

private lemma poch_succ (z : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval z = z * (ascPochhammer ℝ n).eval (z + 1) := by
  rw [ascPochhammer_succ_left]
  simp

private lemma coefficient_derivative {a b c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      a * b / c * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, poch_succ, mul_inv_rev]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

private lemma hasDerivAt_gauss_abs {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hx : |x| < 1) :
    HasDerivAt (gauss a b c)
      (a * b / c * gauss (a + 1) (b + 1) (c + 1) x) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  let d : ℕ → ℝ → ℝ := fun n z =>
    (n : ℝ) * ordinaryHypergeometricCoefficient a b c n * z ^ (n - 1)
  have hd (n : ℕ) (z : ℝ) :
      d (n + 1) z = a * b / c *
        (ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n * z ^ n) := by
    simp only [d, Nat.add_sub_cancel, coefficient_derivative hc]
    ring
  have hs (z : ℝ) (hz : |z| < 1) :
      HasSum (d · z) (a * b / c * gauss (a + 1) (b + 1) (c + 1) z) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [hd, d] using
      (hasSum_gauss (by linarith : 0 < a + 1) (by linarith : 0 < b + 1)
        (by linarith : 0 < c + 1) hz).mul_left (a * b / c)
  have hder : HasDerivAt
      (fun z => ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n * z ^ n)
      (∑' n : ℕ, d n x) x := by
    apply hasDerivAt_tsum_of_isPreconnected (u := fun n => d n r)
      (t := Ioo (-r) r) (y₀ := 0) (hs r (by simpa [abs_of_pos hr] using hr1)).summable
      isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    · intro n z _
      simpa [d, mul_assoc, mul_left_comm] using
        (hasDerivAt_pow n z).const_mul (ordinaryHypergeometricCoefficient a b c n)
    · intro n z hz
      have hzr : |z| ≤ r := (abs_lt.mpr hz).le
      have hc0 : 0 ≤ (n : ℝ) * ordinaryHypergeometricCoefficient a b c n :=
        mul_nonneg (Nat.cast_nonneg n) (coefficient_pos ha hb hc n).le
      change ‖((n : ℝ) * ordinaryHypergeometricCoefficient a b c n) * z ^ (n - 1)‖ ≤ _
      rw [norm_mul, norm_pow, Real.norm_eq_abs,
        abs_of_nonneg hc0, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hzr _) hc0
    · exact ⟨by linarith, hr⟩
    · exact (hasSum_gauss ha hb hc (by norm_num : |(0 : ℝ)| < 1)).summable
    · exact abs_lt.mp hxr
  rw [(hs x hx).tsum_eq] at hder
  change HasDerivAt (fun z => gauss a b c z) _ x
  simpa only [gauss, ordinaryHypergeometric_eq_tsum, smul_eq_mul,
    ordinaryHypergeometricCoefficient] using hder

/-- Differentiation in the series variable, including the analytic point zero. -/
theorem hasDerivAt_gauss {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (gauss a b c)
      (a * b / c * gauss (a + 1) (b + 1) (c + 1) x) x :=
  hasDerivAt_gauss_abs ha hb hc (by simpa [abs_of_nonneg hx] using hx1)

end D5.S3.Analytic.GaussZeroBalanced.Series

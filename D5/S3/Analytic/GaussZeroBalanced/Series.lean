/- GID: D5/S3/Analytic/GaussZeroBalanced/Series
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Series
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.SmoothSeries, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Pow, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Inv, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Positive Gauss series, contiguous identities and the zero-balanced Riccati equation. -/

import D5.S3.Analytic.GaussZeroBalanced.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
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


private lemma coefficient_c_succ {a b c : ℝ} (hc : 0 < c) (n : ℕ) :
    (c + n) * ordinaryHypergeometricCoefficient a b (c + 1) n =
      c * ordinaryHypergeometricCoefficient a b c n := by
  have hp : c * (ascPochhammer ℝ n).eval (c + 1) =
      (ascPochhammer ℝ n).eval c * (c + n) := by
    rw [← poch_succ, ascPochhammer_succ_eval]
  have hp0 := (ascPochhammer_pos n c hc).ne'
  have hp1 := (ascPochhammer_pos n (c + 1) (by linarith)).ne'
  unfold ordinaryHypergeometricCoefficient
  field_simp
  linear_combination -(ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b * hp

private lemma coefficient_recurrence {a b c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * ordinaryHypergeometricCoefficient a b c (n + 1) * (c + n) =
      (a + n) * (b + n) * ordinaryHypergeometricCoefficient a b c n := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcn : c + n ≠ 0 := by positivity
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  field_simp

private lemma hasSum_deriv_gauss {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      ordinaryHypergeometricCoefficient a b c (n + 1) * x ^ n)
      (deriv (gauss a b c) x) := by
  rw [(hasDerivAt_gauss ha hb hc hx hx1).deriv]
  convert (hasSum_gauss (x := x) (by linarith : 0 < a + 1) (by linarith : 0 < b + 1)
      (by linarith : 0 < c + 1) (by simpa [abs_of_nonneg hx] using hx1)).mul_left (a * b / c) using 1
  ext n
  rw [coefficient_derivative hc]
  ring

private lemma hasSum_x_deriv_gauss {a b c x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => (n : ℝ) * ordinaryHypergeometricCoefficient a b c n * x ^ n)
      (x * deriv (gauss a b c) x) := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    (hasSum_deriv_gauss ha hb hc hx hx1).mul_left x

/-- The first contiguous identity for the denominator-parameter shift. -/
theorem contiguous_G {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    x * deriv (gauss a b (a + b + 1)) x =
      (a + b) * (gauss a b (a + b) x - gauss a b (a + b + 1) x) := by
  have hc : 0 < a + b := by positivity
  have h := hasSum_x_deriv_gauss ha hb (by linarith : 0 < a + b + 1) hx hx1
  have h0 := hasSum_gauss (x := x) ha hb hc (by simpa [abs_of_nonneg hx] using hx1)
  have h1 := hasSum_gauss (x := x) ha hb (by linarith : 0 < a + b + 1)
    (by simpa [abs_of_nonneg hx] using hx1)
  apply h.unique
  convert (h0.sub h1).mul_left (a + b) using 1
  ext n
  have he := coefficient_c_succ (a := a) (b := b) hc n
  nlinarith [congrArg (fun z : ℝ => z * x ^ n) he]

/-- The second contiguous identity in the zero-balanced case. -/
theorem contiguous_H {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    (1 - x) * deriv (gauss a b (a + b)) x =
      (a * b / (a + b)) * gauss a b (a + b + 1) x := by
  have hc : 0 < a + b := by positivity
  have h0 := hasSum_deriv_gauss ha hb hc hx hx1
  have h1 := hasSum_x_deriv_gauss ha hb hc hx hx1
  have h2 := hasSum_gauss (x := x) ha hb (by linarith : 0 < a + b + 1)
    (by simpa [abs_of_nonneg hx] using hx1)
  have he (n : ℕ) :
      ((n + 1 : ℕ) : ℝ) * ordinaryHypergeometricCoefficient a b (a + b) (n + 1) -
        n * ordinaryHypergeometricCoefficient a b (a + b) n =
          a * b / (a + b) * ordinaryHypergeometricCoefficient a b (a + b + 1) n := by
    have hrec := coefficient_recurrence (a := a) (b := b) hc n
    have hshift := coefficient_c_succ (a := a) (b := b) hc n
    have hcn : 0 < a + b + (n : ℝ) := by positivity
    apply (mul_right_cancel₀ hcn.ne')
    have hr : a * b / (a + b) * ordinaryHypergeometricCoefficient a b (a + b + 1) n *
        (a + b + n) = a * b * ordinaryHypergeometricCoefficient a b (a + b) n := by
      calc
        _ = a * b / (a + b) * ((a + b + n) *
            ordinaryHypergeometricCoefficient a b (a + b + 1) n) := by ring
        _ = a * b / (a + b) * ((a + b) *
            ordinaryHypergeometricCoefficient a b (a + b) n) := by rw [hshift]
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hc.ne']
    rw [hr]
    linear_combination hrec
  have h3 : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * ordinaryHypergeometricCoefficient a b (a + b) (n + 1) * x ^ n -
        n * ordinaryHypergeometricCoefficient a b (a + b) n * x ^ n)
      (a * b / (a + b) * gauss a b (a + b + 1) x) := by
    convert h2.mul_left (a * b / (a + b)) using 1
    ext n
    rw [← mul_sub_right_distrib, he]
    ring
  have hu := (h0.sub h1).unique h3
  nlinarith [hu]


/-- The contiguous quotient equals one at the series origin. -/
theorem f_zero (a b : ℝ) : f a b 0 = 1 := by
  simp [f, gauss]

/-- The contiguous quotient is positive. -/
theorem f_pos {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) : 0 < f a b x := by
  exact div_pos (gauss_pos ha hb (by positivity) hx hx1)
    (gauss_pos ha hb (by positivity) hx hx1)

/-- The contiguous quotient is strictly below its origin value at positive arguments. -/
theorem f_lt_one {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hx1 : x < 1) : f a b x < 1 := by
  have hH := gauss_pos ha hb (add_pos ha hb) hx.le hx1
  apply (div_lt_one hH).mpr
  have hd := (hasDerivAt_gauss ha hb (by positivity : 0 < a + b + 1) hx.le hx1).deriv
  have hp := gauss_pos (by linarith : 0 < a + 1) (by linarith : 0 < b + 1)
    (by positivity : 0 < a + b + 1 + 1) hx.le hx1
  have hdp : 0 < deriv (gauss a b (a + b + 1)) x := by
    rw [hd]
    exact mul_pos (div_pos (mul_pos ha hb) (by positivity)) hp
  have h := contiguous_G ha hb hx.le hx1
  have hc : 0 < a + b := add_pos ha hb
  have hdiff : 0 < gauss a b (a + b) x - gauss a b (a + b + 1) x := by
    exact (mul_pos_iff_of_pos_left hc).mp (h ▸ mul_pos hx hdp)
  linarith

/-- The quotient rule at all nonnegative arguments below one. -/
theorem hasDerivAt_f {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) :
    HasDerivAt (f a b)
      ((deriv (gauss a b (a + b + 1)) x * gauss a b (a + b) x -
        gauss a b (a + b + 1) x * deriv (gauss a b (a + b)) x) /
          (gauss a b (a + b) x) ^ 2) x := by
  exact (hasDerivAt_gauss ha hb (by positivity : 0 < a + b + 1) hx hx1).differentiableAt.hasDerivAt.div
    (hasDerivAt_gauss ha hb (add_pos ha hb) hx hx1).differentiableAt.hasDerivAt
    (gauss_pos ha hb (add_pos ha hb) hx hx1).ne'

/-- Continuity of the contiguous quotient on the interval including its origin. -/
theorem continuousOn_f {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (f a b) (Ico 0 1) := by
  intro x hx
  exact (hasDerivAt_f ha hb hx.1 hx.2).continuousAt.continuousWithinAt

/-- The Gauss quotient is the contiguous quotient divided by one minus the argument. -/
theorem quot_eq {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hx1 : x < 1) : quot a b x = f a b x / (1 - x) := by
  have h := contiguous_H ha hb hx hx1
  rw [(hasDerivAt_gauss ha hb (add_pos ha hb) hx hx1).deriv] at h
  have hk : a * b / (a + b) ≠ 0 := (div_pos (mul_pos ha hb) (add_pos ha hb)).ne'
  have he : (1 - x) * gauss (a + 1) (b + 1) (a + b + 1) x =
      gauss a b (a + b + 1) x := by
    apply mul_left_cancel₀ hk
    nlinarith [h]
  have hH := (gauss_pos ha hb (add_pos ha hb) hx hx1).ne'
  have h1 : 1 - x ≠ 0 := by linarith
  unfold quot f
  field_simp
  nlinarith [he]

/-- The zero-balanced contiguous quotient satisfies the Riccati differential equation. -/
theorem riccati {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hx1 : x < 1) :
    x * deriv (f a b) x = (a + b) * (1 - f a b x) -
      (a * b / (a + b)) * (x / (1 - x)) * (f a b x) ^ 2 := by
  rw [(hasDerivAt_f ha hb hx.le hx1).deriv]
  have h1 : 1 - x ≠ 0 := by linarith
  have hH := (gauss_pos ha hb (add_pos ha hb) hx.le hx1).ne'
  have hG := contiguous_G ha hb hx.le hx1
  have hD := contiguous_H ha hb hx.le hx1
  have hd : deriv (gauss a b (a + b)) x =
      (a * b / (a + b)) * gauss a b (a + b + 1) x / (1 - x) := by
    apply (eq_div_iff h1).mpr
    nlinarith [hD]
  unfold f
  rw [show x * ((deriv (gauss a b (a + b + 1)) x * gauss a b (a + b) x -
      gauss a b (a + b + 1) x * deriv (gauss a b (a + b)) x) /
      gauss a b (a + b) x ^ 2) =
    ((x * deriv (gauss a b (a + b + 1)) x) * gauss a b (a + b) x -
      x * gauss a b (a + b + 1) x * deriv (gauss a b (a + b)) x) /
      gauss a b (a + b) x ^ 2 by ring]
  rw [hG, hd]
  field_simp

/-- The initial slope of the contiguous quotient. -/
theorem deriv_f_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (f a b) 0 = -(a * b / ((a + b) * (a + b + 1))) := by
  rw [(hasDerivAt_f ha hb (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)).deriv,
    (hasDerivAt_gauss ha hb (by positivity : 0 < a + b + 1)
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)).deriv,
    (hasDerivAt_gauss ha hb (add_pos ha hb)
      (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)).deriv]
  simp only [gauss, ordinaryHypergeometric_zero, mul_one, one_mul, one_pow, div_one]
  field_simp; ring

end D5.S3.Analytic.GaussZeroBalanced.Series

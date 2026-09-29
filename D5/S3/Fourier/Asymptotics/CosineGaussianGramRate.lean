/- GID: D5/S3/Fourier/Asymptotics/CosineGaussianGramRate
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineGaussianGramRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian-weighted cosine-integral Gram products have uniform inverse-radius error. -/

import D5.S3.Fourier.Asymptotics.CosineIntegralGram

open MeasureTheory Set Filter
open D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)

namespace D5.S3.Fourier.Asymptotics.CosineGaussianGramRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Gaussian weighting preserves integrability and approximates the exact Gram integral
with an explicit error, uniformly when the two positive scales stay away from zero. -/
theorem result : ∀ a b beta R : ℝ, 0 < a → 0 < b → 0 < beta → 0 < R →
    Integrable (fun z : ℝ =>
      cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        Real.exp (-beta * (z / R) ^ 2)) ∧
    |(∫ z : ℝ, cosineIntegral (a * |z|) * cosineIntegral (b * |z|) *
        Real.exp (-beta * (z / R) ^ 2)) - Real.pi / max a b| ≤
      8 * (beta + 1) / (a * b * R) := by
  intro a b beta R ha hb hbeta hR
  obtain ⟨hf, hmass⟩ := CosineIntegralGram.result a b ha hb
  let f : ℝ → ℝ := fun z => cosineIntegral (a * |z|) * cosineIntegral (b * |z|)
  let w : ℝ → ℝ := fun z => Real.exp (-beta * (z / R) ^ 2)
  have hw (z : ℝ) : 0 ≤ w z ∧ w z ≤ 1 := by
    refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta.le) (sq_nonneg _)
  have hwcont : Continuous w := by dsimp [w]; fun_prop
  have hfw : Integrable (fun z => f z * w z) :=
    hf.mul_bdd hwcont.aestronglyMeasurable (Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw z).1]
      exact (hw z).2))
  refine ⟨hfw, ?_⟩
  -- The sine-tail definition gives a bound at every positive argument.
  have hCi (x : ℝ) (hx : 0 < x) : |cosineIntegral x| ≤ 2 / x := by
    have ht : |∫ t in Ioi x, Real.sin t / t ^ 2| ≤ 1 / x := by
      have h := norm_integral_le_of_norm_le
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx)
        (f := fun t : ℝ => Real.sin t / t ^ 2) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : 0 < t := hx.trans ht
          rw [norm_div, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_of_pos ht0,
            Real.rpow_neg ht0.le, Real.rpow_two]
          simpa [one_div] using
            div_le_div_of_nonneg_right (Real.abs_sin_le_one t) (sq_nonneg t))
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx] at h
      norm_num [Real.rpow_neg_one, Real.norm_eq_abs, one_div] at h ⊢
      exact h
    have hs : |Real.sin x / x| ≤ 1 / x := by
      rw [abs_div, abs_of_pos hx]
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hx.le
    exact (abs_sub _ _).trans ((add_le_add hs ht).trans_eq (by ring))
  have hfbound (z : ℝ) (hz : 0 < z) : |f z| ≤ 4 / (a * b * z ^ 2) := by
    dsimp [f]
    rw [abs_mul, abs_of_pos hz]
    calc
      |cosineIntegral (a*z)| * |cosineIntegral (b*z)| ≤ (2/(a*z)) * (2/(b*z)) :=
        mul_le_mul (hCi _ (mul_pos ha hz)) (hCi _ (mul_pos hb hz))
          (abs_nonneg _) (by positivity)
      _ = 4 / (a*b*z^2) := by ring
  have hdecrement (z : ℝ) : 0 ≤ 1 - w z ∧
      1 - w z ≤ beta * (z / R)^2 ∧ 1 - w z ≤ 1 := by
    have he := Real.add_one_le_exp (-beta * (z / R)^2)
    dsimp [w] at *
    exact ⟨sub_nonneg.mpr (hw z).2, by linarith, by linarith [(hw z).1]⟩
  let e : ℝ → ℝ := fun z => f z * (w z - 1)
  have he : Integrable e := by
    convert hfw.sub hf using 1
    funext z
    dsimp [e]
    ring
  have heabs (z : ℝ) : |e z| = |f z| * (1 - w z) := by
    dsimp [e]
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (hw z).2)]
    ring
  have hnear (z : ℝ) (hz : 0 < z) : |e z| ≤ 4 * beta / (a * b * R^2) := by
    rw [heabs]
    calc
      |f z| * (1-w z) ≤ (4/(a*b*z^2)) * (beta*(z/R)^2) :=
        mul_le_mul (hfbound z hz) (hdecrement z).2.1
          (hdecrement z).1 (by positivity)
      _ = 4*beta/(a*b*R^2) := by field_simp
  have hfar (z : ℝ) (hz : 0 < z) : |e z| ≤ (4/(a*b)) * z^(-2 : ℝ) := by
    rw [heabs]
    calc
      |f z| * (1-w z) ≤ (4/(a*b*z^2)) * 1 :=
        mul_le_mul (hfbound z hz) (hdecrement z).2.2
          (hdecrement z).1 (by positivity)
      _ = (4/(a*b)) * z^(-2 : ℝ) := by
        rw [Real.rpow_neg hz.le, Real.rpow_two]
        ring
  have hsmall : (∫ z in (0 : ℝ)..R, |e z|) ≤ 4*beta/(a*b*R) := by
    calc
      (∫ z in (0 : ℝ)..R, |e z|) ≤ ∫ _z in (0 : ℝ)..R, 4*beta/(a*b*R^2) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hR.le he.abs.intervalIntegrable
          intervalIntegrable_const (fun z hz => hnear z hz.1)
      _ = 4*beta/(a*b*R) := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        field_simp
  have htail : (∫ z in Ioi R, |e z|) ≤ 4/(a*b*R) := by
    calc
      (∫ z in Ioi R, |e z|) ≤ ∫ z in Ioi R, (4/(a*b))*z^(-2 : ℝ) :=
        setIntegral_mono_on he.abs.integrableOn
          ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul _)
          measurableSet_Ioi (fun z hz => hfar z (hR.trans hz))
      _ = 4/(a*b*R) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
        norm_num [Real.rpow_neg_one]
        ring
  have heven : (∫ z : ℝ, |e z|) = 2 * ∫ z in Ioi (0 : ℝ), |e z| := by
    convert (integral_comp_abs (f := fun z => |e z|)) using 1
    congr 1
    funext z
    simp [e, f, w, div_pow, sq_abs]
  have herr : (∫ z : ℝ, f z * w z) - Real.pi / max a b = ∫ z : ℝ, e z := by
    rw [← hmass, ← integral_sub hfw hf]
    congr 1
    funext z
    dsimp [e, f]
    ring
  rw [herr]
  calc
    |∫ z : ℝ, e z| ≤ ∫ z : ℝ, |e z| := abs_integral_le_integral_abs
    _ = 2 * ((∫ z in (0 : ℝ)..R, |e z|) + ∫ z in Ioi R, |e z|) := by
      rw [heven, intervalIntegral.integral_interval_add_Ioi he.abs.integrableOn he.abs.integrableOn]
    _ ≤ 2 * (4*beta/(a*b*R) + 4/(a*b*R)) := by linarith
    _ = 8*(beta+1)/(a*b*R) := by ring

end D5.S3.Fourier.Asymptotics.CosineGaussianGramRate

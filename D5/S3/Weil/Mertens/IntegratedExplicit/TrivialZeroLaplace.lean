/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/TrivialZeroLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full trivial zero correction, coefficient mass and Laplace transform. -/
/- Complete trivial-zero source candidate; final admission pending.
   Exact full trivial-zero correction, including its total coefficient mass.
   Supplied APIs are pinned to Mathlib56a00585/project26623eee/coref024c589. -/
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit

/-- The index n represents j=n+1, so no totalized j=0 term is introduced. -/
def trivialCoeff (n : ℕ) : ℝ :=
  1 / (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1))

/-- Every trivial-zero term, on its actual half-axis of convergence. -/
def trivialT (y : ℝ) : ℝ :=
  ∑' n : ℕ, trivialCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)

theorem trivialCoeff_nonneg (n : ℕ) : 0 ≤ trivialCoeff n := by
  dsimp only [trivialCoeff]
  positivity

private theorem half_integerComplement : (1 / 2 : ℂ) ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hr := congrArg Complex.re hn
  norm_num at hr
  have hn0 : (0 : ℤ) < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
  have hn1 : n < (1 : ℤ) := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
  omega

/-- The exact coefficient constant follows from the existing digamma series at 1/2.
The series is absolutely convergent; no conditionally convergent regrouping occurs. -/
theorem trivialCoeff_hasSum : HasSum trivialCoeff (1 - Real.log 2) := by
  have hc : HasSum (fun n : ℕ => (trivialCoeff n : ℂ))
      ((1 - Real.log 2 : ℝ) : ℂ) := by
    convert (Zeta23.DigammaSeries.hasSum_digamma_series half_integerComplement).mul_right (1 / 2 : ℂ) using 1
    · funext n
      have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have hn' : (1 / 2 : ℂ) + n + 1 ≠ 0 := by
        intro e
        have hr := congrArg Complex.re e
        norm_num at hr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      simp only [trivialCoeff, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
      field_simp [hn, hn']
      <;> ring_nf
      have hd : (3 : ℂ) + (n : ℂ) * 2 ≠ 0 := by
        intro e
        have hr := congrArg Complex.re e
        simp at hr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      field_simp [hd]
      <;> ring
    · have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
        (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
      rw [Complex.digamma_one_half, hlog]
      push_cast
      ring
  simpa only [Complex.ofReal_re] using Complex.hasSum_re hc

theorem trivialT_summable {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun n : ℕ => trivialCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) := by
  apply Summable.of_norm_bounded trivialCoeff_hasSum.summable
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (trivialCoeff_nonneg n)
    (Real.exp_nonneg _))]
  exact mul_le_of_le_one_right (trivialCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))

theorem trivialT_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ trivialT y := by
  exact tsum_nonneg (fun n => mul_nonneg (trivialCoeff_nonneg n) (Real.exp_nonneg _))

theorem trivialT_le_mass {y : ℝ} (hy : 0 ≤ y) : trivialT y ≤ 1 - Real.log 2 := by
  rw [← trivialCoeff_hasSum.tsum_eq]
  apply (trivialT_summable hy).tsum_le_tsum _ trivialCoeff_hasSum.summable
  intro n
  exact mul_le_of_le_one_right (trivialCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))

/-- Uniform absolute convergence includes the endpoint y=0. -/
theorem trivialT_continuousOn : ContinuousOn trivialT (Ici 0) := by
  apply continuousOn_tsum (fun n => (show Continuous (fun y : ℝ =>
    trivialCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) by fun_prop).continuousOn)
    trivialCoeff_hasSum.summable
  intro n y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (trivialCoeff_nonneg n)
    (Real.exp_nonneg _))]
  exact mul_le_of_le_one_right (trivialCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))

theorem trivialT_continuousAt {y : ℝ} (hy : 0 < y) : ContinuousAt trivialT y :=
  trivialT_continuousOn.continuousAt (Ici_mem_nhds hy)

/-- The entire correction is norm integrable after damping; the pointwise
majorant is the proved exact positive coefficient mass. -/
theorem trivialT_laplace_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * (trivialT y : ℂ)) (Ioi 0) := by
  have hb := (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul (1 - Real.log 2)
  refine hb.mono' ?_ ?_
  · have hc : ContinuousOn (fun y : ℝ => Complex.exp (-s * y) * (trivialT y : ℂ))
        (Ioi 0) := by
      apply ContinuousOn.mul (by fun_prop)
      exact Complex.continuous_ofReal.comp_continuousOn
        (trivialT_continuousOn.mono Ioi_subset_Ici_self)
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    calc
      ‖Complex.exp (-s * y) * (trivialT y : ℂ)‖ =
          Real.exp (-s.re * y) * trivialT y := by
        simp [norm_mul, Complex.norm_exp, abs_of_nonneg (trivialT_nonneg hy.le)]
      _ ≤ Real.exp (-s.re * y) * (1 - Real.log 2) :=
        mul_le_mul_of_nonneg_left (trivialT_le_mass hy.le) (Real.exp_nonneg _)
      _ = _ := mul_comm _ _

/-- Absolute dominated exchange for every term of the full trivial-zero series. -/
theorem trivialT_laplace_hasSum {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (trivialCoeff n : ℂ) / (s + 2 * ((n : ℂ) + 1)))
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * (trivialT y : ℂ)) := by
  let f : ℕ → ℝ → ℂ := fun n y => (trivialCoeff n : ℂ) *
    Complex.exp (-(s + 2 * ((n : ℂ) + 1)) * y)
  let b : ℕ → ℝ → ℝ := fun n y => trivialCoeff n * Real.exp (-s.re * y)
  have hmeas : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    exact (show Continuous (f n) by dsimp only [f]; fun_prop).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ‖f n y‖ ≤ b n y := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    dsimp only [f, b]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (trivialCoeff_nonneg n), Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (trivialCoeff_nonneg n)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.natCast_re, Complex.re_ofNat,
      Complex.one_re]
    simp only [Complex.im_ofNat, Complex.add_im, Complex.natCast_im,
      Complex.one_im, zero_add, add_zero, zero_mul, sub_zero]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, (show 0 < y from hy)]
  have hb : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), Summable (fun n => b n y) :=
    ae_of_all _ (fun y => trivialCoeff_hasSum.summable.mul_right _)
  have hbi : Integrable (fun y => ∑' n, b n y) (volume.restrict (Ioi 0)) := by
    simpa only [b, tsum_mul_right, trivialCoeff_hasSum.tsum_eq] using
      (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul (1 - Real.log 2)
  have hlim : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), HasSum (fun n => f n y)
      (Complex.exp (-s * y) * (trivialT y : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hreal := Complex.hasSum_ofReal.mpr (trivialT_summable hy.le).hasSum
    have he := hreal.mul_left (Complex.exp (-s * y))
    convert he using 1
    · funext n
      dsimp only [f]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_add,
        Complex.ofReal_natCast, Complex.ofReal_one]
      rw [show -(s + 2 * ((n : ℂ) + 1)) * (y : ℂ) =
        -s * y + -(2 * ((n : ℂ) + 1)) * y by ring, Complex.exp_add]
      ring
    · rfl
  have h := hasSum_integral_of_dominated_convergence b hmeas hbound hb hbi hlim
  convert h using 1
  funext n
  dsimp only [f]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.one_re, Complex.im_ofNat, Complex.natCast_im,
      Complex.one_im, add_zero, mul_zero, sub_zero]
    linarith [Nat.cast_nonneg (α := ℝ) n])]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg,
    div_eq_mul_inv, one_mul, inv_neg, neg_mul_neg]

/-- The per-term cancellation paying the complete trivial-zero transform. -/
theorem trivial_partial_fraction (j s : ℂ) (hj : j ≠ 0)
    (hj1 : 2 * j + 1 ≠ 0) (hsj : s + 2 * j ≠ 0) :
    1 / (2 * j * (s + 2 * j)) +
      (s - 1) / (2 * j * (2 * j + 1) * (s + 2 * j)) =
        1 / (2 * j * (2 * j + 1)) := by
  field_simp [hj, hj1, hsj]
  <;> ring

end D5.S3.Weil.Mertens.IntegratedExplicit
end

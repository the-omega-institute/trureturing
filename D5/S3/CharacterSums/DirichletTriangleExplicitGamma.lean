/- GID: D5/S3/CharacterSums/DirichletTriangleExplicitGamma
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletTriangleExplicitGamma
   mirror-E: none(waiver:dirichlet-archimedean-transform)
   anchors: []
   utility: none
   digest: Parity corrections and their absolutely convergent Laplace transforms. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.TrivialZeroLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! The two parity corrections retain the complete trivial-zero tails. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Complex
open scoped BigOperators Topology
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane

namespace D5.S3.CharacterSums.DirichletTriangleExplicit

/-- Coefficients for the even trivial zeros, indexed from the first positive integer. -/
def evenCoeff (n : ℕ) : ℝ :=
  1 / (2 * ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) - 1))

/-- The even trivial-zero tail on the logarithmic half-axis. -/
def evenT (y : ℝ) : ℝ :=
  ∑' n : ℕ, evenCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)

private theorem evenCoeff_nonneg (n : ℕ) : 0 ≤ evenCoeff n := by
  unfold evenCoeff
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))

private theorem neg_half_integerComplement : -(1 / 2 : ℂ) ∈ integerComplement := by
  rintro ⟨n, hn⟩
  have hr := congrArg Complex.re hn
  norm_num at hr
  have hn0 : n < (0 : ℤ) := by exact_mod_cast (show (n : ℝ) < 0 by linarith)
  have hn1 : (-1 : ℤ) < n := by exact_mod_cast (show (-1 : ℝ) < n by linarith)
  omega

private theorem digamma_neg_half : digamma (-(1 / 2 : ℂ)) =
    -2 * (Real.log 2 : ℂ) - (Real.eulerMascheroniConstant : ℂ) + 2 := by
  have hh := digamma_apply_add_one (-(1 / 2 : ℂ)) (by
    intro n he
    have hr := congrArg Complex.re he
    norm_num at hr
    have hn : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
    have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by linarith)
    omega)
  norm_num only [show -(1 / 2 : ℂ) + 1 = 1 / 2 by norm_num,
    one_div_neg, one_div_div, div_one] at hh
  rw [digamma_one_half, show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm] at hh
  linear_combination -hh

private theorem evenCoeff_hasSum : HasSum evenCoeff (Real.log 2) := by
  have hc : HasSum (fun n : ℕ => (evenCoeff n : ℂ)) (Real.log 2 : ℂ) := by
    convert (Zeta23.DigammaSeries.hasSum_digamma_series
      neg_half_integerComplement).mul_right (-(1 / 2 : ℂ)) using 1
    · funext n
      have hn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      have hn' : 2 * ((n : ℂ) + 1) - 1 ≠ 0 := by
        intro he
        have hr := congrArg Complex.re he
        simp at hr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have he : -(1 / 2 : ℂ) + n + 1 = (2 * ((n : ℂ) + 1) - 1) / 2 := by ring
      simp only [evenCoeff, Complex.ofReal_div, Complex.ofReal_mul,
        Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_natCast,
        Complex.ofReal_one, Complex.ofReal_ofNat]
      rw [he]
      field_simp [hn, hn']
      <;> ring
    · rw [digamma_neg_half]
      norm_num
      ring
  simpa only [Complex.ofReal_re] using Complex.hasSum_re hc

private theorem evenT_summable {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun n : ℕ => evenCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) := by
  apply Summable.of_norm_bounded evenCoeff_hasSum.summable
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (evenCoeff_nonneg n)
    (Real.exp_nonneg _))]
  exact mul_le_of_le_one_right (evenCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))

theorem evenT_nonneg (y : ℝ) : 0 ≤ evenT y :=
  tsum_nonneg (fun n => mul_nonneg (evenCoeff_nonneg n) (Real.exp_nonneg _))

theorem evenT_le_mass {y : ℝ} (hy : 0 ≤ y) :
    Summable (fun n : ℕ => evenCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) ∧
      evenT 0 = Real.log 2 ∧ evenT y ≤ Real.log 2 := by
  refine ⟨evenT_summable hy, ?_, ?_⟩
  · simpa [evenT] using evenCoeff_hasSum.tsum_eq
  ·   rw [← evenCoeff_hasSum.tsum_eq]
    apply (evenT_summable hy).tsum_le_tsum _ evenCoeff_hasSum.summable
    intro n
    exact mul_le_of_le_one_right (evenCoeff_nonneg n)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))
private theorem evenT_continuousOn : ContinuousOn evenT (Ici 0) := by
  apply continuousOn_tsum (fun n => (show Continuous (fun y : ℝ =>
    evenCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) by fun_prop).continuousOn)
    evenCoeff_hasSum.summable
  intro n y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (evenCoeff_nonneg n)
    (Real.exp_nonneg _))]
  exact mul_le_of_le_one_right (evenCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hy))

private theorem evenT_laplace_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => exp (-s * y) * (evenT y : ℂ)) (Ioi 0) := by
  have hb := (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul
    (Real.log 2)
  refine hb.mono' ?_ ?_
  · exact ((show ContinuousOn (fun y : ℝ => exp (-s * y)) (Ioi 0) by fun_prop).mul
      (Complex.continuous_ofReal.comp_continuousOn
        (evenT_continuousOn.mono Ioi_subset_Ici_self))).aestronglyMeasurable
          measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    calc
      ‖exp (-s * y) * (evenT y : ℂ)‖ = Real.exp (-s.re * y) * evenT y := by
        simp [norm_mul, Complex.norm_exp, abs_of_nonneg (evenT_nonneg y)]
      _ ≤ Real.exp (-s.re * y) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (evenT_le_mass hy.le).2.2 (Real.exp_nonneg _)
      _ = _ := mul_comm _ _

private theorem evenT_laplace_hasSum {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (evenCoeff n : ℂ) / (s + 2 * ((n : ℂ) + 1)))
      (∫ y : ℝ in Ioi 0, exp (-s * y) * (evenT y : ℂ)) := by
  let f : ℕ → ℝ → ℂ := fun n y => (evenCoeff n : ℂ) *
    exp (-(s + 2 * ((n : ℂ) + 1)) * y)
  let b : ℕ → ℝ → ℝ := fun n y => evenCoeff n * Real.exp (-s.re * y)
  have hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioi 0)) := by
    intro n
    exact (show Continuous (f n) by dsimp [f]; fun_prop).aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), ‖f n y‖ ≤ b n y := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    dsimp only [f, b]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (evenCoeff_nonneg n), Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (evenCoeff_nonneg n)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.re_ofNat, Complex.one_re,
      Complex.im_ofNat, Complex.natCast_im, Complex.one_im, zero_add, add_zero,
      mul_zero, zero_mul, sub_zero]
    nlinarith [Nat.cast_nonneg (α := ℝ) n, (show 0 < y from hy)]
  have hbs : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), Summable (fun n => b n y) :=
    ae_of_all _ (fun y => evenCoeff_hasSum.summable.mul_right _)
  have hbi : Integrable (fun y => ∑' n, b n y) (volume.restrict (Ioi 0)) := by
    simpa only [b, tsum_mul_right, evenCoeff_hasSum.tsum_eq] using
      (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0).const_mul (Real.log 2)
  have hlim : ∀ᵐ y : ℝ ∂volume.restrict (Ioi 0), HasSum (fun n => f n y)
      (exp (-s * y) * (evenT y : ℂ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have he := (Complex.hasSum_ofReal.mpr (evenT_summable hy.le).hasSum).mul_left
      (exp (-s * y))
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
  have he := hasSum_integral_of_dominated_convergence b hf hb hbs hbi hlim
  convert he using 1
  funext n
  dsimp only [f]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (by
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.one_re, Complex.im_ofNat, Complex.natCast_im,
      Complex.one_im, add_zero, mul_zero, sub_zero]
    linarith [Nat.cast_nonneg (α := ℝ) n])]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg, neg_neg,
    div_eq_mul_inv, one_mul, inv_neg, neg_mul_neg]

private theorem digamma_resolvent {s : ℂ} (hs : 0 < s.re)
    (hc : s / 2 ∈ integerComplement) :
    HasSum (fun n : ℕ => 1 / (2 * ((n : ℂ) + 1) * (s + 2 * ((n : ℂ) + 1))))
      ((digamma (s / 2) / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s) := by
  have hs0 : s ≠ 0 := by intro he; rw [he] at hs; norm_num at hs
  have hdig := Zeta23.DigammaSeries.hasSum_digamma_series hc
  convert hdig.mul_right (1 / (2 * s)) using 1
  · funext n
    have hj : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hsj : s + 2 * ((n : ℂ) + 1) ≠ 0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [show s / 2 + (n : ℂ) + 1 = (s + 2 * ((n : ℂ) + 1)) / 2 by ring,
      one_div_div]
    field_simp [hj, hsj, hs0]
    <;> ring
  · field_simp [hs0]
    <;> ring

private theorem even_balance {s : ℂ} (hs : 0 < s.re)
    (hc : s / 2 ∈ integerComplement) :
    (digamma (s / 2) / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s +
      (s + 1) * (∫ y : ℝ in Ioi 0, exp (-s * y) * (evenT y : ℂ)) =
        (Real.log 2 : ℂ) := by
  have he := (digamma_resolvent hs hc).add ((evenT_laplace_hasSum hs).mul_left (s + 1))
  have hm := Complex.hasSum_ofReal.mpr evenCoeff_hasSum
  apply HasSum.unique _ hm
  convert he using 1
  funext n
  have hj : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hj1 : 2 * ((n : ℂ) + 1) - 1 ≠ 0 := by
    intro e
    have hr := congrArg Complex.re e
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsj : s + 2 * ((n : ℂ) + 1) ≠ 0 := by
    intro e
    have hr := congrArg Complex.re e
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [evenCoeff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp [hj, hj1, hsj]
  <;> ring

private theorem odd_balance {s : ℂ} (hs : 0 < s.re)
    (hc : s / 2 ∈ integerComplement) :
    (digamma (s / 2) / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s +
      (s - 1) * (∫ y : ℝ in Ioi 0, exp (-s * y) * (trivialT y : ℂ)) =
        ((1 - Real.log 2 : ℝ) : ℂ) := by
  have he := (digamma_resolvent hs hc).add ((trivialT_laplace_hasSum hs).mul_left (s - 1))
  have hm := Complex.hasSum_ofReal.mpr trivialCoeff_hasSum
  apply HasSum.unique _ hm
  convert he using 1
  funext n
  have hj : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hj1 : 2 * ((n : ℂ) + 1) + 1 ≠ 0 := by
    intro e
    have hr := congrArg Complex.re e
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsj : s + 2 * ((n : ℂ) + 1) ≠ 0 := by
    intro e
    have hr := congrArg Complex.re e
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simp only [trivialCoeff, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp [hj, hj1, hsj]
  <;> ring

/-- The parity index is zero for even characters and one for odd characters. -/
def parity {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact if χ.Even then 0 else 1

/-- The correction includes both endpoint finite parts and the full trivial tail. -/
def parityCorrection {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ := by
  classical
  exact if χ.Even then
    ((1 - Real.log x + (Real.log 2 - 1) / x - evenT (Real.log x) : ℝ) : ℂ)
  else
    ((-1 + (Real.log x + 2 - Real.log 2) / x -
      trivialT (Real.log x) / x : ℝ) : ℂ)

/-- Both endpoint corrections vanish at the initial arithmetic endpoint. -/
theorem parityCorrection_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    parityCorrection χ 1 = 0 := by
  classical
  have he : evenT 0 = Real.log 2 := by
    simpa [evenT] using evenCoeff_hasSum.tsum_eq
  have ho : trivialT 0 = 1 - Real.log 2 := by
    simpa [trivialT] using trivialCoeff_hasSum.tsum_eq
  by_cases hχ : χ.Even <;> simp [parityCorrection, hχ, he, ho] <;> ring

private theorem correction_exp_even {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : χ.Even) (y : ℝ) :
    parityCorrection χ (Real.exp y) =
      1 - (y : ℂ) + ((Real.log 2 : ℂ) - 1) * exp (-y) - (evenT y : ℂ) := by
  simp only [parityCorrection, if_pos hχ, Real.log_exp]
  push_cast
  rw [Complex.exp_neg]
  ring

private theorem correction_exp_odd {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : ¬χ.Even) (y : ℝ) :
    parityCorrection χ (Real.exp y) =
      -1 + ((y : ℂ) + 2 - (Real.log 2 : ℂ)) * exp (-y) -
        exp (-y) * (trivialT y : ℂ) := by
  simp only [parityCorrection, if_neg hχ, Real.log_exp]
  push_cast
  rw [Complex.exp_neg]
  ring

/-- Continuity of the logarithmic correction includes the initial endpoint. -/
theorem parityCorrection_continuousOn {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun y : ℝ => parityCorrection χ (Real.exp y)) (Ici 0) := by
  classical
  by_cases hχ : χ.Even
  · simp_rw [correction_exp_even hχ]
    exact (((continuous_const.sub Complex.continuous_ofReal).add
      (continuous_const.mul (by fun_prop))).continuousOn).sub
        (Complex.continuous_ofReal.comp_continuousOn evenT_continuousOn)
  · simp_rw [correction_exp_odd hχ]
    have he : Continuous (fun y : ℝ =>
        -1 + ((y : ℂ) + 2 - (Real.log 2 : ℂ)) * exp (-y)) := by fun_prop
    exact he.continuousOn.sub
      ((show Continuous (fun y : ℝ => exp (-(y : ℂ))) by fun_prop).continuousOn.mul
        (Complex.continuous_ofReal.comp_continuousOn trivialT_continuousOn))

theorem exp_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => exp (-s * y)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0

private theorem moment_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) * exp (-s * y)) (Ioi 0) := by
  simpa only [show (1 : ℂ) - (s + 1) = -s by ring] using
    first_moment_integrable (s := s + 1) (by simpa using hs)

theorem exp_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, exp (-s * y)) = 1 / s := by
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp

private theorem moment_integral {s : ℂ} (hs : 0 < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) * exp (-s * y)) = 1 / s ^ 2 := by
  simpa only [show (1 : ℂ) - (s + 1) = -s by ring, add_sub_cancel_right] using
    first_moment (s := s + 1) (by simpa using hs)

private theorem damp_even {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : χ.Even) (s : ℂ) (y : ℝ) :
    exp (-s * y) * parityCorrection χ (Real.exp y) =
      exp (-s * y) - (y : ℂ) * exp (-s * y) +
        ((Real.log 2 : ℂ) - 1) * exp (-(s + 1) * y) -
          exp (-s * y) * (evenT y : ℂ) := by
  rw [correction_exp_even hχ]
  rw [show -(s + 1) * (y : ℂ) = -s * y + -(y : ℂ) by ring, Complex.exp_add]
  ring

private theorem damp_odd {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hχ : ¬χ.Even) (s : ℂ) (y : ℝ) :
    exp (-s * y) * parityCorrection χ (Real.exp y) =
      -exp (-s * y) + (y : ℂ) * exp (-(s + 1) * y) +
        (2 - (Real.log 2 : ℂ)) * exp (-(s + 1) * y) -
          exp (-(s + 1) * y) * (trivialT y : ℂ) := by
  rw [correction_exp_odd hχ]
  rw [show -(s + 1) * (y : ℂ) = -s * y + -(y : ℂ) by ring, Complex.exp_add]
  ring

/-- Absolute Laplace convergence needs only a positive damping abscissa. -/
theorem parityCorrection_laplace_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun y : ℝ => exp (-s * y) * parityCorrection χ (Real.exp y)) (Ioi 0) := by
  classical
  have hs1 : 0 < (s + 1).re := by simp only [add_re, one_re]; linarith
  by_cases hχ : χ.Even
  · simp_rw [damp_even hχ]
    exact (((exp_integrable hs).sub (moment_integrable hs)).add
      ((exp_integrable hs1).const_mul _)).sub (evenT_laplace_integrable hs)
  · simp_rw [damp_odd hχ]
    exact ((((exp_integrable hs).neg).add (moment_integrable hs1)).add
      ((exp_integrable hs1).const_mul _)).sub (trivialT_laplace_integrable hs1)

private theorem line_parity_complement (t a : ℝ) (ht : t ≠ 0) :
    (transformLine t + (a : ℂ)) / 2 ∈ integerComplement := by
  rintro ⟨n, hn⟩
  have him : ((transformLine t + (a : ℂ)) / 2).im = Real.pi * t := by
    simp [transformLine, div_eq_mul_inv] <;> ring
  have he := congrArg Complex.im hn
  simp only [Complex.intCast_im, him] at he
  exact (mul_ne_zero Real.pi_ne_zero ht) he.symm

/-- The Gamma endpoint correction has the centered digamma Laplace transform. -/
theorem parityCorrection_laplace {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : t ≠ 0) :
    (∫ y : ℝ in Ioi 0, exp (-transformLine t * y) *
      parityCorrection χ (Real.exp y)) =
        (digamma ((transformLine t + parity χ) / 2) -
          digamma ((2 + parity χ) / 2)) /
            (2 * transformLine t * (transformLine t + 1)) := by
  classical
  let s := transformLine t
  have hs : 0 < s.re := by simp [s]
  have hs1 : 0 < (s + 1).re := by norm_num [s]
  have hs0 : s ≠ 0 := by intro e; have := congrArg Complex.re e; simp [s] at this
  have hs10 : s + 1 ≠ 0 := by
    intro e; have := congrArg Complex.re e; norm_num [s] at this
  change (∫ y : ℝ in Ioi 0, exp (-s * y) * parityCorrection χ (Real.exp y)) = _
  by_cases hχ : χ.Even
  · simp_rw [damp_even hχ]
    rw [integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun y : ℝ => exp (-s * y) - (y : ℂ) * exp (-s * y) +
        ((Real.log 2 : ℂ) - 1) * exp (-(s + 1) * y))
      (g := fun y : ℝ => exp (-s * y) * (evenT y : ℂ))
      (((exp_integrable hs).sub (moment_integrable hs)).add
        ((exp_integrable hs1).const_mul _)) (evenT_laplace_integrable hs),
      integral_add (f := fun y : ℝ => exp (-s * y) - (y : ℂ) * exp (-s * y))
        (g := fun y : ℝ => ((Real.log 2 : ℂ) - 1) * exp (-(s + 1) * y))
        ((exp_integrable hs).sub (moment_integrable hs))
        ((exp_integrable hs1).const_mul _),
      integral_sub (f := fun y : ℝ => exp (-s * y))
        (g := fun y : ℝ => (y : ℂ) * exp (-s * y))
        (exp_integrable hs) (moment_integrable hs), integral_const_mul,
      exp_integral hs, moment_integral hs, exp_integral hs1]
    have he := even_balance hs (by simpa [s] using line_parity_complement t 0 ht)
    simp only [parity, if_pos hχ, add_zero, show (2 : ℂ) / 2 = 1 by norm_num,
      digamma_one]
    change 1 / s - 1 / s ^ 2 + ((Real.log 2 : ℂ) - 1) * (1 / (s + 1)) - _ = _
    have hR : (∫ y : ℝ in Ioi 0, exp (-s * y) * (evenT y : ℂ)) =
        ((Real.log 2 : ℂ) -
          (digamma (s / 2) / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 + 1 / s) / s) /
            (s + 1) := (eq_div_iff hs10).2 (by linear_combination he)
    rw [hR]
    change _ = (digamma (s / 2) - -(Real.eulerMascheroniConstant : ℂ)) /
      (2 * s * (s + 1))
    field_simp [hs0, hs10]
    <;> ring
  · simp_rw [damp_odd hχ]
    rw [integral_sub (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun y : ℝ => -exp (-s * y) + (y : ℂ) * exp (-(s + 1) * y) +
        (2 - (Real.log 2 : ℂ)) * exp (-(s + 1) * y))
      (g := fun y : ℝ => exp (-(s + 1) * y) * (trivialT y : ℂ))
      ((((exp_integrable hs).neg).add (moment_integrable hs1)).add
        ((exp_integrable hs1).const_mul _)) (trivialT_laplace_integrable hs1),
      integral_add (f := fun y : ℝ => -exp (-s * y) +
          (y : ℂ) * exp (-(s + 1) * y))
        (g := fun y : ℝ => (2 - (Real.log 2 : ℂ)) * exp (-(s + 1) * y))
        (((exp_integrable hs).neg).add (moment_integrable hs1))
        ((exp_integrable hs1).const_mul _),
      integral_add (f := fun y : ℝ => -exp (-s * y))
        (g := fun y : ℝ => (y : ℂ) * exp (-(s + 1) * y))
        ((exp_integrable hs).neg) (moment_integrable hs1),
      integral_neg, integral_const_mul,
      exp_integral hs, moment_integral hs1, exp_integral hs1]
    have he := odd_balance hs1 (line_parity_complement t 1 ht)
    have hd := digamma_apply_add_one (1 / 2 : ℂ) (by
      intro n hn
      have hr := congrArg Complex.re hn
      simp at hr
      linarith [Nat.cast_nonneg (α := ℝ) n])
    norm_num only [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num,
      one_div_div, div_one] at hd
    rw [digamma_one_half, show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm] at hd
    simp only [parity, if_neg hχ, show ((2 : ℂ) + 1) / 2 = 3 / 2 by norm_num]
    rw [hd]
    change -(1 / s) + 1 / (s + 1) ^ 2 +
      (2 - (Real.log 2 : ℂ)) * (1 / (s + 1)) - _ = _
    push_cast at he
    have hR : (∫ y : ℝ in Ioi 0, exp (-(s + 1) * y) * (trivialT y : ℂ)) =
        (1 - (Real.log 2 : ℂ) -
          (digamma ((s + 1) / 2) / 2 + (Real.eulerMascheroniConstant : ℂ) / 2 +
            1 / (s + 1)) / (s + 1)) / s :=
      (eq_div_iff hs0).2 (by linear_combination he)
    rw [hR]
    change _ = (digamma ((s + 1) / 2) -
      (-2 * (Real.log 2 : ℂ) - (Real.eulerMascheroniConstant : ℂ) + 2)) /
        (2 * s * (s + 1))
    field_simp [hs0, hs10]
    <;> ring

end D5.S3.CharacterSums.DirichletTriangleExplicit

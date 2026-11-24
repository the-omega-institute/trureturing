/- GID: D5/S3/CharacterSums/DirichletTrianglePerron
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletTrianglePerron
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolutely convergent Laplace and Perron formulas for triangular character sums. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes.Integral
import D5.S3.Arith.PrimitiveRoot.CharacterSieve
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.Calculus.LogDeriv

/-! Triangular smoothing gives absolutely convergent transforms of every character. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter Complex
open scoped BigOperators Topology
open D5.S3.Weil.Mertens.IntegratedExplicit
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

namespace D5.S3.CharacterSums.DirichletTrianglePerron

/-- The inclusive triangular Mangoldt sum; its entering endpoint has weight zero. -/
def characterTriangle {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) *
    χ n * (1 - (n : ℂ) / x)

private def laplaceAtom (n : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  (n : ℂ) * (Complex.exp (-(s + 1) * y) * (mangoldtRamp n (Real.exp y) : ℂ))

private theorem atom_integrable (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (laplaceAtom n s) (Ioi 0) := by
  exact (mangoldtRamp_laplace_integrable (n := n) (s := s + 1)
    (by simpa using hs)).const_mul _

private theorem atom_integral (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (∫ y in Ioi 0, laplaceAtom n s y) =
      LSeries.term (fun k : ℕ => (ArithmeticFunction.vonMangoldt k : ℂ)) s n /
        (s * (s + 1)) := by
  simp only [laplaceAtom]
  rw [integral_const_mul, mangoldtRamp_laplace (by simpa using hs)]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    Complex.cpow_add _ _ hnC, Complex.cpow_one]
  simp only [add_sub_cancel_right]
  field_simp

private theorem atom_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y in Ioi 0, ‖laplaceAtom n s y‖) := by
  let σ : ℂ := s.re
  have hσ : 0 < σ.re := zero_lt_one.trans hs
  have he (n : ℕ) (y : ℝ) : ‖laplaceAtom n s y‖ = (laplaceAtom n σ y).re := by
    have hex : Complex.exp (-(σ + 1) * (y : ℂ)) =
        (Real.exp (-(s.re + 1) * y) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      simp [σ]
    simp only [laplaceAtom, norm_mul, Complex.norm_natCast, Complex.norm_exp,
      Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.one_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (mangoldtRamp_nonneg n _), hex]
    simp
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < σ.re from hs)).hasSum.div_const (σ * (σ + 1))
  apply (Complex.hasSum_re hsum).summable.congr
  intro n
  rw [← atom_integral n hσ]
  change RCLike.re (∫ y in Ioi 0, laplaceAtom n σ y) = _
  rw [← integral_re (atom_integrable n hσ)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun y _ => (he n y).symm)

private theorem series_integrable {F : ℕ → ℝ → ℂ} {μ : Measure ℝ}
    (hi : ∀ n, Integrable (F n) μ)
    (hn : Summable (fun n => ∫ y, ‖F n y‖ ∂μ)) :
    Integrable (fun y => ∑' n, F n y) μ := by
  have hm : AEStronglyMeasurable (fun y => ∑' n, F n y) μ :=
    (AEMeasurable.tsum (fun n => (hi n).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  refine ⟨hm, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  calc
    (∫⁻ y, ‖∑' n, F n y‖ₑ ∂μ) ≤ ∫⁻ y, ∑' n, ‖F n y‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ y, ‖F n y‖ₑ ∂μ :=
      lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)
    _ = ∑' n, ENNReal.ofReal (∫ y, ‖F n y‖ ∂μ) := by
      congr 1
      funext n
      exact (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ < ⊤ := hn.tsum_ofReal_lt_top

private theorem atom_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (y : ℝ) :
    (∑' n : ℕ, laplaceAtom n s y * χ n) =
      Complex.exp (-s * y) * characterTriangle χ (Real.exp y) := by
  have hex : Complex.exp (-(s + 1) * (y : ℂ)) =
      Complex.exp (-s * y) / (Real.exp y : ℂ) := by
    rw [Complex.ofReal_exp, div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp y⌋₊)]
  · rw [characterTriangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn0)
    rw [laplaceAtom, ramp_eq_affine hn0
      ((Nat.le_floor_iff (Real.exp_nonneg y)).mp (Finset.mem_Icc.mp hn).2), hex]
    push_cast
    field_simp
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [laplaceAtom]
    · have hnf : ⌊Real.exp y⌋₊ < n := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      simp [laplaceAtom, ramp_zero_of_lt (Real.exp_nonneg y) (Nat.lt_of_floor_lt hnf)]

private theorem twisted_norm_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y in Ioi 0, ‖laplaceAtom n s y * χ n‖) := by
  refine (atom_norm_summable hs).of_nonneg_of_le
    (fun n => integral_nonneg (fun _ => norm_nonneg _)) (fun n => ?_)
  apply integral_mono ((atom_integrable n (zero_lt_one.trans hs)).mul_const _).norm
    (atom_integrable n (zero_lt_one.trans hs)).norm
  intro y
  change ‖laplaceAtom n s y * χ n‖ ≤ ‖laplaceAtom n s y‖
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)

/-- The triangular sum has an absolutely convergent Laplace transform for Re(s) > 1. -/
theorem characterTriangle_laplace_integrable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      characterTriangle χ (Real.exp y)) (Ioi 0) := by
  have hi := series_integrable
    (fun n => (atom_integrable n (zero_lt_one.trans hs)).mul_const (χ n))
    (twisted_norm_summable χ hs)
  simpa only [IntegrableOn, atom_sum] using hi

private theorem twisted_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -logDeriv χ.LFunction s := by
  change LSeries ((fun n : ℕ => χ n) *
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) s = _
  rw [χ.LSeries_twist_vonMangoldt_eq hs, logDeriv_apply,
    χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs, neg_div]

/-- The Laplace identity holds for principal and nonprincipal characters alike. -/
theorem characterTriangle_laplace {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * characterTriangle χ (Real.exp y)) =
      -logDeriv χ.LFunction s / (s * (s + 1)) := by
  have hi (n : ℕ) := (atom_integrable n (zero_lt_one.trans hs)).mul_const (χ n)
  have he (n : ℕ) : (∫ y in Ioi 0, laplaceAtom n s y * χ n) =
      LSeries.term (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) s n /
        (s * (s + 1)) := by
    rw [integral_mul_const, atom_integral n (zero_lt_one.trans hs)]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      ring
  have hx := hasSum_integral_of_summable_integral_norm hi (twisted_norm_summable χ hs)
  simp_rw [he, atom_sum] at hx
  have hL := (χ.LSeriesSummable_twist_vonMangoldt hs).hasSum.div_const (s * (s + 1))
  change HasSum _ (LSeries
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s / (s * (s + 1))) at hL
  rw [twisted_series χ hs] at hL
  exact hx.unique hL

/-- The vertical integrand in the triangular Perron formula. -/
def trianglePerronIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (x c t : ℝ) : ℂ :=
  let s : ℂ := c + (t : ℂ) * I;
  -logDeriv χ.LFunction s * (x : ℂ) ^ s / (s * (s + 1))

private theorem perron_series_integrable {f : ℕ → ℂ} {x c : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hL : LSeriesSummable f (c : ℂ)) :
    Integrable (fun t : ℝ => LSeries f ((c : ℂ) + (t : ℂ) * I) *
      smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) := by
  have hi := series_integrable (integrable_term_mul_smoothedPerronKernel f hx hc)
    (summable_integral_norm_term_mul_smoothedPerronKernel (x := x) hL)
  simpa only [LSeries, tsum_mul_right] using hi

private theorem scaled_perron_integrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 < c) (t : ℝ) :
    (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((c : ℂ) + (t : ℂ) * I) *
      smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) / (x : ℂ) =
        trianglePerronIntegrand χ x c t := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [twisted_series χ (by simpa using hc), smoothedPerronKernel,
    Complex.cpow_add _ _ hxC, Complex.cpow_one]
  dsimp only [trianglePerronIntegrand]
  field_simp

private theorem perron_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℝ} (hc : 1 < c) (t : ℝ) : trianglePerronIntegrand χ 0 c t = 0 := by
  have hs : (c : ℂ) + (t : ℂ) * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  simp [trianglePerronIntegrand, Complex.zero_cpow hs]

/-- Absolute convergence holds on every vertical line c > 1, including x = 0. -/
theorem trianglePerronIntegrand_integrable {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    Integrable (fun t : ℝ =>
      -logDeriv χ.LFunction ((c : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
  change Integrable (trianglePerronIntegrand χ x c)
  rcases eq_or_lt_of_le hx with rfl | hx
  · have he : trianglePerronIntegrand χ 0 c = fun _ : ℝ => (0 : ℂ) :=
      funext (perron_zero χ hc)
    rw [he]
    exact integrable_zero ℝ ℂ volume
  have hL : LSeriesSummable
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt (by simpa using hc)
  have hi := (perron_series_integrable hx (zero_lt_one.trans hc)
    hL).div_const (x : ℂ)
  simpa only [scaled_perron_integrand χ hx hc] using hi

/-- The classical Perron formula with triangular weight, including 0 ≤ x ≤ 1. -/
theorem characterTriangle_perron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 ≤ x) (hc : 1 < c) :
    characterTriangle χ x =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, trianglePerronIntegrand χ x c t := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [characterTriangle, perron_zero χ hc]
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hL : LSeriesSummable
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) :=
    χ.LSeriesSummable_twist_vonMangoldt (by simpa using hc)
  have hf : characterTriangle χ x =
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) * ((x : ℂ) - (n : ℂ))) /
          (x : ℂ) := by
    rw [characterTriangle, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n _
    field_simp
  rw [hf, smoothed_perron_LSeries hx (zero_lt_one.trans hc) hL, mul_div_assoc,
    ← integral_div]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (scaled_perron_integrand χ hx hc)

/-- At an integer endpoint the inclusive sum agrees with the sieve's strict sum. -/
theorem characterTriangle_nat (p : ℕ) (χ : DirichletCharacter ℂ p) :
    characterTriangle χ p =
      D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p χ := by
  classical
  let f (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) *
    χ n * (1 - (n : ℂ) / p)
  have hrange : Finset.range (p + 1) = insert 0 (Finset.Icc 1 p) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hf : (∑ n ∈ Finset.Icc 1 p, f n) = ∑ n ∈ Finset.range (p + 1), f n := by
    rw [hrange, Finset.sum_insert (by simp)]
    simp [f]
  have hp : f p = 0 := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp [f]
    · simp [f, Nat.cast_ne_zero.mpr hp]
  change (∑ n ∈ Finset.Icc 1 ⌊(p : ℝ)⌋₊, f n) = _
  rw [Nat.floor_natCast, hf, Finset.sum_range_succ, hp, add_zero]
  unfold D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum
  apply Finset.sum_congr rfl
  intro n _
  dsimp only [f]
  ring

end D5.S3.CharacterSums.DirichletTrianglePerron

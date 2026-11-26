/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coercivity of the two-insertion spectral sum on the full four-mark average. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.HingeMoments
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

namespace RefinedBMV.Tracial

open intervalIntegral

noncomputable section

private theorem fourMarkPeriodicMean_reverse (s x y : ℝ) :
    fourMarkPeriodicMean (1 - s) y x = fourMarkPeriodicMean s x y := by
  unfold fourMarkPeriodicMean
  split_ifs <;> try linarith
  all_goals
    first
    | have ha : s = 1 / 4 := by linarith
      rw [ha]
    | have ha : s = 1 / 2 := by linarith
      rw [ha]
    | have ha : s = 3 / 4 := by linarith
      rw [ha]
  all_goals ring

/-- The signed arc-count difference integrated against the two drift eigenvalues. -/
private def fourMarkSpectralDefect (h k x y : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, Real.exp ((1 - s) * h + s * k) *
    (((1 - s) * x + s * y) ^ 4 - fourMarkPeriodicMean s x y)

private theorem fourMarkSpectralDefect_reverse (h k x y : ℝ) :
    fourMarkSpectralDefect h k x y = fourMarkSpectralDefect k h y x := by
  unfold fourMarkSpectralDefect
  let f : ℝ → ℝ := fun s ↦ Real.exp ((1 - s) * k + s * h) *
    (((1 - s) * y + s * x) ^ 4 - fourMarkPeriodicMean s y x)
  have hf : (∫ s in (0 : ℝ)..1, f (1 - s)) = ∫ s in (0 : ℝ)..1, f s := by
    simp [integral_comp_sub_left f 1]
  rw [← hf]
  apply integral_congr
  intro s _
  dsimp only [f]
  rw [fourMarkPeriodicMean_reverse]
  congr 2 <;> ring

private theorem fourMarkSpectralDefect_lower {R h k : ℝ} (hh : -R ≤ h) (hk : -R ≤ k)
    (x y : ℝ) :
    Real.exp (-R) * ((x - y) ^ 2 * ((x ^ 2 + y ^ 2) / 40)) ≤
      fourMarkSpectralDefect h k x y := by
  have step {a b : ℝ} (ha : -R ≤ a) (hab : a ≤ b) (u v : ℝ) :
      Real.exp (-R) * ((u - v) ^ 2 * ((u ^ 2 + v ^ 2) / 40)) ≤
        fourMarkSpectralDefect a b u v := by
    have hgap : 0 ≤ b - a := sub_nonneg.mpr hab
    calc
      _ ≤ Real.exp a * ((u - v) ^ 2 * ((u ^ 2 + v ^ 2) / 40)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (by positivity)
      _ ≤ Real.exp a * (∫ s in (0 : ℝ)..1, Real.exp ((b - a) * s) *
            (((1 - s) * u + s * v) ^ 4 - fourMarkPeriodicMean s u v)) :=
        mul_le_mul_of_nonneg_left (integral_fourMarkSignedDefect_lower hgap u v)
          (Real.exp_pos a).le
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr
        intro s _
        dsimp only
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  rcases le_total h k with hhk | hkh
  · exact step hh hhk x y
  · rw [fourMarkSpectralDefect_reverse]
    convert step hk hkh y x using 1
    ring


/-- A trace with two insertions and a fixed arc count only uses closed
two-step spectral paths. The nonnegative path weight is the squared
modulus of the inserted Hermitian matrix entry. -/
private theorem trace_fourMarkArc_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (s : ℝ) (k : ℕ) :
    let B := Matrix.diagonal fun i ↦ (b i : ℂ)
    let E₀ := Matrix.diagonal fun i ↦ (Real.exp ((1 - s) * h i) : ℂ)
    let E₁ := Matrix.diagonal fun i ↦ (Real.exp (s * h i) : ℂ)
    (Matrix.trace ((E₀ * B ^ (4 - k) * X) * (E₁ * B ^ k * X))).re =
      ∑ i, ∑ j, Real.exp ((1 - s) * h i + s * h j) *
        (b i ^ (4 - k) * b j ^ k) * ‖X i j‖ ^ 2 := by
  dsimp only
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hc : X j i = (starRingEnd ℂ) (X i j) := by
    have he := congrFun (congrFun hX.eq j) i
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using he.symm
  simp only [Matrix.diagonal_mul, Pi.pow_apply]
  rw [hc]
  have hprod :
      ((Real.exp ((1 - s) * h i) : ℂ) * (b i : ℂ) ^ (4 - k) * X i j) *
        ((Real.exp (s * h j) : ℂ) * (b j : ℂ) ^ k * (starRingEnd ℂ) (X i j)) =
      ((Real.exp ((1 - s) * h i) * Real.exp (s * h j) *
        (b i ^ (4 - k) * b j ^ k) : ℝ) : ℂ) * (X i j * (starRingEnd ℂ) (X i j)) := by
    push_cast
    ring
  rw [hprod, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re,
    ← Real.exp_add]

open scoped Matrix Matrix.Norms.Frobenius in
/-- In a common eigenbasis of the drift and the signed second factor, the
spectral two-insertion sum controls the Frobenius energy of the commutator. -/
private theorem fourMarkSpectralHessian_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {R : ℝ}
    (hR : ∀ i, -R ≤ h i) :
    let B : Matrix ι ι ℂ := Matrix.diagonal fun i ↦ (b i : ℂ)
    (Real.exp (-R) / 40) * ‖B * (X * B - B * X)‖ ^ 2 ≤
      (∑ i, ∑ j, ‖X i j‖ ^ 2 * fourMarkSpectralDefect (h i) (h j) (b i) (b j)) / 2 := by
  classical
  dsimp only
  let w : ι → ι → ℝ := fun i j ↦ ‖X i j‖ ^ 2 * (b i - b j) ^ 2
  have hw (i j : ι) : w i j = w j i := by
    have hx := congrFun (congrFun hX.eq i) j
    have hn : ‖X i j‖ = ‖X j i‖ := by
      simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.norm_conj] using
        congrArg (fun z : ℂ ↦ ‖z‖) hx.symm
    dsimp only [w]
    rw [hn, ← neg_sub, neg_sq]
  have hsym : (∑ i, ∑ j, w i j * b j ^ 2) = ∑ i, ∑ j, w i j * b i ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [hw]
  have henergy :
      ‖Matrix.diagonal (fun i ↦ (b i : ℂ)) *
        (X * Matrix.diagonal (fun i ↦ (b i : ℂ)) -
          Matrix.diagonal (fun i ↦ (b i : ℂ)) * X)‖ ^ 2 =
        ∑ i, ∑ j, w i j * b i ^ 2 := by
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Matrix.diagonal_mul, Matrix.sub_apply, Matrix.mul_diagonal]
    have hentry :
        (b i : ℂ) * (X i j * (b j : ℂ) - (b i : ℂ) * X i j) =
          ((b i : ℂ) * ((b j - b i : ℝ) : ℂ)) * X i j := by
      push_cast
      ring
    rw [hentry]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, w]
    ring
  have hcomp :
      (∑ i, ∑ j, ‖X i j‖ ^ 2 *
        (Real.exp (-R) * ((b i - b j) ^ 2 * ((b i ^ 2 + b j ^ 2) / 40)))) ≤
      ∑ i, ∑ j, ‖X i j‖ ^ 2 * fourMarkSpectralDefect (h i) (h j) (b i) (b j) :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (fourMarkSpectralDefect_lower (hR i) (hR j) (b i) (b j))
        (sq_nonneg _)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [henergy]
  apply le_trans _ hcomp
  have hfac (i j : ι) :
      ‖X i j‖ ^ 2 *
          (Real.exp (-R) * ((b i - b j) ^ 2 * ((b i ^ 2 + b j ^ 2) / 40))) =
        (Real.exp (-R) / 40) * (w i j * b i ^ 2 + w i j * b j ^ 2) := by
    dsimp only [w]
    ring
  simp_rw [hfac, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsym]
  ring_nf
  exact le_rfl


private def binomialArcAverage (s : ℝ) (f : ℕ → ℝ) : ℝ :=
  (1 - s) ^ 4 * f 0 + 4 * s * (1 - s) ^ 3 * f 1 + 6 * s ^ 2 * (1 - s) ^ 2 * f 2 +
    4 * s ^ 3 * (1 - s) * f 3 + s ^ 4 * f 4

private def periodicArcAverage (s : ℝ) (f : ℕ → ℝ) : ℝ :=
  if s ≤ 1 / 4 then (1 - 4 * s) * f 0 + (4 * s) * f 1
  else if s ≤ 1 / 2 then (2 - 4 * s) * f 1 + (4 * s - 1) * f 2
  else if s ≤ 3 / 4 then (3 - 4 * s) * f 2 + (4 * s - 2) * f 3
  else (4 - 4 * s) * f 3 + (4 * s - 3) * f 4

/-- Two-insertion trace difference for an independent arc mass and a
periodic arc count associated with the actual arc length. -/
def fourMarkTraceInsertionDefectAtMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (s mass : ℝ) : ℝ :=
  let B := Matrix.diagonal fun i ↦ (b i : ℂ)
  let E₀ := Matrix.diagonal fun i ↦ (Real.exp ((1 - s) * h i) : ℂ)
  let E₁ := Matrix.diagonal fun i ↦ (Real.exp (s * h i) : ℂ)
  let traceCount := fun k : ℕ ↦
    (Matrix.trace ((E₀ * B ^ (4 - k) * X) * (E₁ * B ^ k * X))).re
  binomialArcAverage mass traceCount - periodicArcAverage s traceCount

/-- The difference for four independent uniform marks and four periodically
spaced marks. -/
def fourMarkTraceInsertionDefect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (s : ℝ) : ℝ :=
  fourMarkTraceInsertionDefectAtMass h b X s s

private lemma fourMarkTraceInsertionDefectAtMass_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (s mass : ℝ) :
    fourMarkTraceInsertionDefectAtMass h b X s mass =
      ∑ i, ∑ j, ‖X i j‖ ^ 2 * (Real.exp ((1 - s) * h i + s * h j) *
        (((1 - mass) * b i + mass * b j) ^ 4 - fourMarkPeriodicMean s (b i) (b j))) := by
  dsimp only [fourMarkTraceInsertionDefectAtMass, binomialArcAverage, periodicArcAverage,
    fourMarkPeriodicMean]
  simp_rw [trace_fourMarkArc_spectral h b X hX s]
  split_ifs
  all_goals
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    norm_num
    ring

open scoped Matrix Matrix.Norms.Frobenius in
/-- The integrated two-insertion comparison controls the squared
Frobenius norm of the weighted commutator, also for signed B. -/
theorem fourMarkTraceHessian_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian) {R : ℝ}
    (hR : ∀ i, -R ≤ h i) :
    let B : Matrix ι ι ℂ := Matrix.diagonal fun i ↦ (b i : ℂ)
    (Real.exp (-R) / 40) * ‖B * (X * B - B * X)‖ ^ 2 ≤
      (∫ s in (0 : ℝ)..1, fourMarkTraceInsertionDefect h b X s) / 2 := by
  dsimp only
  refine (fourMarkSpectralHessian_lower h b X hX hR).trans ?_
  apply le_of_eq
  congr 1
  simp_rw [fourMarkTraceInsertionDefect, fourMarkTraceInsertionDefectAtMass_spectral h b X hX]
  let f : ι → ι → ℝ → ℝ := fun i j s ↦ ‖X i j‖ ^ 2 *
    (Real.exp ((1 - s) * h i + s * h j) *
      (((1 - s) * b i + s * b j) ^ 4 - fourMarkPeriodicMean s (b i) (b j)))
  change (∑ i, ∑ j, ‖X i j‖ ^ 2 * fourMarkSpectralDefect (h i) (h j) (b i) (b j)) =
    ∫ s in (0 : ℝ)..1, ∑ i, ∑ j, f i j s
  have hf (i j : ι) : Continuous (f i j) := by
    unfold f
    have hc := continuous_fourMarkPeriodicMean (b i) (b j)
    fun_prop
  have hi (i : ι) : Continuous (fun s ↦ ∑ j, f i j s) :=
    continuous_finsetSum _ fun j _ ↦ hf i j
  rw [integral_finsetSum (fun i _ ↦ (hi i).intervalIntegrable 0 1)]
  simp_rw [integral_finsetSum (fun j _ ↦ (hf _ j).intervalIntegrable 0 1)]
  simp only [f, fourMarkSpectralDefect, integral_const_mul]



open MeasureTheory in
private lemma affine_fourth_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {mass : Ω → ℝ} (hm : AEMeasurable mass μ)
    (h01 : ∀ᵐ ω ∂μ, mass ω ∈ Set.Icc (0 : ℝ) 1) (x y : ℝ) :
    Integrable (fun ω ↦ ((1 - mass ω) * x + mass ω * y) ^ 4) μ := by
  have hmeas : AEMeasurable (fun ω ↦ ((1 - mass ω) * x + mass ω * y) ^ 4) μ := by
    fun_prop
  apply (integrable_const ((‖x‖ + ‖y‖) ^ 4)).mono' hmeas.aestronglyMeasurable
  filter_upwards [h01] with ω hω
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 4
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Real.norm_of_nonneg hω.1,
    Real.norm_of_nonneg (sub_nonneg.mpr hω.2)]
  exact add_le_add
    (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hω.1]))
    (mul_le_of_le_one_left (norm_nonneg _) hω.2)

open MeasureTheory in
private lemma affine_fourth_jensen {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {mass : Ω → ℝ} (hm : Integrable mass μ)
    (h01 : ∀ᵐ ω ∂μ, mass ω ∈ Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hmean : (∫ ω, mass ω ∂μ) = s) (x y : ℝ) :
    ((1 - s) * x + s * y) ^ 4 ≤ ∫ ω, ((1 - mass ω) * x + mass ω * y) ^ 4 ∂μ := by
  let g : Ω → ℝ := fun ω ↦ (1 - mass ω) * x + mass ω * y
  have hg : Integrable g μ := ((integrable_const 1).sub hm).mul_const x |>.add (hm.mul_const y)
  have he : (∫ ω, g ω ∂μ) = (1 - s) * x + s * y := by
    change (∫ ω, (1 - mass ω) * x + mass ω * y ∂μ) = _
    have h₁ : Integrable (fun ω ↦ (1 - mass ω) * x) μ :=
      ((integrable_const 1).sub hm).mul_const x
    rw [MeasureTheory.integral_add h₁ (hm.mul_const y),
      MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
    have hs : (∫ ω, 1 - mass ω ∂μ) = (∫ _ : Ω, (1 : ℝ) ∂μ) - ∫ ω, mass ω ∂μ :=
      MeasureTheory.integral_sub (integrable_const 1) hm
    rw [hs, hmean]
    simp
  have hv : ConvexOn ℝ Set.univ (fun t : ℝ ↦ t ^ 4) :=
    (show Even (4 : ℕ) by decide).convexOn_pow
  have hcv : Continuous (fun t : ℝ ↦ t ^ 4) := by fun_prop
  have hj := hv.map_integral_le hcv.continuousOn isClosed_univ
    (.of_forall fun _ ↦ Set.mem_univ _) hg (affine_fourth_integrable hm.aemeasurable h01 x y)
  rwa [he] at hj

open MeasureTheory in
/-- Randomizing the arc mass with its mean fixed preserves the two-insertion
lower bound pointwise. This applies to the conditional binomial law
from a randomly rotated lattice of B marks. -/
theorem fourMarkTraceInsertionDefect_le_expected {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h b : ι → ℝ) (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    {mass : Ω → ℝ} (hm : Integrable mass μ)
    (h01 : ∀ᵐ ω ∂μ, mass ω ∈ Set.Icc (0 : ℝ) 1) {s : ℝ}
    (hmean : (∫ ω, mass ω ∂μ) = s) :
    fourMarkTraceInsertionDefect h b X s ≤
      ∫ ω, fourMarkTraceInsertionDefectAtMass h b X s (mass ω) ∂μ := by
  simp_rw [fourMarkTraceInsertionDefect, fourMarkTraceInsertionDefectAtMass_spectral h b X hX]
  let w : ι → ι → ℝ := fun i j ↦ ‖X i j‖ ^ 2 * Real.exp ((1 - s) * h i + s * h j)
  let f : ι → ι → ℝ → ℝ := fun i j t ↦
    ((1 - t) * b i + t * b j) ^ 4 - fourMarkPeriodicMean s (b i) (b j)
  simp_rw [← mul_assoc]
  change (∑ i, ∑ j, w i j * f i j s) ≤ ∫ ω, ∑ i, ∑ j, w i j * f i j (mass ω) ∂μ
  have hf (i j : ι) : Integrable (fun ω ↦ f i j (mass ω)) μ :=
    (affine_fourth_integrable hm.aemeasurable h01 (b i) (b j)).sub (integrable_const _)
  have hweighted (i j : ι) : Integrable (fun ω ↦ w i j * f i j (mass ω)) μ :=
    (hf i j).const_mul _
  rw [MeasureTheory.integral_finsetSum _ (fun i _ ↦
    integrable_finsetSum _ (fun j _ ↦ hweighted i j))]
  simp_rw [MeasureTheory.integral_finsetSum _ (fun j _ ↦ hweighted _ j)]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [MeasureTheory.integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by unfold w; positivity)
  unfold f
  rw [MeasureTheory.integral_sub
    (affine_fourth_integrable hm.aemeasurable h01 (b i) (b j)) (integrable_const _)]
  simpa using sub_le_sub_right (affine_fourth_jensen hm h01 hmean (b i) (b j))
    (fourMarkPeriodicMean s (b i) (b j))


end

end RefinedBMV.Tracial

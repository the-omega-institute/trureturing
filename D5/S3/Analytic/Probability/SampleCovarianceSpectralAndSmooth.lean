/- GID: D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Spectral logarithmic energies and smooth entry laws. -/
/-
proof_shape: pending per-declaration verification.
escape_witness: none claimed before the upstream-only tests.
admission_basis: pending escape-witness verification
Direct frozen dependencies: pending compiled-constant extraction.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Matrix.Hermitian
import D5.S3.Quantum.Schatten.SingularValueOrder
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Measure.Prod
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth

open MeasureTheory Filter
open scoped BigOperators ENNReal Matrix

noncomputable def gram (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := A * Aᴴ

theorem gramHermitian (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (gram n A).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self A

noncomputable def gramEigenvalue (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : ℝ := (gramHermitian n A).eigenvalues i

noncomputable def empiricalSpectralMeasure (n : ℕ) (_hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (gramEigenvalue n A i / n)

def EntryLaw (μ : Measure ℂ) : Prop :=
  μ Set.univ = 1 ∧
    Integrable (fun z : ℂ => z) μ ∧
    Integrable (fun z : ℂ => ‖z‖ ^ 2) μ ∧
    (∫ z : ℂ, z ∂μ) = 0 ∧
    (∫ z : ℂ, ‖z‖ ^ 2 ∂μ) = 1

noncomputable def matrixLaw (n : ℕ) (μ : Measure ℂ) :
    Measure (Matrix (Fin n) (Fin n) ℂ) :=
  Measure.map (fun f : Fin n × Fin n → ℂ => fun i j => f (i, j))
    (Measure.pi (fun _ : Fin n × Fin n => μ))

noncomputable def meanSpectralMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) : Measure ℝ :=
  (matrixLaw n μ).bind (fun A => empiricalSpectralMeasure n hn A)

noncomputable def logPositiveKernel (x y : ℝ) : ℝ≥0∞ :=
  if x = y then ∞ else ENNReal.ofReal (max (Real.log (1 / |x - y|)) 0)

noncomputable def logNegativeKernel (x y : ℝ) : ℝ≥0∞ :=
  if x = y then 0 else ENNReal.ofReal (max (-Real.log (1 / |x - y|)) 0)

noncomputable def logarithmicEnergy (μ : Measure ℝ) : EReal :=
  (∫⁻ x, ∫⁻ y, logPositiveKernel x y ∂μ ∂μ : EReal) -
    (∫⁻ x, ∫⁻ y, logNegativeKernel x y ∂μ ∂μ : EReal)

noncomputable def firstMoment (μ : Measure ℝ) : EReal :=
  ENNReal.toEReal (∫⁻ x, ENNReal.ofReal (max x 0) ∂μ)

noncomputable def penalizedEnergy (μ : Measure ℝ) : EReal :=
  logarithmicEnergy μ + firstMoment μ

noncomputable def marchenkoPasturDensity (x : ℝ) : ℝ≥0∞ :=
  if 0 < x then
    ENNReal.ofReal (Real.sqrt (max (4 - x) 0) /
      (2 * Real.pi * Real.sqrt x))
  else 0

noncomputable def marchenkoPastur : Measure ℝ :=
  Measure.withDensity (Measure.restrict MeasureTheory.volume (Set.Ici 0))
    marchenkoPasturDensity

end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth

namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma continuous_gram (n : ℕ) :
    Continuous (gram n : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  unfold gram
  fun_prop
private lemma continuous_gramEigenvalue (n : ℕ) (i : Fin n) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => gramEigenvalue n A i) := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hT : Continuous T :=
    (T.toAlgEquiv.toLinearEquiv.toLinearMap.restrictScalars ℝ).continuous_of_finiteDimensional
  rw [continuous_iff_continuousAt]
  intro A
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ B : Matrix (Fin n) (Fin n) ℂ,
      dist (gramEigenvalue n B i) (gramEigenvalue n A i) ≤
        ‖T (gram n B - gram n A)‖ := by
    intro B
    simpa only [gramEigenvalue, Matrix.IsHermitian.eigenvalues, Real.dist_eq] using
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.abs_eigenvalues0_sub_le_norm
        (gramHermitian n B) (gramHermitian n A)
        ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm i)
  have ht : Tendsto (fun B : Matrix (Fin n) (Fin n) ℂ =>
      ‖T (gram n B - gram n A)‖) (𝓝 A) (𝓝 0) := by
    have hc : Continuous (fun B : Matrix (Fin n) (Fin n) ℂ =>
        T (gram n B - gram n A)) := hT.comp ((continuous_gram n).sub continuous_const)
    simpa only [sub_self, map_zero, norm_zero] using hc.norm.tendsto A
  exact squeeze_zero (fun _ => dist_nonneg) hb ht
lemma measurable_gramEigenvalue (n : ℕ) (i : Fin n) :
    Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => gramEigenvalue n A i) :=
  (continuous_gramEigenvalue n i).measurable
attribute [fun_prop] continuous_gramEigenvalue measurable_gramEigenvalue
private lemma measurable_empiricalSpectralMeasure (n : ℕ) (hn : 0 < n) :
    Measurable (empiricalSpectralMeasure n hn) := by
  have hsum : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      ∑ i : Fin n, Measure.dirac (gramEigenvalue n A i / n)) := by
    exact Finset.measurable_fun_sum _ (fun i _ =>
      Measure.measurable_dirac.comp ((measurable_gramEigenvalue n i).div_const _))
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun A => empiricalSpectralMeasure n hn A s)
  simp only [empiricalSpectralMeasure, Measure.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((Measure.measurable_coe hs).comp hsum)
private lemma empiricalSpectralMeasure_univ (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    empiricalSpectralMeasure n hn A Set.univ = 1 := by
  simp only [empiricalSpectralMeasure, Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)
private lemma lintegral_empiricalSpectralMeasure (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂empiricalSpectralMeasure n hn A) =
      (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, f (gramEigenvalue n A i / n) := by
  simp only [empiricalSpectralMeasure, lintegral_smul_measure,
    lintegral_finsetSum_measure, lintegral_dirac' _ hf, smul_eq_mul]
lemma lintegral_meanSpectralMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂meanSpectralMeasure n hn μ) =
      (n : ℝ≥0∞)⁻¹ * ∫⁻ A, ∑ i : Fin n, f (gramEigenvalue n A i / n) ∂matrixLaw n μ := by
  rw [meanSpectralMeasure, Measure.lintegral_bind
    (measurable_empiricalSpectralMeasure n hn).aemeasurable hf.aemeasurable]
  simp_rw [lintegral_empiricalSpectralMeasure n hn _ f hf]
  exact lintegral_const_mul' _ _ (by simp [hn.ne'])
private lemma two_copy_det_hermitian {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} {C : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    Matrix.det (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ C) =
      ∏ i : Fin n, ∏ j : Fin m, ((hA.eigenvalues i : ℂ) - (hC.eigenvalues j : ℂ)) := by
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  let V : Matrix (Fin m) (Fin m) ℂ := hC.eigenvectorUnitary
  let W := U ⊗ₖ V
  have hU : Uᴴ * U = 1 := by
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hV : Vᴴ * V = 1 := by
    exact Unitary.coe_star_mul_self hC.eigenvectorUnitary
  have hW : Wᴴ * W = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp
      (Matrix.kronecker_mem_unitary hA.eigenvectorUnitary.property hC.eigenvectorUnitary.property)
  have hdA : Uᴴ * A * U = diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    simpa only [U, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hdC : Vᴴ * C * V = diagonal (fun j => (hC.eigenvalues j : ℂ)) := by
    simpa only [V, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hC.conjStarAlgAut_star_eigenvectorUnitary
  have hd : Wᴴ * (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ C) * W =
      diagonal (fun ij : Fin n × Fin m =>
        ((hA.eigenvalues ij.1 : ℂ) - (hC.eigenvalues ij.2 : ℂ))) := by
    dsimp [W]
    rw [conjTranspose_kronecker, Matrix.mul_sub, Matrix.sub_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.mul_one, Matrix.one_mul, hU, hV, hdA, hdC]
    simp only [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
      mul_one, one_mul, ← Matrix.diagonal_sub]
  have hwdet : Matrix.det Wᴴ * Matrix.det W = 1 := by
    rw [← Matrix.det_mul, hW, Matrix.det_one]
  have hh := congrArg Matrix.det hd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hh
  have cancel (d : ℂ) : Matrix.det Wᴴ * d * Matrix.det W = d := by
    calc
      Matrix.det Wᴴ * d * Matrix.det W = (Matrix.det Wᴴ * Matrix.det W) * d := by ring
      _ = d := by rw [hwdet, one_mul]
  rw [cancel] at hh
  simpa only [Fintype.prod_prod_type] using hh
private lemma two_copy_gram_det (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.det (gram n A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n C) =
      ∏ i : Fin n, ∏ j : Fin n,
        ((gramEigenvalue n A i : ℂ) - (gramEigenvalue n C j : ℂ)) :=
  two_copy_det_hermitian (gramHermitian n A) (gramHermitian n C)
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
instance matrixLaw_isProbabilityMeasure (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (matrixLaw n μ) := by
  unfold matrixLaw
  infer_instance
instance empiricalSpectralMeasure_isProbabilityMeasure (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    IsProbabilityMeasure (empiricalSpectralMeasure n hn A) :=
  ⟨empiricalSpectralMeasure_univ n hn A⟩
instance meanSpectralMeasure_isProbabilityMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (meanSpectralMeasure n hn μ) := by
  constructor
  rw [meanSpectralMeasure, Measure.bind_apply MeasurableSet.univ
    (measurable_empiricalSpectralMeasure n hn).aemeasurable]
  simp_rw [empiricalSpectralMeasure_univ]
  simp

private lemma measurable_logPositiveKernel : Measurable (fun p : ℝ × ℝ => logPositiveKernel p.1 p.2) := by
  unfold logPositiveKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
  fun_prop
private lemma measurable_logNegativeKernel : Measurable (fun p : ℝ × ℝ => logNegativeKernel p.1 p.2) := by
  unfold logNegativeKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
  fun_prop
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
lemma two_copy_gram_det_nonzero_iff (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.det (gram n A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n C) ≠ 0 ↔
      ∀ i j : Fin n, gramEigenvalue n A i ≠ gramEigenvalue n C j := by
  rw [two_copy_gram_det]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const, sub_ne_zero]
  constructor
  · intro h i j he
    apply h i j
    exact congrArg Complex.ofReal he
  · intro h i j he
    apply h i j
    exact Complex.ofReal_injective he
private lemma log_two_copy_gram_det (n : ℕ) (A C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j : Fin n, gramEigenvalue n A i ≠ gramEigenvalue n C j) :
    Real.log ‖Matrix.det (gram n A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n C)‖ =
      ∑ i : Fin n, ∑ j : Fin n, Real.log |gramEigenvalue n A i - gramEigenvalue n C j| := by
  rw [two_copy_gram_det]
  simp_rw [norm_prod]
  rw [Real.log_prod (fun i hi => Finset.prod_ne_zero_iff.mpr (fun j hj =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => h i j (Complex.ofReal_injective he)))))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_prod (fun j hj =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun he => h i j (Complex.ofReal_injective he))))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma logarithmicEnergy_eq_real_integral (ν : Measure ℝ) [SFinite ν]
    (hnocoll : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, p.1 ≠ p.2)
    (hi : Integrable (fun p : ℝ × ℝ => Real.log |p.1-p.2|) (ν.prod ν)) :
    logarithmicEnergy ν = (-(∫ p : ℝ × ℝ, Real.log |p.1-p.2| ∂ν.prod ν) : ℝ) := by
  let f : ℝ × ℝ → ℝ := fun p => -Real.log |p.1-p.2|
  have hfi : Integrable f (ν.prod ν) := hi.neg
  have hpi : Integrable (fun p => max (f p) 0) (ν.prod ν) :=
    hfi.sup (integrable_zero (ℝ × ℝ) ℝ (ν.prod ν))
  have hni : Integrable (fun p => max (-f p) 0) (ν.prod ν) :=
    hfi.neg.sup (integrable_zero (ℝ × ℝ) ℝ (ν.prod ν))
  have hp : (fun p : ℝ × ℝ => logPositiveKernel p.1 p.2) =ᵐ[ν.prod ν]
      (fun p => ENNReal.ofReal (max (f p) 0)) := by
    filter_upwards [hnocoll] with p hp
    simp only [logPositiveKernel, hp, ↓reduceIte, one_div, Real.log_inv, f]
  have hn : (fun p : ℝ × ℝ => logNegativeKernel p.1 p.2) =ᵐ[ν.prod ν]
      (fun p => ENNReal.ofReal (max (-f p) 0)) := by
    filter_upwards [hnocoll] with p hp
    simp only [logNegativeKernel, hp, ↓reduceIte, one_div, Real.log_inv, f, neg_neg]
  have hpos : 0 ≤ ∫ p, max (f p) 0 ∂ν.prod ν :=
    integral_nonneg (fun p => le_max_right _ _)
  have hneg : 0 ≤ ∫ p, max (-f p) 0 ∂ν.prod ν :=
    integral_nonneg (fun p => le_max_right _ _)
  have hsplit : (∫ p, max (f p) 0 ∂ν.prod ν) -
      (∫ p, max (-f p) 0 ∂ν.prod ν) = ∫ p, f p ∂ν.prod ν := by
    rw [← integral_sub hpi hni]
    apply integral_congr_ae
    filter_upwards [] with p
    change max (f p) 0 - max (-f p) 0 = f p
    by_cases hf : 0 ≤ f p
    · rw [max_eq_left hf, max_eq_right (neg_nonpos.mpr hf), sub_zero]
    · rw [max_eq_right (le_of_not_ge hf), max_eq_left (neg_nonneg.mpr (le_of_not_ge hf))]
      ring
  unfold logarithmicEnergy
  rw [← lintegral_prod _ measurable_logPositiveKernel.aemeasurable,
    ← lintegral_prod _ measurable_logNegativeKernel.aemeasurable,
    lintegral_congr_ae hp, lintegral_congr_ae hn,
    ← ofReal_integral_eq_lintegral_ofReal hpi (Eventually.of_forall (fun p => le_max_right _ _)),
    ← ofReal_integral_eq_lintegral_ofReal hni (Eventually.of_forall (fun p => le_max_right _ _))]
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left hpos, max_eq_left hneg,
    ← EReal.coe_sub, hsplit]
  change (((∫ p : ℝ × ℝ, -Real.log |p.1-p.2| ∂ν.prod ν) : ℝ) : EReal) = _
  exact congrArg (fun r : ℝ => (r : EReal))
    (integral_neg (fun p : ℝ × ℝ => Real.log |p.1-p.2|))
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma meanSpectralMeasure_eq_sum_map (n : ℕ) (hn : 0 < n) (μ : Measure ℂ) :
    meanSpectralMeasure n hn μ = (n : ℝ≥0∞)⁻¹ •
      ∑ i : Fin n, Measure.map (fun A => gramEigenvalue n A i / n) (matrixLaw n μ) := by
  apply Measure.ext
  intro s hs
  rw [meanSpectralMeasure, Measure.bind_apply hs
    (measurable_empiricalSpectralMeasure n hn).aemeasurable]
  simp only [empiricalSpectralMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  rw [lintegral_const_mul' _ _ (by simp [hn.ne'])]
  have hsum : (∫⁻ A : Matrix (Fin n) (Fin n) ℂ,
      ∑ i : Fin n, Measure.dirac (gramEigenvalue n A i / n) s ∂matrixLaw n μ) =
      ∑ i : Fin n, ∫⁻ A : Matrix (Fin n) (Fin n) ℂ,
        Measure.dirac (gramEigenvalue n A i / n) s ∂matrixLaw n μ := by
    exact lintegral_finsetSum _ (fun i _ => (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp ((measurable_gramEigenvalue n i).div_const _)))
  rw [hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hLam : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => gramEigenvalue n A i / n) :=
    (measurable_gramEigenvalue n i).div_const _
  have h := congrArg (fun ν : Measure ℝ => ν s)
    (Measure.bind_dirac_eq_map (matrixLaw n μ) hLam)
  have hb : ((matrixLaw n μ).bind (fun A : Matrix (Fin n) (Fin n) ℂ =>
      Measure.dirac (gramEigenvalue n A i / n))) s =
      ∫⁻ A : Matrix (Fin n) (Fin n) ℂ, Measure.dirac (gramEigenvalue n A i / n) s
        ∂matrixLaw n μ := Measure.bind_apply hs
          (show AEMeasurable (fun A : Matrix (Fin n) (Fin n) ℂ =>
            Measure.dirac (gramEigenvalue n A i / n)) (matrixLaw n μ) from
            (Measure.measurable_dirac.comp hLam).aemeasurable)
  exact hb.symm.trans h
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma meanSpectralMeasure_prod_eq_sum_map (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] :
    (meanSpectralMeasure n hn μ).prod (meanSpectralMeasure n hn μ) =
      ((n : ℝ≥0∞)⁻¹)^2 • Measure.sum (fun ij : Fin n × Fin n =>
        Measure.map (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
          (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n))
          ((matrixLaw n μ).prod (matrixLaw n μ))) := by
  simp_rw [meanSpectralMeasure_eq_sum_map, ← Measure.sum_fintype,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.prod_sum, ← pow_two]
  congr 1
  apply congrArg Measure.sum
  funext ij
  exact Measure.map_prod_map (matrixLaw n μ) (matrixLaw n μ)
    ((measurable_gramEigenvalue n ij.1).div_const _)
    ((measurable_gramEigenvalue n ij.2).div_const _)
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma integrable_two_copy_meanSpectralMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (f : ℝ × ℝ → ℝ)
    (hf : Measurable f)
    (hi : ∀ ij : Fin n × Fin n, Integrable (fun AC : Matrix (Fin n) (Fin n) ℂ ×
        Matrix (Fin n) (Fin n) ℂ =>
      f (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n))
      ((matrixLaw n μ).prod (matrixLaw n μ))) :
    Integrable f ((meanSpectralMeasure n hn μ).prod (meanSpectralMeasure n hn μ)) := by
  rw [meanSpectralMeasure_prod_eq_sum_map, Measure.sum_fintype]
  apply Integrable.smul_measure _ (by simp [hn.ne'])
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  have hm : Measurable (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n)) := by
    fun_prop
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr (hi ij)
private lemma integral_two_copy_meanSpectralMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (f : ℝ × ℝ → ℝ)
    (hf : Measurable f)
    (hi : ∀ ij : Fin n × Fin n, Integrable (fun AC : Matrix (Fin n) (Fin n) ℂ ×
        Matrix (Fin n) (Fin n) ℂ =>
      f (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n))
      ((matrixLaw n μ).prod (matrixLaw n μ))) :
    (∫ p, f p ∂(meanSpectralMeasure n hn μ).prod (meanSpectralMeasure n hn μ)) =
      (n : ℝ)⁻¹ ^ 2 * ∑ ij : Fin n × Fin n,
        ∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          f (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n)
          ∂(matrixLaw n μ).prod (matrixLaw n μ) := by
  have hm (ij : Fin n × Fin n) : Measurable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n)) := by
    exact (((measurable_gramEigenvalue n ij.1).comp measurable_fst).div_const _).prodMk
      (((measurable_gramEigenvalue n ij.2).comp measurable_snd).div_const _)
  have him (ij : Fin n × Fin n) : Integrable f (Measure.map _
      ((matrixLaw n μ).prod (matrixLaw n μ))) :=
    (integrable_map_measure hf.aestronglyMeasurable (hm ij).aemeasurable).mpr (hi ij)
  rw [meanSpectralMeasure_prod_eq_sum_map, Measure.sum_fintype, integral_smul_measure,
    integral_finsetSum_measure (fun ij _ => him ij)]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact integral_map (hm ij).aemeasurable hf.aestronglyMeasurable
private lemma ae_noncollision_meanSpectralMeasure (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h : ∀ᵐ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
        ∂(matrixLaw n μ).prod (matrixLaw n μ),
      ∀ i j, gramEigenvalue n AC.1 i ≠ gramEigenvalue n AC.2 j) :
    ∀ᵐ p : ℝ × ℝ ∂(meanSpectralMeasure n hn μ).prod (meanSpectralMeasure n hn μ),
      p.1 ≠ p.2 := by
  rw [meanSpectralMeasure_prod_eq_sum_map]
  apply Measure.ae_smul_measure
  apply Measure.ae_sum_iff.mpr
  intro ij
  have hm : Measurable (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      (gramEigenvalue n AC.1 ij.1 / n, gramEigenvalue n AC.2 ij.2 / n)) := by
    exact (((measurable_gramEigenvalue n ij.1).comp measurable_fst).div_const _).prodMk
      (((measurable_gramEigenvalue n ij.2).comp measurable_snd).div_const _)
  exact (MeasureTheory.ae_map_iff (p := fun p : ℝ × ℝ => p.1 ≠ p.2) hm.aemeasurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
      (h.mono (fun AC hAC =>
        (div_left_inj' (by exact_mod_cast hn.ne')).not.mpr (hAC ij.1 ij.2)))
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma log_two_copy_normalized_gram_det (n : ℕ) (hn : 0 < n)
    (A C : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j : Fin n, gramEigenvalue n A i ≠ gramEigenvalue n C j) :
    Real.log ‖Matrix.det (gram n A ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
      (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n C)‖ =
      (∑ ij : Fin n × Fin n,
        Real.log |gramEigenvalue n A ij.1 / n - gramEigenvalue n C ij.2 / n|) +
        (n : ℝ)^2 * Real.log n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [log_two_copy_gram_det n A C h, ← Fintype.sum_prod_type']
  have hpair (ij : Fin n × Fin n) :
      Real.log |gramEigenvalue n A ij.1 - gramEigenvalue n C ij.2| =
        Real.log |gramEigenvalue n A ij.1 / n - gramEigenvalue n C ij.2 / n| + Real.log n := by
    rw [← sub_div, abs_div, abs_of_pos (by exact_mod_cast hn : (0:ℝ) < n),
      Real.log_div (abs_ne_zero.mpr (sub_ne_zero.mpr (h ij.1 ij.2))) hnR]
    ring
  simp_rw [hpair]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, ← pow_two, Nat.cast_pow]
private lemma logarithmicEnergy_mean_eq_log_det (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (h : ∀ᵐ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
        ∂(matrixLaw n μ).prod (matrixLaw n μ),
      ∀ i j, gramEigenvalue n AC.1 i ≠ gramEigenvalue n AC.2 j)
    (hi : ∀ ij : Fin n × Fin n, Integrable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        Real.log |gramEigenvalue n AC.1 ij.1 / n - gramEigenvalue n AC.2 ij.2 / n|)
      ((matrixLaw n μ).prod (matrixLaw n μ))) :
    logarithmicEnergy (meanSpectralMeasure n hn μ) =
      (Real.log n - (n : ℝ)⁻¹^2 *
        ∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          Real.log ‖Matrix.det (gram n AC.1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
            (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n AC.2)‖
          ∂(matrixLaw n μ).prod (matrixLaw n μ) : ℝ) := by
  have hf : Measurable (fun p : ℝ × ℝ => Real.log |p.1-p.2|) := by fun_prop
  have hint := integrable_two_copy_meanSpectralMeasure n hn μ _ hf hi
  rw [logarithmicEnergy_eq_real_integral _ (ae_noncollision_meanSpectralMeasure n hn μ h) hint,
    integral_two_copy_meanSpectralMeasure n hn μ _ hf hi]
  have hdet : (∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          Real.log ‖Matrix.det (gram n AC.1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
            (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n AC.2)‖
          ∂(matrixLaw n μ).prod (matrixLaw n μ)) =
      (∑ ij : Fin n × Fin n,
        ∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          Real.log |gramEigenvalue n AC.1 ij.1 / n - gramEigenvalue n AC.2 ij.2 / n|
          ∂(matrixLaw n μ).prod (matrixLaw n μ)) + (n : ℝ)^2 * Real.log n := by
    calc
      _ = ∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          (∑ ij : Fin n × Fin n,
            Real.log |gramEigenvalue n AC.1 ij.1 / n - gramEigenvalue n AC.2 ij.2 / n|) +
              (n : ℝ)^2 * Real.log n ∂(matrixLaw n μ).prod (matrixLaw n μ) := by
        apply integral_congr_ae
        filter_upwards [h] with AC hAC
        exact log_two_copy_normalized_gram_det n hn AC.1 AC.2 hAC
      _ = _ := by
        rw [integral_add (integrable_finsetSum _ (fun ij _ => hi ij)) (integrable_const _),
          integral_finsetSum _ (fun ij _ => hi ij), integral_const]
        simp only [probReal_univ, one_smul]
  rw [hdet]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]
  ring
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.FiniteLog
open MeasureTheory
open scoped BigOperators
private lemma integrable_components_of_sum_and_positive {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : ι → Ω → ℝ)
    (hm : ∀ i, AEStronglyMeasurable (f i) ν)
    (hs : Integrable (fun x => ∑ i, f i x) ν)
    (hp : ∀ i, Integrable (fun x => max (f i x) 0) ν) :
    ∀ i, Integrable (f i) ν := by
  classical
  have hpSum : Integrable (fun x => ∑ i, max (f i x) 0) ν :=
    integrable_finsetSum _ (fun i _ => hp i)
  intro i
  apply ((hpSum.const_mul 2).sub hs).mono' (hm i)
  filter_upwards [] with x
  have hb : max (f i x) 0 - f i x ≤ ∑ j, (max (f j x) 0 - f j x) :=
    Finset.single_le_sum (f := fun j => max (f j x) 0 - f j x)
      (fun j _ => sub_nonneg.mpr (le_max_left _ _)) (Finset.mem_univ i)
  have hpi : max (f i x) 0 ≤ ∑ j, max (f j x) 0 :=
    Finset.single_le_sum (f := fun j => max (f j x) 0)
      (fun j _ => le_max_right _ _) (Finset.mem_univ i)
  rw [Finset.sum_sub_distrib] at hb
  change ‖f i x‖ ≤ 2*(∑ j, max (f j x) 0) - ∑ j, f j x
  rw [Real.norm_eq_abs]
  by_cases hfi : 0 ≤ f i x
  · rw [abs_of_nonneg hfi, max_eq_left hfi] at *
    linarith
  · have hfi' : f i x ≤ 0 := le_of_not_ge hfi
    rw [abs_of_nonpos hfi', max_eq_right hfi'] at *
    linarith
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.FiniteLog
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma gramEigenvalue_nonneg (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    0 ≤ gramEigenvalue n A i :=
  Matrix.eigenvalues_self_mul_conjTranspose_nonneg A i
private lemma pos_log_gap_le_sum {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max (Real.log |x-y|) 0 ≤ x+y := by
  apply max_le
  · have hb : |x-y| ≤ x+y := (abs_le.mpr ⟨by linarith, by linarith⟩)
    exact (Real.log_le_self (abs_nonneg _)).trans hb
  · linarith
private lemma pairwise_log_integrable_of_log_det (n : ℕ) (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (he : ∀ i : Fin n, Integrable (fun A => gramEigenvalue n A i) (matrixLaw n μ))
    (h : ∀ᵐ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
        ∂(matrixLaw n μ).prod (matrixLaw n μ),
      ∀ i j, gramEigenvalue n AC.1 i ≠ gramEigenvalue n AC.2 j)
    (hd : Integrable (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      Real.log ‖Matrix.det (gram n AC.1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
        (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n AC.2)‖)
      ((matrixLaw n μ).prod (matrixLaw n μ))) :
    ∀ ij : Fin n × Fin n, Integrable
      (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
        Real.log |gramEigenvalue n AC.1 ij.1 - gramEigenvalue n AC.2 ij.2|)
      ((matrixLaw n μ).prod (matrixLaw n μ)) := by
  apply D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.FiniteLog.integrable_components_of_sum_and_positive
  · intro ij
    apply Measurable.aestronglyMeasurable
    fun_prop
  · apply hd.congr
    filter_upwards [h] with AC hAC
    rw [log_two_copy_gram_det n AC.1 AC.2 hAC, Fintype.sum_prod_type]
  · intro ij
    apply ((he ij.1).comp_fst _ |>.add ((he ij.2).comp_snd _)).mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [] with AC
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact pos_log_gap_le_sum (gramEigenvalue_nonneg _ _ _) (gramEigenvalue_nonneg _ _ _)
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
open MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology Kronecker
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma logarithmicEnergy_mean_eq_log_det_of_moments (n : ℕ) (hn : 0 < n)
    (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (he : ∀ i : Fin n, Integrable (fun A => gramEigenvalue n A i) (matrixLaw n μ))
    (h : ∀ᵐ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
        ∂(matrixLaw n μ).prod (matrixLaw n μ),
      ∀ i j, gramEigenvalue n AC.1 i ≠ gramEigenvalue n AC.2 j)
    (hd : Integrable (fun AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ =>
      Real.log ‖Matrix.det (gram n AC.1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
        (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n AC.2)‖)
      ((matrixLaw n μ).prod (matrixLaw n μ))) :
    logarithmicEnergy (meanSpectralMeasure n hn μ) =
      (Real.log n - (n : ℝ)⁻¹^2 *
        ∫ AC : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
          Real.log ‖Matrix.det (gram n AC.1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) -
            (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ gram n AC.2)‖
          ∂(matrixLaw n μ).prod (matrixLaw n μ) : ℝ) := by
  have hr := pairwise_log_integrable_of_log_det n μ he h hd
  apply logarithmicEnergy_mean_eq_log_det n hn μ h
  intro ij
  apply ((hr ij).sub (integrable_const (Real.log n))).congr
  filter_upwards [h] with AC hAC
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← sub_div, abs_div, abs_of_pos (by exact_mod_cast hn : (0:ℝ) < n),
    Real.log_div (abs_ne_zero.mpr (sub_ne_zero.mpr (hAC ij.1 ij.2))) hnR]
  rfl
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix Polynomial
open scoped BigOperators Kronecker

namespace D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def complexGaussian (m : ℝ) (v : ℝ≥0) : Measure ℂ :=
  Measure.map (fun xy : ℝ × ℝ => (xy.1 : ℂ) + (xy.2 : ℂ) * Complex.I)
    ((gaussianReal m v).prod (gaussianReal 0 v))
instance complexGaussian_probability (m : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (complexGaussian m v) := by unfold complexGaussian; infer_instance
private lemma gaussian_square_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^2) (gaussianReal m v) := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_id_gaussianReal 2)
private lemma gaussian_square_integral (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal m v) = m^2 + v := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := m) (v := v) 2)
  simp only [variance_id_gaussianReal, integral_id_gaussianReal, id_eq, Pi.pow_apply] at h
  linarith
private lemma complex_coordinates_norm (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ)*Complex.I‖^2 = x^2+y^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring
private lemma complexGaussian_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℂ => z) (complexGaussian m v) := by
  have hx : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hy : Integrable (fun y : ℝ => y) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  exact (hx.comp_fst (gaussianReal 0 v)).ofReal.add
    ((hy.comp_snd (gaussianReal m v)).ofReal.mul_const Complex.I)
private lemma complexGaussian_integral (m : ℝ) (v : ℝ≥0) :
    (∫ z : ℂ, z ∂complexGaussian m v) = (m : ℂ) := by
  unfold complexGaussian
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_add]
  · have hfst : (∫ a : ℝ × ℝ, (a.1 : ℂ) ∂(gaussianReal m v).prod (gaussianReal 0 v)) = (m : ℂ) := by
      rw [integral_fun_fst]
      have hm : (∫ x : ℝ, (x : ℂ) ∂gaussianReal m v) = (m : ℂ) := by
        rw [integral_complex_ofReal, integral_id_gaussianReal]
      simpa [hm]
    have hsnd : (∫ a : ℝ × ℝ, (a.2 : ℂ) * Complex.I ∂(gaussianReal m v).prod (gaussianReal 0 v)) = 0 := by
      rw [integral_mul_const Complex.I, integral_fun_snd]
      have hz : (∫ y : ℝ, (y : ℂ) ∂gaussianReal 0 v) = 0 := by
        rw [integral_complex_ofReal, integral_id_gaussianReal]
        norm_num
      simpa [hz]
    rw [hfst, hsnd, add_zero]
  · exact ((memLp_id_gaussianReal 1).integrable (by norm_num)).comp_fst (gaussianReal 0 v) |>.ofReal
  · exact (((memLp_id_gaussianReal 1).integrable (by norm_num)).comp_snd (gaussianReal m v)).ofReal.mul_const Complex.I
private lemma complexGaussian_second_integrable (m : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℂ => ‖z‖^2) (complexGaussian m v) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  change Integrable (fun xy : ℝ × ℝ => ‖(xy.1 : ℂ) + (xy.2 : ℂ) * Complex.I‖^2)
    ((gaussianReal m v).prod (gaussianReal 0 v))
  simp_rw [complex_coordinates_norm]
  exact ((gaussian_square_integrable m v).comp_fst (gaussianReal 0 v)).add
    ((gaussian_square_integrable 0 v).comp_snd (gaussianReal m v))
private lemma complexGaussian_second_integral (m : ℝ) (v : ℝ≥0) :
    (∫ z : ℂ, ‖z‖^2 ∂complexGaussian m v) = m^2+2*v := by
  unfold complexGaussian
  rw [integral_map (by fun_prop) (by fun_prop)]
  change (∫ xy : ℝ × ℝ, ‖(xy.1 : ℂ) + (xy.2 : ℂ) * Complex.I‖^2 ∂((gaussianReal m v).prod (gaussianReal 0 v))) = m^2+2*v
  simp_rw [complex_coordinates_norm]
  rw [integral_add]
  · have hfst : (∫ a : ℝ × ℝ, a.1^2 ∂((gaussianReal m v).prod (gaussianReal 0 v))) =
        (gaussianReal 0 v).real Set.univ • (∫ x : ℝ, x^2 ∂gaussianReal m v) := by
      exact integral_fun_fst (fun x : ℝ => x^2)
    have hsnd : (∫ a : ℝ × ℝ, a.2^2 ∂((gaussianReal m v).prod (gaussianReal 0 v))) =
        (gaussianReal m v).real Set.univ • (∫ y : ℝ, y^2 ∂gaussianReal 0 v) := by
      exact integral_fun_snd (fun y : ℝ => y^2)
    rw [hfst, hsnd]
    simp [gaussian_square_integral]
    ring
  · exact gaussian_square_integrable m v |>.comp_fst (gaussianReal 0 v)
  · exact gaussian_square_integrable 0 v |>.comp_snd (gaussianReal m v)

def mixture (a b : ℝ) (v : ℝ≥0) : Measure ℂ :=
  (255/256 : ℝ≥0∞) • complexGaussian a v + (1/256 : ℝ≥0∞) • complexGaussian b v

private lemma mixture_EntryLaw (a b : ℝ) (v : ℝ≥0)
    (hmean : (255/256 : ℝ)*a + (1/256 : ℝ)*b = 0)
    (hsecond : (255/256 : ℝ)*(a^2+2*v) + (1/256 : ℝ)*(b^2+2*v) = 1) :
    D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.EntryLaw (mixture a b v) := by
  have hqtop : (255/256 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hptop : (1/256 : ℝ≥0∞) ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have ha := complexGaussian_integrable a v
  have hb := complexGaussian_integrable b v
  have ha2 := complexGaussian_second_integrable a v
  have hb2 := complexGaussian_second_integrable b v
  have haq := ha.smul_measure (c := (255/256 : ℝ≥0∞)) hqtop
  have hbp := hb.smul_measure (c := (1/256 : ℝ≥0∞)) hptop
  have ha2q := ha2.smul_measure (c := (255/256 : ℝ≥0∞)) hqtop
  have hb2p := hb2.smul_measure (c := (1/256 : ℝ≥0∞)) hptop
  refine ⟨?_, integrable_add_measure.mpr ⟨haq,hbp⟩,
    integrable_add_measure.mpr ⟨ha2q,hb2p⟩, ?_, ?_⟩
  · norm_num [mixture, Measure.add_apply, Measure.smul_apply, ENNReal.smul_def,
      ENNReal.div_eq_inv_mul, hqtop, hptop]
    have hsum : (255/256 : ℝ≥0∞) + (1/256 : ℝ≥0∞) = 1 := by
      have hst : (255/256 : ℝ≥0∞) + (1/256 : ℝ≥0∞) ≠ ∞ :=
        ENNReal.add_ne_top.mpr ⟨hqtop, hptop⟩
      apply (ENNReal.toReal_eq_toReal_iff' hst ENNReal.one_ne_top).mp
      rw [ENNReal.toReal_add hqtop hptop, ENNReal.toReal_div, ENNReal.toReal_div]
      norm_num
    simpa [ENNReal.div_eq_inv_mul, one_div] using hsum
  · rw [mixture, integral_add_measure haq hbp, integral_smul_measure, integral_smul_measure,
      complexGaussian_integral, complexGaussian_integral]
    norm_num [smul_eq_mul, ENNReal.div_eq_inv_mul, ENNReal.toReal_div, hqtop, hptop]
    apply Complex.ext <;> norm_num [hmean]
  · rw [mixture, integral_add_measure ha2q hb2p, integral_smul_measure, integral_smul_measure,
      complexGaussian_second_integral, complexGaussian_second_integral]
    norm_num [smul_eq_mul, ENNReal.smul_def, ENNReal.div_eq_inv_mul, ENNReal.toReal_div, hqtop, hptop]
    exact hsecond

def noiseVariance (ε : ℝ) : ℝ≥0 := ⟨ε^2 / (2*(1+ε^2)), by positivity⟩
def smoothLaw (ε : ℝ) : Measure ℂ :=
  mixture (-1 / (Real.sqrt 255 * Real.sqrt (1+ε^2)))
    (Real.sqrt 255 / Real.sqrt (1+ε^2)) (noiseVariance ε)

lemma smoothLaw_EntryLaw (ε : ℝ) : D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.EntryLaw (smoothLaw ε) := by
  have hs : Real.sqrt (255 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have ht : Real.sqrt (1+ε^2) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hs2 : Real.sqrt (255 : ℝ)^2 = 255 := Real.sq_sqrt (by norm_num)
  have ht2 : Real.sqrt (1+ε^2)^2 = 1+ε^2 := Real.sq_sqrt (by positivity)
  have hp : (1+ε^2) ≠ 0 := by positivity
  apply mixture_EntryLaw
  · field_simp
    nlinarith [hs2]
  · change (255/256 : ℝ)*((-1/(Real.sqrt 255*Real.sqrt (1+ε^2)))^2 +
        2*(ε^2/(2*(1+ε^2)))) +
      (1/256 : ℝ)*((Real.sqrt 255/Real.sqrt (1+ε^2))^2 +
        2*(ε^2/(2*(1+ε^2)))) = 1
    simp only [div_pow, mul_pow, neg_one_sq, hs2, ht2]
    field_simp [hp]
    <;> ring
end
end D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Smooth

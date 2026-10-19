/- GID: D5/S3/Quantum/Subentropy/GaussianMatrix
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GaussianMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Distributions.Gaussian.Multivariate]
   utility: none
   digest: Matrix subentropy is a common-coordinate Gaussian entropy expectation. -/

import D5.S3.Quantum.Subentropy.GaussianDiagonal
import D5.S3.Quantum.Subentropy.GaussianQuadratic
import D5.S3.Quantum.Subentropy.DensityKernel
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Unitary spectral transport supplies a common Gaussian measure for all matrices
of a fixed dimension. No nonzero-spectrum or invertibility hypothesis is used. -/

noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Subentropy.GaussianMatrix
open _root_.D5.S3.Quantum.Subentropy.Basic
open _root_.D5.S3.Quantum.Subentropy.DensityKernel
open _root_.D5.S3.Quantum.Subentropy.GaussianDiagonal
open _root_.D5.S3.Quantum.Subentropy.GaussianQuadratic

private theorem measurable_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : Measurable (gaussianQuadratic A) := by
  have hlin := (Matrix.toEuclideanLin A).continuous_of_finiteDimensional
  exact ((Complex.continuous_re.comp (continuous_id.inner hlin)).div_const 2).measurable

private theorem measurable_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (complexGaussianCoordinates : ((ι × Fin 2) → ℝ) → EuclideanSpace ℂ ι) := by
  unfold complexGaussianCoordinates
  simp_rw [Complex.mk_eq_add_mul_I]
  fun_prop

/-- A positive semidefinite trace-one matrix has integrable Gaussian quadratic-form
entropy, and its subentropy equals that expectation minus a fixed coordinate baseline. -/
theorem matrix_subentropy_gaussian_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (htr : A.trace = 1) (i₀ : ι) :
    Integrable (fun z => Real.negMulLog (gaussianQuadratic A z))
      (stdGaussian (EuclideanSpace ℂ ι)) ∧
    matrixSubentropy A =
      (∫ z, Real.negMulLog (gaussianQuadratic A z)
        ∂stdGaussian (EuclideanSpace ℂ ι)) -
      (∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (((z (i₀,0))^2 + (z (i₀,1))^2)/2)
        ∂Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)) := by
  classical
  let p := hA.isHermitian.eigenvalues
  have hp := spectral_prob hA htr
  have hd := diagonal_subentropy_gaussian_entropy p hp.1 hp.2 i₀
  let γ := Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)
  let T := fun z : (ι × Fin 2) → ℝ =>
    hA.isHermitian.eigenvectorBasis.repr.symm (complexGaussianCoordinates z)
  have hTm : Measurable T :=
    hA.isHermitian.eigenvectorBasis.repr.symm.continuous.measurable.comp measurable_coordinates
  have hmap : γ.map T = stdGaussian (EuclideanSpace ℂ ι) := by
    change (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map
      (hA.isHermitian.eigenvectorBasis.repr.symm ∘ complexGaussianCoordinates) = _
    rw [← Measure.map_map
      hA.isHermitian.eigenvectorBasis.repr.symm.continuous.measurable measurable_coordinates,
      complex_coordinate_transport.1, (spectral_transport hA.isHermitian).2]
  have heq (z : (ι × Fin 2) → ℝ) :
      gaussianQuadratic A (T z) =
        ∑ i, p i * (((z (i,0))^2 + (z (i,1))^2)/2) := by
    rw [(spectral_transport hA.isHermitian).1]
    simp_rw [complex_coordinate_transport.2]
    simp only [Finset.sum_div, mul_div_assoc, p]
  have hfm : AEStronglyMeasurable
      (fun z => Real.negMulLog (gaussianQuadratic A z)) (γ.map T) :=
    (Real.continuous_negMulLog.measurable.comp (measurable_quadratic A)).aestronglyMeasurable
  have hi : Integrable (fun z => Real.negMulLog (gaussianQuadratic A z)) (γ.map T) := by
    apply (integrable_map_measure hfm hTm.aemeasurable).2
    simpa only [Function.comp_def, heq] using hd.1
  have hint : (∫ z, Real.negMulLog (gaussianQuadratic A z)
      ∂stdGaussian (EuclideanSpace ℂ ι)) =
      ∫ z : (ι × Fin 2) → ℝ,
        Real.negMulLog (∑ i, p i * (((z (i,0))^2 + (z (i,1))^2)/2)) ∂γ := by
    rw [← hmap, integral_map hTm.aemeasurable hfm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => congrArg Real.negMulLog (heq z))
  refine ⟨hmap ▸ hi, ?_⟩
  rw [hint, ← hd.2]
  let U : Matrix ι ι ℂ := hA.isHermitian.eigenvectorUnitary
  have hs : A = U * diagonal (fun i => (p i : ℂ)) * U.conjTranspose :=
    hA.isHermitian.spectral_theorem
  rw [hs]
  exact matrixSubentropy_isometric_embedding _ U
    (Unitary.coe_star_mul_self hA.isHermitian.eigenvectorUnitary)

end D5.S3.Quantum.Subentropy.GaussianMatrix

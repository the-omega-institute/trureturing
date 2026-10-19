/- GID: D5/S3/Quantum/Subentropy/GaussianQuadratic
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/GaussianQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Distributions.Gaussian.Multivariate]
   utility: none
   digest: Spectral transport of matrix quadratic forms under standard Gaussian measure. -/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-! Complex quadratic forms use the standard real Gaussian in the underlying Euclidean space. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder
namespace D5.S3.Quantum.Subentropy.GaussianQuadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix quadratic form with the complex-Gaussian normalization. -/
def gaussianQuadratic (A : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) : ℝ :=
  (inner ℂ z (Matrix.toEuclideanLin A z)).re / 2

/-- Pair real and imaginary independent coordinates into the canonical complex Euclidean space. -/
def complexGaussianCoordinates (z : (ι × Fin 2) → ℝ) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (⟨z (i, 0), z (i, 1)⟩ : ℂ))

private def complexRealBasis : OrthonormalBasis (ι × Fin 2) ℝ (EuclideanSpace ℂ ι) :=
  (Pi.orthonormalBasis (fun _ : ι => Complex.orthonormalBasisOneI)).reindex
    (Equiv.sigmaEquivProd ι (Fin 2))

private theorem complexCoordinates_repr (z : (ι × Fin 2) → ℝ) :
    complexRealBasis.repr (complexGaussianCoordinates z) = WithLp.toLp 2 z := by
  apply PiLp.ext
  rintro ⟨i, j⟩
  fin_cases j <;>
    simp [complexRealBasis, OrthonormalBasis.repr_reindex,
      Pi.orthonormalBasis_repr, complexGaussianCoordinates]

theorem complex_coordinate_transport :
    (Measure.pi (fun _ : ι × Fin 2 => gaussianReal 0 1)).map complexGaussianCoordinates =
      stdGaussian (EuclideanSpace ℂ ι) ∧
    ∀ (z : (ι × Fin 2) → ℝ) (i : ι),
      Complex.normSq (complexGaussianCoordinates z i) = z (i, 0)^2 + z (i, 1)^2 := by
  constructor
  · have hfun : (complexGaussianCoordinates : ((ι × Fin 2) → ℝ) → EuclideanSpace ℂ ι) =
        complexRealBasis.repr.symm ∘ WithLp.toLp 2 := by
      funext z
      apply complexRealBasis.repr.injective
      rw [complexCoordinates_repr]
      simp
    rw [hfun, ← Measure.map_map, map_pi_eq_stdGaussian, stdGaussian_map]
    all_goals fun_prop
  · intro z i
    simp [complexGaussianCoordinates, Complex.normSq_apply, pow_two]

private def realIsometry (e : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  { e.toLinearEquiv.restrictScalars ℝ with norm_map' := e.norm_map }

private theorem eigenvector_action {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (i : ι) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
  apply PiLp.ext
  intro j
  have h := congrFun (hA.mulVec_eigenvectorBasis i) j
  simpa only [Matrix.toLpLin_apply, PiLp.smul_apply, Pi.smul_apply, RCLike.real_smul_eq_coe_mul,
    RCLike.ofReal_eq_complex_ofReal, smul_eq_mul] using h

private theorem spectral_action {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (w : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin A (hA.eigenvectorBasis.repr.symm w) =
      hA.eigenvectorBasis.repr.symm
        (WithLp.toLp 2 (fun i => (hA.eigenvalues i : ℂ) * w i)) := by
  simp only [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, eigenvector_action]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_smul, PiLp.toLp_apply]
  congr 1
  exact mul_comm _ _

/-- Spectral change of coordinates diagonalizes the quadratic form and preserves the
standard real Gaussian. The identity includes repeated and zero eigenvalues. -/
theorem spectral_transport {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (∀ w : EuclideanSpace ℂ ι,
      gaussianQuadratic A (hA.eigenvectorBasis.repr.symm w) =
        (∑ i, hA.eigenvalues i * Complex.normSq (w i)) / 2) ∧
    (stdGaussian (EuclideanSpace ℂ ι)).map hA.eigenvectorBasis.repr.symm =
      stdGaussian (EuclideanSpace ℂ ι) := by
  constructor
  · intro w
    unfold gaussianQuadratic
    rw [spectral_action hA]
    rw [hA.eigenvectorBasis.repr.symm.inner_map_map]
    simp only [PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply, Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, Complex.mul_conj, Complex.mul_re]
    simp
  · exact stdGaussian_map (realIsometry hA.eigenvectorBasis.repr.symm)

theorem quadratic_nonnegative {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (z : EuclideanSpace ℂ ι) : 0 ≤ gaussianQuadratic A z := by
  apply div_nonneg _ (by norm_num)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, dotProduct_comm, RCLike.re_eq_complex_re] using
    hA.re_dotProduct_nonneg (WithLp.ofLp z)


end D5.S3.Quantum.Subentropy.GaussianQuadratic

/- GID: D5/S3/Observer/Linear/GaussianObservationPrecision
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GaussianObservationPrecision
   mirror-E: none(waiver:general-gaussian-precision-construction)
   anchors: []
   digest: Construct positive Gaussian observation precision, its inverse and unique quadratic mode, and an actual Gaussian law with those moments. -/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
The precision matrix is derived from an actual rectangular observation M,
positive prior precision beta and nonnegative noise precision tau. There is
no full-rank hypothesis on M. In the physical experiment tau = 1/sigma^2.

The posterior candidate is an actual Mathlib Gaussian probability measure;
its moments are proved from the constructed positive covariance. Completing
the likelihood square and normalizing a Gaussian kernel are distinct steps:
the conditional-law/disintegration identification, mutual information and
optimality over all measurable estimators are not claimed in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.Linear.GaussianObservationPrecision

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- Constructed posterior precision. -/
def precision (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n n ℝ :=
  β • (1 : Matrix n n ℝ) + τ • (M.transpose * M)

def covariance (M : Matrix p n ℝ) (β τ : ℝ) : Matrix n n ℝ :=
  (precision M β τ)⁻¹

def score (M : Matrix p n ℝ) (τ : ℝ) (y : p → ℝ) : n → ℝ :=
  τ • M.transpose.mulVec y

def center (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) : n → ℝ :=
  (covariance M β τ).mulVec (score M τ y)

/-- Squared prior-plus-likelihood exponent, prior mean zero. -/
def loss (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) (x : n → ℝ) : ℝ :=
  β * (x ⬝ᵥ x) + τ * ((y - M.mulVec x) ⬝ᵥ (y - M.mulVec x))

theorem precision_symmetric (M : Matrix p n ℝ) (β τ : ℝ) :
    (precision M β τ).transpose = precision M β τ := by
  simp [precision, Matrix.transpose_mul]

theorem precision_quadratic (M : Matrix p n ℝ) (β τ : ℝ) (x : n → ℝ) :
    x ⬝ᵥ (precision M β τ).mulVec x =
      β * (x ⬝ᵥ x) + τ * (M.mulVec x ⬝ᵥ M.mulVec x) := by
  simp only [precision, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]

/-- Prior precision makes the matrix strictly positive even for blind sensors. -/
theorem precision_posDef (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    (precision M β τ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose, star_trivial] using
      precision_symmetric M β τ
  · intro x hx
    have hxpos : 0 < x ⬝ᵥ x := by
      simpa using (Matrix.PosDef.one (R := ℝ) (n := n)).dotProduct_mulVec_pos hx
    have hm : 0 ≤ M.mulVec x ⬝ᵥ M.mulVec x := by
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    simpa only [star_trivial, precision_quadratic] using
      add_pos_of_pos_of_nonneg (mul_pos hβ hxpos) (mul_nonneg hτ hm)

theorem covariance_posDef (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    (covariance M β τ).PosDef := (precision_posDef M β τ hβ hτ).inv

/-- Both inverse equations are derived, not supplied as hypotheses. -/
theorem precision_inverse (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ) :
    precision M β τ * covariance M β τ = 1 ∧
      covariance M β τ * precision M β τ = 1 := by
  have hu := (precision M β τ).isUnit_iff_isUnit_det.mp
    (precision_posDef M β τ hβ hτ).isUnit
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩

theorem center_equation (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (y : p → ℝ) : (precision M β τ).mulVec (center M β τ y) = score M τ y := by
  unfold center
  rw [Matrix.mulVec_mulVec, (precision_inverse M β τ hβ hτ).1, Matrix.one_mulVec]

theorem loss_expand (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) (x : n → ℝ) :
    loss M β τ y x = x ⬝ᵥ (precision M β τ).mulVec x -
      2 * (x ⬝ᵥ score M τ y) + τ * (y ⬝ᵥ y) := by
  rw [precision_quadratic]
  simp only [loss, score, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_eq_mul, Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (M.mulVec x) y]
  ring

/-- Full rectangular-observation completion of the square with constructed center. -/
theorem complete_square (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (y : p → ℝ) (x : n → ℝ) :
    loss M β τ y x =
      (x - center M β τ y) ⬝ᵥ (precision M β τ).mulVec (x - center M β τ y) +
        τ * (y ⬝ᵥ y) - center M β τ y ⬝ᵥ score M τ y := by
  let m := center M β τ y
  have hs : m ⬝ᵥ (precision M β τ).mulVec x =
      x ⬝ᵥ (precision M β τ).mulVec m := by
    simpa only [precision_symmetric] using
      Matrix.dotProduct_transpose_mulVec (precision M β τ) m x
  rw [loss_expand]
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  change x ⬝ᵥ (precision M β τ).mulVec x - 2 * (x ⬝ᵥ score M τ y) +
    τ * (y ⬝ᵥ y) =
    (x ⬝ᵥ (precision M β τ).mulVec x - m ⬝ᵥ (precision M β τ).mulVec x) -
      (x ⬝ᵥ (precision M β τ).mulVec m - m ⬝ᵥ (precision M β τ).mulVec m) +
        τ * (y ⬝ᵥ y) - m ⬝ᵥ score M τ y
  rw [hs, show (precision M β τ).mulVec m = score M τ y from
    center_equation M β τ hβ hτ y]
  ring

/-- The constructed center is the unique minimizer of the actual exponent. -/
theorem unique_quadratic_mode (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (y : p → ℝ) (x : n → ℝ) :
    loss M β τ y (center M β τ y) ≤ loss M β τ y x ∧
      (loss M β τ y x = loss M β τ y (center M β τ y) ↔ x = center M β τ y) := by
  have hx := complete_square M β τ hβ hτ y x
  have hm := complete_square M β τ hβ hτ y (center M β τ y)
  simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero, zero_add] at hm
  by_cases heq : x = center M β τ y
  · subst x
    exact ⟨le_rfl, iff_of_true rfl rfl⟩
  · have hpos := (precision_posDef M β τ hβ hτ).dotProduct_mulVec_pos (sub_ne_zero.mpr heq)
    simp only [star_trivial] at hpos
    constructor
    · linarith
    · constructor
      · intro h
        exfalso
        linarith
      · exact fun h => (heq h).elim

/-- Actual factorization of the unnormalized Gaussian likelihood product.
This identity does not silently assert a conditional-probability theorem. -/
theorem exponential_kernel_factorization (M : Matrix p n ℝ) (β τ : ℝ)
    (hβ : 0 < β) (hτ : 0 ≤ τ) (y : p → ℝ) (x : n → ℝ) :
    Real.exp (-loss M β τ y x / 2) =
      Real.exp (-(τ * (y ⬝ᵥ y) - center M β τ y ⬝ᵥ score M τ y) / 2) *
      Real.exp (-((x - center M β τ y) ⬝ᵥ
        (precision M β τ).mulVec (x - center M β τ y)) / 2) := by
  rw [← Real.exp_add, complete_square M β τ hβ hτ y x]
  congr 1
  ring

/-- A genuine Gaussian probability measure with the constructed candidate parameters. -/
def candidateLaw (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) :
    Measure (EuclideanSpace ℝ n) :=
  multivariateGaussian (WithLp.toLp 2 (center M β τ y)) (covariance M β τ)

instance candidateLaw_probability (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) :
    IsProbabilityMeasure (candidateLaw M β τ y) := by
  unfold candidateLaw
  infer_instance

theorem candidateLaw_mean (M : Matrix p n ℝ) (β τ : ℝ) (y : p → ℝ) :
    ∫ x, x ∂candidateLaw M β τ y = WithLp.toLp 2 (center M β τ y) := by
  exact integral_id_multivariateGaussian

/-- The inverse precision is the actual covariance, with its positivity proved above. -/
theorem candidateLaw_covariance (M : Matrix p n ℝ) (β τ : ℝ) (hβ : 0 < β) (hτ : 0 ≤ τ)
    (y : p → ℝ) (i j : n) :
    cov[fun x => x i, fun x => x j; candidateLaw M β τ y] = covariance M β τ i j := by
  exact covariance_eval_multivariateGaussian (covariance_posDef M β τ hβ hτ).posSemidef i j

#print axioms precision_posDef
#print axioms precision_inverse
#print axioms complete_square
#print axioms unique_quadratic_mode
#print axioms exponential_kernel_factorization
#print axioms candidateLaw_covariance
end D5.S3.Observer.Linear.GaussianObservationPrecision

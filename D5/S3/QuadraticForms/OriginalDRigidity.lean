/- GID: D5/S3/QuadraticForms/OriginalDRigidity
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OriginalDRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The common two-label Hermitian boundary forces scalar skew symmetry of the old relation. -/

/- Stage-A declaration audit.
   proof_shape: content; the consumed private helper performs the Hermitian-boundary
     extraction and is not a bind-only alias.
   escape_witness: response_skew_of_three_label, whose proof uses the PSD Hermitian
     boundary and complex-imaginary projection to derive a new scalar relation.
   admission_basis: reusable scalar rigidity boundary; the full original-D
     additivity and all-finite positivity endpoint remains open.
   Direct frozen dependencies: Matrix.PosSemidef.isHermitian. -/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! Three-label positive response tables and the resulting original relation. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.OriginalDRigidity

open scoped ComplexConjugate ComplexOrder
open scoped BigOperators
open Matrix

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def responseKernel (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (α : E →ₗ[ℝ] ℝ) (a b : E) : ℂ :=
  (α (S a b) : ℂ) - Complex.I * (α (D a b) : ℂ)

def responseMatrix (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) (α : E →ₗ[ℝ] ℝ)
    {n : ℕ} (a : Fin n → E) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => responseKernel S D α (a i) (a j)

def ThreeLabelPSD (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E)
    (α : E →ₗ[ℝ] ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ 3 → ∀ (a : Fin n → E),
    Matrix.PosSemidef (responseMatrix S D α a)

private theorem response_skew_of_three_label
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) (α : E →ₗ[ℝ] ℝ)
    (hS : ∀ x y, S x y = S y x) (hPSD : ThreeLabelPSD S D α)
    (x y : E) :
    α (D y x) = - α (D x y) := by
  have h := hPSD 2 (by norm_num) (![x, y])
  have he := h.isHermitian.apply (0 : Fin 2) 1
  have heR := congrArg Complex.re he
  have heI := congrArg Complex.im he
  simp [responseMatrix, responseKernel, hS] at heR heI
  linarith

/-- The common two-label Hermitian boundary forces skew symmetry of the old relation
at every separating real evaluation. This is the first source-faithful rigidity step;
no division by a mass or Gram determinant is used. -/
theorem three_label_skew
    (S : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) (α : E →ₗ[ℝ] ℝ)
    (hS : ∀ x y, S x y = S y x) (hPSD : ThreeLabelPSD S D α) :
    ∀ x y, α (D y x) = -α (D x y) := by
  intro x y
  exact response_skew_of_three_label S D α hS hPSD x y

end D5.S3.QuadraticForms.OriginalDRigidity

/- GID: D5/S3/Quantum/Subentropy/Basic
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/Basic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: Determinant-integral subentropy and invariance under rectangular Gram conversion. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Subentropy through a one-dimensional determinant integral. -/

noncomputable section
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Subentropy.Basic

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel

/-- The determinant kernel on the positive real half-line. -/
def subentropyKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (t : ℝ) : ℝ :=
  t / (1 + t) - ((Matrix.det (1 + (t⁻¹ : ℝ) • A)).re)⁻¹

/-- The determinant-integral representation of subentropy. -/
def matrixSubentropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), subentropyKernel A t

/-- Subentropy of the canonical bundled finite density state. -/
def subentropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityState ι) : ℝ :=
  matrixSubentropy (CStarMatrix.ofMatrix.symm ρ.1)

/-- Rectangular Gram conversion preserves the entire determinant kernel.
No positivity or trace assumption is needed for this algebraic identity. -/
theorem kernel_rectangular_gram {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (t : ℝ) :
    subentropyKernel (V.conjTranspose * V) t =
      subentropyKernel (V * V.conjTranspose) t := by
  unfold subentropyKernel
  congr 3
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using
    Matrix.det_one_add_mul_comm ((t⁻¹ : ℝ) • V.conjTranspose) V

/-- Subentropy is invariant under rectangular Gram conversion. -/
theorem matrixSubentropy_rectangular_gram {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    matrixSubentropy (V.conjTranspose * V) =
      matrixSubentropy (V * V.conjTranspose) := by
  unfold matrixSubentropy
  exact integral_congr_ae (Filter.Eventually.of_forall (kernel_rectangular_gram V))

/-- Isometric compression and embedding preserve subentropy. -/
theorem matrixSubentropy_isometric_embedding {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (J : Matrix ι κ ℂ)
    (hJ : J.conjTranspose * J = 1) :
    matrixSubentropy (J * A * J.conjTranspose) = matrixSubentropy A := by
  unfold matrixSubentropy subentropyKernel
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have h := Matrix.det_one_add_mul_comm ((t⁻¹ : ℝ) • (J * A)) J.conjTranspose
  simp only [Matrix.smul_mul, Matrix.mul_smul] at h
  rw [← Matrix.mul_assoc J.conjTranspose J A, hJ, Matrix.one_mul] at h
  exact congrArg (fun z : ℂ => t / (1 + t) - z.re⁻¹) h

/-- The scalar state of trace one has zero subentropy. -/
private theorem matrixSubentropy_one_unique {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Unique ι] : matrixSubentropy (1 : Matrix ι ι ℂ) = 0 := by
  unfold matrixSubentropy
  have h : ∀ t ∈ Ioi (0 : ℝ), subentropyKernel (1 : Matrix ι ι ℂ) t = 0 := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp only [subentropyKernel, Matrix.det_unique, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, mul_one,
      Complex.add_re, Complex.one_re, Complex.real_smul, Complex.inv_re,
      Complex.ofReal_re]
    field_simp
    <;> ring
  rw [setIntegral_congr_fun measurableSet_Ioi h]
  simp

/-- A normalized rank-one Gram matrix is a pure state and has zero subentropy. -/
theorem matrixSubentropy_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (hv : ∑ i, star (v i) * v i = 1) :
    matrixSubentropy (Matrix.vecMulVec v (star v)) = 0 := by
  let V : Matrix ι Unit ℂ := fun i _ => v i
  have hleft : V.conjTranspose * V = 1 := by
    ext i j
    change (∑ k, star (v k) * v k) = (1 : Matrix Unit Unit ℂ) i j
    simpa using hv
  have hright : V * V.conjTranspose = Matrix.vecMulVec v (star v) := by
    ext i j
    change (∑ k : Unit, v i * star (v j)) = v i * star (v j)
    simp
  rw [← hright, ← matrixSubentropy_rectangular_gram V, hleft]
  exact matrixSubentropy_one_unique

/-- The kernel of a diagonal matrix is its classical product kernel. -/
theorem kernel_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (t : ℝ) (ht : t ≠ 0) :
    subentropyKernel (Matrix.diagonal (fun i => (p i : ℂ))) t =
      t / (1 + t) - ∏ i, t / (t + p i) := by
  have hdiag : (1 : Matrix ι ι ℂ) + (t⁻¹ : ℝ) • diagonal (fun i => (p i : ℂ)) =
      diagonal (fun i => ((1 + t⁻¹ * p i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
    · simp [Matrix.one_apply, Matrix.diagonal_apply, hij]
  rw [subentropyKernel, hdiag, Matrix.det_diagonal]
  simp only [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_inv_distrib]
  congr 1
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [show 1 + t⁻¹ * p i = (t + p i) / t by field_simp <;> ring]
  simp [div_eq_mul_inv, mul_comm]

end D5.S3.Quantum.Subentropy.Basic

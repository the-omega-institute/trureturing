/- GID: D5/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/FiniteLocalizedStieltjesKernelFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor finite atomic Stieltjes mass and support kernels through one Cauchy feature matrix and two diagonal weight matrices. -/

import D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel
import Mathlib.Tactic

/-!
# Finite localized Stieltjes kernel factorization

A finite atomic Stieltjes family uses one Cauchy feature matrix. The ordinary
Nevanlinna Gram matrix inserts the mass diagonal, while coordinate localization
inserts the mass-times-support diagonal. This module proves the finite algebraic
factorization only. It does not assert full column rank or an inertia theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix Finset
open scoped ComplexConjugate BigOperators

namespace D5.S3.Weil.Pick.FiniteLocalizedStieltjesKernelFactorization

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares
open D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- The Stieltjes transform of a finite real atomic family. -/
def finiteAtomicStieltjesTransform
    (mass support : Atom → ℝ) (z : ℂ) : ℂ :=
  ∑ a, atomicStieltjesTransform (mass a) (support a) z

/-- The coordinate-localized transform of a finite real atomic family. -/
def finiteLocalizedAtomicStieltjesTransform
    (mass support : Atom → ℝ) (z : ℂ) : ℂ :=
  ∑ a, localizedAtomicStieltjesTransform (mass a) (support a) z

/-- The finite Hermitian kernel whose atomic weights are the masses. -/
def finiteMassKernel
    (mass support : Atom → ℝ) : HermitianKernel ℂ where
  value := fun z w =>
    ∑ a, (atomicMassKernel (mass a) (support a)).value z w
  conj_symm := by
    intro z w
    rw [star_sum]
    exact Finset.sum_congr rfl (fun a _ =>
      (atomicMassKernel (mass a) (support a)).conj_symm z w)

/-- The finite Hermitian kernel whose atomic weights are mass times support. -/
def finiteSupportKernel
    (mass support : Atom → ℝ) : HermitianKernel ℂ where
  value := fun z w =>
    ∑ a, (atomicSupportKernel (mass a) (support a)).value z w
  conj_symm := by
    intro z w
    rw [star_sum]
    exact Finset.sum_congr rfl (fun a _ =>
      (atomicSupportKernel (mass a) (support a)).conj_symm z w)

/-- The rectangular Cauchy feature matrix at a finite sample family. -/
def cauchyFeatureMatrix {n : ℕ}
    (support : Atom → ℝ) (points : Fin n → ℂ) :
    Matrix (Fin n) Atom ℂ :=
  fun i a => stieltjesFeature (support a) (points i)

/-- The diagonal matrix of atomic masses. -/
def massWeightMatrix (mass : Atom → ℝ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal (fun a => (mass a : ℂ))

/-- The diagonal matrix of mass-times-support localizing weights. -/
def supportWeightMatrix
    (mass support : Atom → ℝ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal (fun a => ((mass a * support a : ℝ) : ℂ))

/-- Finite coordinate localization commutes with summation. -/
theorem finite_localized_transform_eq_coordinate_mul
    (mass support : Atom → ℝ) (z : ℂ) :
    finiteLocalizedAtomicStieltjesTransform mass support z =
      z * finiteAtomicStieltjesTransform mass support z := by
  simp [finiteLocalizedAtomicStieltjesTransform,
    finiteAtomicStieltjesTransform, localizedAtomicStieltjesTransform,
    Finset.mul_sum]

/-- Every finite support kernel is the sum of support-scaled atomic mass
kernels. No common support scalar is pulled outside the sum. -/
theorem finite_support_kernel_eq_sum_support_mul_mass_kernel
    (mass support : Atom → ℝ) (z w : ℂ) :
    (finiteSupportKernel mass support).value z w =
      ∑ a, (support a : ℂ) *
        (atomicMassKernel (mass a) (support a)).value z w := by
  apply Finset.sum_congr rfl
  intro a _
  exact atomic_support_kernel_eq_support_mul_mass_kernel
    (mass a) (support a) z w

/-- The finite ordinary Gram matrix factors as `C D_mass Cᴴ`. -/
theorem finite_mass_gram_factorization {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) :
    (finiteMassKernel mass support).gramMatrix points =
      cauchyFeatureMatrix support points * massWeightMatrix mass *
        Matrix.conjTranspose (cauchyFeatureMatrix support points) := by
  classical
  ext i j
  simp only [HermitianKernel.gramMatrix, finiteMassKernel,
    atomicMassKernel, massWeightMatrix]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_diagonal]
  simp only [cauchyFeatureMatrix, Matrix.conjTranspose_apply]
  ring

/-- The finite localized Gram matrix factors as `C D_support Cᴴ`, where the
localizing diagonal is `mass * support`. -/
theorem finite_support_gram_factorization {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) :
    (finiteSupportKernel mass support).gramMatrix points =
      cauchyFeatureMatrix support points *
        supportWeightMatrix mass support *
        Matrix.conjTranspose (cauchyFeatureMatrix support points) := by
  classical
  ext i j
  simp only [HermitianKernel.gramMatrix, finiteSupportKernel,
    atomicSupportKernel, supportWeightMatrix]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_diagonal]
  simp only [cauchyFeatureMatrix, Matrix.conjTranspose_apply]
  ring

/-- For one atom, the finite factorization reduces to the atomic kernels. -/
example (mass support : ℝ) (z w : ℂ) :
    let m : Fin 1 → ℝ := fun _ => mass
    let x : Fin 1 → ℝ := fun _ => support
    (finiteMassKernel m x).value z w =
      (atomicMassKernel mass support).value z w ∧
    (finiteSupportKernel m x).value z w =
      (atomicSupportKernel mass support).value z w := by
  simp [finiteMassKernel, finiteSupportKernel]

#print axioms finite_localized_transform_eq_coordinate_mul
#print axioms finite_support_kernel_eq_sum_support_mul_mass_kernel
#print axioms finite_mass_gram_factorization
#print axioms finite_support_gram_factorization

end D5.S3.Weil.Pick.FiniteLocalizedStieltjesKernelFactorization

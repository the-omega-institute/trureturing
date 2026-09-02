/- GID: D5/S3/Weil/Pick/MassSupportKernelPencil
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/MassSupportKernelPencil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recover finite support coordinates as generalized eigenvalues of the localized Stieltjes mass-support Gram pencil under explicit dual Cauchy-feature certificates. -/

import D5.S3.Weil.Pick.FiniteLocalizedStieltjesKernelFactorization
import Mathlib.Tactic

/-!
# Mass-support kernel pencil

The two finite Gram matrices share the same Cauchy feature matrix. Their pencil
therefore replaces each atomic diagonal weight `mass * support` by
`mass * (support - lambda)`. An explicit dual Cauchy feature for one atom gives
a generalized eigenvector at exactly that atom's support coordinate.

The dual-feature hypothesis is the local algebraic certificate needed here. No
unproved global Cauchy full-rank theorem is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix Finset
open scoped ComplexConjugate BigOperators

namespace D5.S3.Weil.Pick.MassSupportKernelPencil

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares
open D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel
open D5.S3.Weil.Pick.FiniteLocalizedStieltjesKernelFactorization

variable {Atom : Type*} [Fintype Atom] [DecidableEq Atom]

/-- The ordinary finite Stieltjes Gram matrix. -/
def massGramMatrix {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (finiteMassKernel mass support).gramMatrix points

/-- The coordinate-localized finite Stieltjes Gram matrix. -/
def supportGramMatrix {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (finiteSupportKernel mass support).gramMatrix points

/-- The localized mass-support Gram pencil `K_support - lambda K_mass`. -/
def massSupportKernelPencil {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) (lambda : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  supportGramMatrix mass support points -
    (lambda : ℂ) • massGramMatrix mass support points

/-- The diagonal pencil weight at each atom. -/
def shiftedSupportWeightMatrix
    (mass support : Atom → ℝ) (lambda : ℝ) : Matrix Atom Atom ℂ :=
  Matrix.diagonal
    (fun a => ((mass a * (support a - lambda) : ℝ) : ℂ))

/-- The sampled Cauchy column belonging to one support atom. -/
def cauchyAtomVector {n : ℕ}
    (support : Atom → ℝ) (points : Fin n → ℂ) (a : Atom) :
    Fin n → ℂ :=
  fun i => stieltjesFeature (support a) (points i)

/-- A sample-space vector is dual to atom `a` when Cauchy analysis returns the
coordinate vector concentrated at `a`. -/
def IsCauchyDual {n : ℕ}
    (support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ) : Prop :=
  Matrix.conjTranspose (cauchyFeatureMatrix support points) *ᵥ v =
    fun b => if b = a then 1 else 0

/-- A nondegenerate generalized eigenpair of the support Gram matrix relative
to the mass Gram matrix. -/
def IsSupportedGeneralizedEigenpair {n : ℕ}
    (supportGram massGram : Matrix (Fin n) (Fin n) ℂ)
    (lambda : ℝ) (v : Fin n → ℂ) : Prop :=
  v ≠ 0 ∧
    massGram *ᵥ v ≠ 0 ∧
    supportGram *ᵥ v = (lambda : ℂ) • (massGram *ᵥ v)

/-- The whole mass-support pencil factors through the shifted atomic diagonal. -/
theorem mass_support_kernel_pencil_factorization {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ) (lambda : ℝ) :
    massSupportKernelPencil mass support points lambda =
      cauchyFeatureMatrix support points *
        shiftedSupportWeightMatrix mass support lambda *
        Matrix.conjTranspose (cauchyFeatureMatrix support points) := by
  classical
  ext i j
  simp [massSupportKernelPencil, massGramMatrix, supportGramMatrix,
    HermitianKernel.gramMatrix, finiteMassKernel, finiteSupportKernel,
    cauchyFeatureMatrix, shiftedSupportWeightMatrix,
    atomicMassKernel, atomicSupportKernel,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    mul_comm, mul_left_comm, mul_assoc]
  ring

/-- A Cauchy-dual vector is nonzero, because its analyzed coordinate at the
selected atom is one. -/
theorem cauchy_dual_vector_ne_zero {n : ℕ}
    (support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v) :
    v ≠ 0 := by
  unfold IsCauchyDual at hdual
  intro hv
  have hzeroOne : (0 : ℂ) = 1 := by
    simpa [hv, Matrix.mulVec] using congrFun hdual a
  exact zero_ne_one hzeroOne

/-- Under a dual Cauchy certificate, the mass Gram matrix selects exactly one
atomic Cauchy column with coefficient equal to its mass. -/
theorem mass_gram_mulVec_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v) :
    massGramMatrix mass support points *ᵥ v =
      (mass a : ℂ) • cauchyAtomVector support points a := by
  unfold IsCauchyDual at hdual
  rw [massGramMatrix, finite_mass_gram_factorization,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdual]
  funext i
  simp [massWeightMatrix, cauchyFeatureMatrix, cauchyAtomVector,
    Matrix.mulVec, mul_comm, mul_left_comm, mul_assoc]

/-- Under the same certificate, the support Gram matrix selects the same
Cauchy column with coefficient equal to mass times support. -/
theorem support_gram_mulVec_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v) :
    supportGramMatrix mass support points *ᵥ v =
      (((mass a * support a : ℝ) : ℂ)) •
        cauchyAtomVector support points a := by
  unfold IsCauchyDual at hdual
  rw [supportGramMatrix, finite_support_gram_factorization,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdual]
  funext i
  simp [supportWeightMatrix, cauchyFeatureMatrix, cauchyAtomVector,
    Matrix.mulVec, mul_comm, mul_left_comm, mul_assoc]

/-- A dual atom obeys the exact generalized eigenrelation at its support
coordinate. -/
theorem support_gram_eigenrelation_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v) :
    supportGramMatrix mass support points *ᵥ v =
      (support a : ℂ) • (massGramMatrix mass support points *ᵥ v) := by
  rw [mass_gram_mulVec_of_dual mass support points a v hdual,
    support_gram_mulVec_of_dual mass support points a v hdual]
  funext i
  simp [cauchyAtomVector]
  ring

/-- At the recovered support coordinate, the Gram pencil annihilates the dual
vector. -/
theorem pencil_mulVec_at_support_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v) :
    massSupportKernelPencil mass support points (support a) *ᵥ v = 0 := by
  rw [massSupportKernelPencil, Matrix.sub_mulVec, Matrix.smul_mulVec,
    support_gram_eigenrelation_of_dual mass support points a v hdual]
  simp

/-- If the selected mass and at least one sampled Cauchy feature are nonzero,
then the relative mass action is nonzero. -/
theorem mass_gram_mulVec_ne_zero_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v)
    (hmass : mass a ≠ 0)
    (hfeature : ∃ i, stieltjesFeature (support a) (points i) ≠ 0) :
    massGramMatrix mass support points *ᵥ v ≠ 0 := by
  rw [mass_gram_mulVec_of_dual mass support points a v hdual]
  intro hzero
  obtain ⟨i, hi⟩ := hfeature
  have hmassComplex : (mass a : ℂ) ≠ 0 := by
    exact_mod_cast hmass
  have hproduct :
      (mass a : ℂ) * stieltjesFeature (support a) (points i) = 0 := by
    simpa [cauchyAtomVector] using congrFun hzero i
  exact (mul_ne_zero hmassComplex hi) hproduct

/-- The dual feature certificate packages a genuine generalized eigenpair at
the selected support coordinate. -/
theorem support_is_generalized_eigenvalue_of_dual {n : ℕ}
    (mass support : Atom → ℝ) (points : Fin n → ℂ)
    (a : Atom) (v : Fin n → ℂ)
    (hdual : IsCauchyDual support points a v)
    (hmass : mass a ≠ 0)
    (hfeature : ∃ i, stieltjesFeature (support a) (points i) ≠ 0) :
    IsSupportedGeneralizedEigenpair
      (supportGramMatrix mass support points)
      (massGramMatrix mass support points)
      (support a) v := by
  exact ⟨
    cauchy_dual_vector_ne_zero support points a v hdual,
    mass_gram_mulVec_ne_zero_of_dual
      mass support points a v hdual hmass hfeature,
    support_gram_eigenrelation_of_dual
      mass support points a v hdual⟩

#print axioms mass_support_kernel_pencil_factorization
#print axioms pencil_mulVec_at_support_of_dual
#print axioms support_is_generalized_eigenvalue_of_dual

end D5.S3.Weil.Pick.MassSupportKernelPencil

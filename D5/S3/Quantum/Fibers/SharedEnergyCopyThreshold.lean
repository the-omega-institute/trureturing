/- GID: D5/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   generality: I
   mirror-B: D5/B/S3/Quantum/Fibers/SharedEnergyCopyThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sparse three-level density matrices and their shared-energy relations. -/

import D5.S3.Quantum.Fibers.RealCopyConjugation
import D5.S3.Arith.Lattices.CofactorKernel
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold
open Matrix
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.RealCopyConjugation
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The sparse Hermitian family in the fixed energy basis. -/
def sparseMatrix (u : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/3, 0, (1/12) * star u;
     0, 1/3, 1/12;
     (1/12) * u, 1/12, 1/3]

private theorem sparse_hermitian (u : ℂ) : (sparseMatrix u).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sparseMatrix, conjTranspose_apply, star_mul]

private theorem sparse_trace (u : ℂ) : trace (sparseMatrix u) = 1 := by
  norm_num [sparseMatrix, trace, Fin.sum_univ_succ]

private theorem sparse_det_shift (u z : ℂ) (hu : u * star u = 1) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - sparseMatrix u).det =
      (z - 1/3) * ((z - 1/3)^2 - 2/144) := by
  simp only [sparseMatrix, Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.head_fin_const]
  norm_num
  linear_combination (-(z-1/3)/144) * hu

private theorem sparse_spectrum (u : ℂ) (hu : u * star u = 1) :
    spectrum ℂ (sparseMatrix u) =
      {1/3, 1/3 - (Real.sqrt 2 : ℂ)/12, 1/3 + (Real.sqrt 2 : ℂ)/12} := by
  have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det]
  have he : algebraMap ℂ (Matrix (Fin 3) (Fin 3) ℂ) z = z • 1 := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, Matrix.one_apply]
  rw [he, sparse_det_shift u z hu, isUnit_iff_ne_zero, not_not]
  have hf : (z - 1/3) * ((z - 1/3)^2 - 2/144) =
      (z - 1/3) * (z - (1/3 - (Real.sqrt 2 : ℂ)/12)) *
        (z - (1/3 + (Real.sqrt 2 : ℂ)/12)) := by
    linear_combination ((z - 1/3)/144) * hs
  rw [hf]
  simp only [mul_eq_zero, sub_eq_zero, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem sparse_posDef (u : ℂ) (hu : u * star u = 1) :
    (sparseMatrix u).PosDef := by
  have hH := sparse_hermitian u
  apply hH.posDef_iff_eigenvalues_pos.mpr
  intro i
  have he : (hH.eigenvalues i : ℂ) ∈ spectrum ℂ (sparseMatrix u) :=
    spectrum.algebraMap_mem ℂ (hH.eigenvalues_mem_spectrum_real i)
  rw [sparse_spectrum u hu] at he
  have hsmall : Real.sqrt 2 < 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rcases he with he | he | he
  · have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  · have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  · have hr := congrArg Complex.re he
    norm_num at hr
    nlinarith [Real.sqrt_nonneg 2]

/-- Every unit phase gives a literal positive definite trace-one matrix with the
same exact three-point spectrum. -/
theorem sparse_density_spectrum (u : ℂ) (hu : u * star u = 1) :
    (sparseMatrix u).PosDef ∧ trace (sparseMatrix u) = 1 ∧
      spectrum ℂ (sparseMatrix u) =
        {1/3, 1/3 - (Real.sqrt 2 : ℂ)/12, 1/3 + (Real.sqrt 2 : ℂ)/12} :=
  ⟨sparse_posDef u hu, sparse_trace u, sparse_spectrum u hu⟩

/-- Native normalized states, rather than independent coordinate tables. -/
def sparseState (u : ℂ) (hu : u * star u = 1) : DensityState (Fin 3) :=
  ⟨CStarMatrix.ofMatrix (sparseMatrix u),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (sparse_density_spectrum u hu).1.posSemidef.nonneg,
    (sparse_density_spectrum u hu).2.1⟩

end D5.S3.Quantum.Fibers.SharedEnergyCopyThreshold

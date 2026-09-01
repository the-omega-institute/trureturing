/- GID: D5/S3/Weil/Pick/HermitianKernelNegativeSquares
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/HermitianKernelNegativeSquares
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define finite negative squares of Hermitian kernels and realize index one. -/

import D5.S3.Weil.ZetaLinear.PoleCapacityRankOne
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom remains residual-open with empty `coverage_gids` and no
     formalization receipt. Repository searches for Hermitian kernels,
     negative squares, Pontryagin spaces, generalized Schur functions, and
     finite Gram inertia found no existing definition with both the uniform
     upper bound and attainment clauses. The adjacent Pick modules only prove
     positive-semidefinite Gram and finite channel-dimension statements.
   * `OfflineZeroCharacter` and `OfflineZeroGeometricMonodromy` concern Mellin
     characters and hyperbolic monodromy, not kernel inertia. The reusable D5
     hits are `RHLinalg.negIndex` and `pole_capacity_rank_one`, used below.
   * Pinned Mathlib supplies Hermitian eigenvalues, trace identities, and
     positive-semidefinite outer products, but no negative-squares kernel,
     Pontryagin-space, generalized-Schur, or Krein-Langer declaration. A
     public GitHub code-search attempt through the required credential broker
     was unavailable because its GitHub bindings were expired or pending. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Weil.Pick.HermitianKernelNegativeSquares

open D5.S3.Weil.ZetaLinear.PoleCapacityRankOne
open RHLinalg

/-- A complex Hermitian kernel, represented by its conjugate symmetry. -/
structure HermitianKernel (Point : Type*) where
  value : Point -> Point -> ℂ
  conj_symm : ∀ x y, star (value y x) = value x y

namespace HermitianKernel

/-- The Gram matrix obtained by sampling a Hermitian kernel at finitely many
points. Repetitions in the sampling family are permitted. -/
def gramMatrix {Point : Type*} (K : HermitianKernel Point)
    {n : ℕ} (points : Fin n -> Point) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => K.value (points i) (points j)

/-- Every finite Gram matrix of a Hermitian kernel is Hermitian. -/
theorem gramMatrix_isHermitian {Point : Type*} (K : HermitianKernel Point)
    {n : ℕ} (points : Fin n -> Point) :
    (K.gramMatrix points).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  exact K.conj_symm (points i) (points j)

end HermitianKernel

/-- A Hermitian kernel has exactly `kappa` negative squares when every finite
Gram matrix has at most `kappa` negative eigenvalues and some finite Gram
matrix attains that bound. -/
def HasNegativeSquares {Point : Type*} (K : HermitianKernel Point)
    (kappa : ℕ) : Prop :=
  (∀ (n : ℕ) (points : Fin n -> Point),
      negIndex (K.gramMatrix_isHermitian points) <= kappa) ∧
    ∃ (n : ℕ) (points : Fin n -> Point),
      negIndex (K.gramMatrix_isHermitian points) = kappa

/-- The constant negative kernel on one point. -/
def oneNegativeKernel : HermitianKernel Unit where
  value := fun _ _ => -1
  conj_symm := by simp

private theorem oneNegativeKernel_negIndex_le_one
    (n : ℕ) (points : Fin n -> Unit) :
    negIndex (oneNegativeKernel.gramMatrix_isHermitian points) <= 1 := by
  let p : Fin n -> ℂ := fun _ => 1
  have hUpdated :
      (oneNegativeKernel.gramMatrix points +
          (2 : ℝ) • Matrix.vecMulVec p (star p)).PosSemidef := by
    convert Matrix.posSemidef_vecMulVec_self_star p using 1
    ext i j
    simp [HermitianKernel.gramMatrix, oneNegativeKernel, p,
      Matrix.vecMulVec]
    norm_num
  exact (pole_capacity_rank_one
    (oneNegativeKernel.gramMatrix_isHermitian points) p).2 hUpdated

private theorem oneNegativeKernel_attains_one :
    ∃ (n : ℕ) (points : Fin n -> Unit),
      negIndex (oneNegativeKernel.gramMatrix_isHermitian points) = 1 := by
  let points : Fin 1 -> Unit := fun _ => ()
  let hGram := oneNegativeKernel.gramMatrix_isHermitian points
  have hEigenvalueZero : hGram.eigenvalues 0 = -1 := by
    have hTrace := hGram.trace_eq_sum_eigenvalues
    have hCast : ((-1 : ℝ) : ℂ) = (hGram.eigenvalues 0 : ℂ) := by
      simpa [hGram, HermitianKernel.gramMatrix, oneNegativeKernel,
        Matrix.trace_fin_one] using hTrace
    exact_mod_cast hCast.symm
  have hEigenvalue (i : Fin 1) : hGram.eigenvalues i = -1 := by
    simpa [Subsingleton.elim i 0] using hEigenvalueZero
  refine ⟨1, points, ?_⟩
  change negIndex hGram = 1
  simp [negIndex, hEigenvalue]

/-- The negative-squares definition is nonempty in the genuinely indefinite
case: the constant `-1` kernel has exactly one negative square. -/
theorem exists_hermitian_kernel_with_one_negative_square :
    ∃ K : HermitianKernel Unit, HasNegativeSquares K 1 := by
  refine ⟨oneNegativeKernel, ?_⟩
  exact ⟨oneNegativeKernel_negIndex_le_one,
    oneNegativeKernel_attains_one⟩

#print axioms exists_hermitian_kernel_with_one_negative_square

end D5.S3.Weil.Pick.HermitianKernelNegativeSquares

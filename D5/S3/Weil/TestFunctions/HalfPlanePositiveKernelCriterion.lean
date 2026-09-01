/- GID: D5/S3/Weil/TestFunctions/HalfPlanePositiveKernelCriterion
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/HalfPlanePositiveKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite Gram positivity yields Hermitian kernel bounds and an abstract RH criterion. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom is residual-open with empty `coverage_gids` and no formalization
     receipt. Exact D5 searches for positive-definite kernels, finite Gram
     positivity, and RH kernel criteria found no existing owner. The adjacent
     `LiCurvatureCriterion` treats Toeplitz moments, while
     `PositivityChartCollapse` supplies only a feature-Gram sufficient condition.
   * Pinned Mathlib supplies `Matrix.PosSemidef.isHermitian`,
     `Matrix.PosSemidef.det_nonneg`, `Matrix.det_fin_one`, `Matrix.det_fin_two`,
     and `Matrix.posSemidef_vecMulVec_self_star`; all are reused below. Its RKHS
     API has an infinite-matrix positivity notion, but no finite-sampling bundle
     with the two requested kernel witnesses.
   * Installed non-Mathlib Lake packages contain no matching positive-definite
     kernel or finite-Gram declaration. The xi/Hadamard bridge is therefore kept
     as the source criterion hypothesis instead of being redeclared or assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexConjugate ComplexOrder Matrix

namespace D5.S3.Weil.TestFunctions.HalfPlanePositiveKernelCriterion

/-- A complex kernel is positive definite when every finite sampled Gram matrix
is positive semidefinite. The sampling family may contain repetitions, and the
empty family is permitted. -/
def IsPosDefKernel {H : Type*} (kernel : H -> H -> ℂ) : Prop :=
  ∀ (N : ℕ) (points : Fin N -> H),
    (Matrix.of fun i j => kernel (points i) (points j)).PosSemidef

/-- Positivity of the one-point Gram matrix makes every diagonal value real and
nonnegative. -/
theorem isPosDefKernel_diagonal {H : Type*} {kernel : H -> H -> ℂ}
    (hKernel : IsPosDefKernel kernel) (x : H) :
    0 ≤ (kernel x x).re ∧ (kernel x x).im = 0 := by
  have hOne := (hKernel 1 fun _ => x).det_nonneg
  have hEntry : (0 : ℂ) ≤ kernel x x := by
    simpa [Matrix.det_fin_one] using hOne
  rcases Complex.nonneg_iff.mp hEntry with ⟨hRe, hIm⟩
  exact ⟨hRe, hIm.symm⟩

/-- Positivity of every two-point Gram matrix forces conjugate symmetry. -/
theorem isPosDefKernel_conj_symm {H : Type*} {kernel : H -> H -> ℂ}
    (hKernel : IsPosDefKernel kernel) (x y : H) :
    kernel y x = conj (kernel x y) := by
  let points : Fin 2 -> H := ![x, y]
  have hEntry := (hKernel 2 points).isHermitian.apply (1 : Fin 2) (0 : Fin 2)
  simpa [points, Complex.star_def] using hEntry.symm

/-- The determinant of the two-point Gram matrix gives the kernel
Cauchy--Schwarz inequality. -/
theorem isPosDefKernel_cauchy_schwarz {H : Type*} {kernel : H -> H -> ℂ}
    (hKernel : IsPosDefKernel kernel) (x y : H) :
    ‖kernel x y‖ ^ 2 ≤ (kernel x x).re * (kernel y y).re := by
  let points : Fin 2 -> H := ![x, y]
  have hDet := (hKernel 2 points).det_nonneg
  have hSymm := isPosDefKernel_conj_symm hKernel x y
  have hDiagX := isPosDefKernel_diagonal hKernel x
  have hDiagY := isPosDefKernel_diagonal hKernel y
  simp only [Matrix.det_fin_two, Matrix.of_apply] at hDet
  simp only [points, Matrix.cons_val_zero, Matrix.cons_val_one] at hDet
  rw [hSymm] at hDet
  have hDetRe := (Complex.nonneg_iff.mp hDet).1
  have hReal :
      0 ≤ (kernel x x).re * (kernel y y).re - ‖kernel x y‖ ^ 2 := by
    simpa [Complex.mul_re, ← Complex.ofReal_pow, hDiagX.2, hDiagY.2,
      Complex.mul_conj'] using hDetRe
  linarith

/-- The constant-one kernel is positive definite on every point type. -/
theorem constant_one_isPosDefKernel (H : Type*) :
    IsPosDefKernel (fun (_ _ : H) => 1) := by
  intro N points
  let ones : Fin N -> ℂ := fun _ => 1
  simpa [Matrix.vecMulVec, ones] using
    (Matrix.posSemidef_vecMulVec_self_star ones)

/-- On any type with two distinct points, the kernel with diagonal value one
and off-diagonal value two is not positive definite. Its sampled two-by-two
determinant is `1 - 4 = -3`. -/
theorem diagonal_one_off_diagonal_two_not_isPosDefKernel
    {H : Type*} [DecidableEq H] {x y : H} (hxy : x ≠ y) :
    ¬IsPosDefKernel (fun u v : H => if u = v then 1 else 2) := by
  intro hKernel
  let points : Fin 2 -> H := ![x, y]
  have hDet := (hKernel 2 points).det_nonneg
  norm_num [points, Matrix.det_fin_two, hxy, Ne.symm hxy,
    Complex.nonneg_iff] at hDet

/-- Abstract half-plane positive-kernel RH criterion. The equivalence itself is
the source's external xi/Hadamard assertion and is therefore an explicit
hypothesis. The reusable consequences of finite Gram positivity are proved
independently above for an arbitrary point type. -/
theorem half_plane_positive_kernel_rh_criterion
    {H : Type*} (RiemannHypothesis : Prop) (xiKernel : H -> H -> ℂ)
    (sourceCriterion : RiemannHypothesis ↔ IsPosDefKernel xiKernel) :
    RiemannHypothesis ↔ IsPosDefKernel xiKernel :=
  sourceCriterion

#print axioms isPosDefKernel_diagonal
#print axioms isPosDefKernel_conj_symm
#print axioms isPosDefKernel_cauchy_schwarz
#print axioms constant_one_isPosDefKernel
#print axioms diagonal_one_off_diagonal_two_not_isPosDefKernel
#print axioms half_plane_positive_kernel_rh_criterion

end D5.S3.Weil.TestFunctions.HalfPlanePositiveKernelCriterion

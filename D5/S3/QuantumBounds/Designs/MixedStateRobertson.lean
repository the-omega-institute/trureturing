/- GID: D5/S3/QuantumBounds/Designs/MixedStateRobertson
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/Designs/MixedStateRobertson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound mixed-state standard deviations by the expected commutator. -/

import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition

/- Library-search audit trail (2026-08-27):
   * The exact D5 pure-state hit `RobertsonSchrodinger.robertson_schrodinger`
     does not cover mixed density matrices. The canonical `DensityState` carrier
     is imported from `QuantumRelativeEntropyDefectComposition`.
   * The repository's matrix GNS family supplies the canonical positive square-root
     realization of the weighted operator semi-inner product; no new definition is made.
   * Pinned Mathlib has no packaged Robertson theorem. The proof directly applies
     `norm_inner_le_norm`, `Complex.abs_im_le_norm`, `Complex.sub_conj`, the matrix
     trace-cycle identities, and the continuous-functional-calculus square-root laws. -/

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace MatrixOrder
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.Designs.MixedStateRobertson

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition

variable {d : Type*} [Fintype d] [DecidableEq d]

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

omit [DecidableEq d] in
private theorem trace_mul_hermitian_real
    (X Y : Matrix d d ℂ) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Matrix.trace (X * Y) = ((Matrix.trace (X * Y)).re : ℂ) := by
  have hstar : starRingEnd ℂ (Matrix.trace (X * Y)) = Matrix.trace (X * Y) := by
    calc
      starRingEnd ℂ (Matrix.trace (X * Y)) = Matrix.trace ((X * Y)ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
      _ = Matrix.trace (Y * X) := by rw [Matrix.conjTranspose_mul, hX.eq, hY.eq]
      _ = Matrix.trace (X * Y) := Matrix.trace_mul_comm _ _
  have him := congrArg Complex.im hstar
  change (starRingEnd ℂ (Matrix.trace (X * Y))).im = _ at him
  rw [Complex.conj_im] at him
  apply Complex.ext
  · rfl
  · simpa using (show (Matrix.trace (X * Y)).im = 0 by linarith)

private theorem matrix_inner_eq_trace_conjTranspose_mul
    (X Y : Matrix d d ℂ) :
    inner ℂ X Y = Matrix.trace (Xᴴ * Y) := by
  change Matrix.trace (Y * 1 * Xᴴ) = Matrix.trace (Xᴴ * Y)
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

/-- For two Hermitian observables in a finite density state, the product of
their GNS standard deviations bounds half the magnitude of the expected commutator. -/
theorem mixed_state_robertson_uncertainty
    (rho : DensityState d) (A B : Matrix d d ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let rhoMatrix : Matrix d d ℂ := CStarMatrix.ofMatrixStarAlgEquiv.symm rho.1
    let stateRoot : Matrix d d ℂ := CFC.sqrt rhoMatrix
    let u := (A - Matrix.trace (rhoMatrix * A) • (1 : Matrix d d ℂ)) * stateRoot
    let v := (B - Matrix.trace (rhoMatrix * B) • (1 : Matrix d d ℂ)) * stateRoot
    ‖u‖ * ‖v‖ ≥
      (1 / 2 : ℝ) * ‖Matrix.trace (rhoMatrix * (A * B - B * A))‖ := by
  dsimp
  let rhoMatrix : Matrix d d ℂ := CStarMatrix.ofMatrixStarAlgEquiv.symm rho.1
  let stateRoot : Matrix d d ℂ := CFC.sqrt rhoMatrix
  have hRho : rhoMatrix.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.2.1
  have hRhoHerm : rhoMatrix.IsHermitian := hRho.isHermitian
  have hExpA := trace_mul_hermitian_real rhoMatrix A hRhoHerm hA
  have hExpB := trace_mul_hermitian_real rhoMatrix B hRhoHerm hB
  let Ac := A - Matrix.trace (rhoMatrix * A) • (1 : Matrix d d ℂ)
  let Bc := B - Matrix.trace (rhoMatrix * B) • (1 : Matrix d d ℂ)
  have hAc : Ac.IsHermitian := by
    change Acᴴ = Ac
    dsimp [Ac]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hA.eq,
      Matrix.conjTranspose_one, hExpA]
    simp
  have hBc : Bc.IsHermitian := by
    change Bcᴴ = Bc
    dsimp [Bc]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hB.eq,
      Matrix.conjTranspose_one, hExpB]
    simp
  let u := Ac * stateRoot
  let v := Bc * stateRoot
  have hSqrtSq : stateRoot * stateRoot = rhoMatrix := by
    exact CFC.sqrt_mul_sqrt_self rhoMatrix hRho.nonneg
  have hSqrtStar : stateRootᴴ = stateRoot := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg rhoMatrix).isSelfAdjoint.star_eq
  have hInner :
      inner ℂ u v = Matrix.trace (rhoMatrix * (Ac * Bc)) := by
    rw [matrix_inner_eq_trace_conjTranspose_mul]
    simp only [u, v, Matrix.conjTranspose_mul, hSqrtStar, hAc.eq]
    calc
      Matrix.trace ((stateRoot * Ac) * (Bc * stateRoot)) =
          Matrix.trace (stateRoot * (Ac * Bc) * stateRoot) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (stateRoot * stateRoot * (Ac * Bc)) :=
        Matrix.trace_mul_cycle stateRoot (Ac * Bc) stateRoot
      _ = Matrix.trace (rhoMatrix * (Ac * Bc)) := by rw [hSqrtSq]
  have hCenteredCommutator : Ac * Bc - Bc * Ac = A * B - B * A := by
    simp only [Ac, Bc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  have hReverse :
      starRingEnd ℂ (Matrix.trace (rhoMatrix * (Ac * Bc))) =
        Matrix.trace (rhoMatrix * (Bc * Ac)) := by
    calc
      starRingEnd ℂ (Matrix.trace (rhoMatrix * (Ac * Bc))) =
          Matrix.trace ((rhoMatrix * (Ac * Bc))ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
      _ = Matrix.trace ((Bc * Ac) * rhoMatrix) := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hRhoHerm.eq, hAc.eq, hBc.eq]
      _ = Matrix.trace (rhoMatrix * (Bc * Ac)) := Matrix.trace_mul_comm _ _
  have hComm :
      Matrix.trace (rhoMatrix * (A * B - B * A)) =
        inner ℂ u v - starRingEnd ℂ (inner ℂ u v) := by
    rw [hInner, hReverse]
    rw [← Matrix.trace_sub, ← Matrix.mul_sub, hCenteredCommutator]
  have hNormComm :
      ‖Matrix.trace (rhoMatrix * (A * B - B * A))‖ =
        2 * |(inner ℂ u v).im| := by
    rw [hComm]
    rw [Complex.sub_conj, norm_mul]
    simp
  have hIm : |(inner ℂ u v).im| ≤ ‖inner ℂ u v‖ :=
    Complex.abs_im_le_norm _
  have hCS : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm _ _
  dsimp [u, v, Ac, Bc] at hNormComm hIm hCS ⊢
  rw [hNormComm]
  nlinarith

#print axioms mixed_state_robertson_uncertainty

end D5.S3.QuantumBounds.Designs.MixedStateRobertson

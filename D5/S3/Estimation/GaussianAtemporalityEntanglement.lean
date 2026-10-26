/- GID: D5/S3/Estimation/GaussianAtemporalityEntanglement
   generality: I
   mirror-B: D5/B/S3/Estimation/GaussianAtemporalityEntanglement
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: PPT two-mode Gaussian covariance matrices are temporally compatible both ways. -/

/-
admission_basis: open-problem-resolution (#19029; Proved)
escape_witness: none
Direct frozen dependencies:
D5/S3/Estimation/GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
statement_id: sha256:410391e348afb0d9876bdf2548ca1782f14191e2ac259dd3c3d81d1876de06a4.
D5/S3/Quantum/Thermal/PositiveOneModeWilliamson.physicalJ2
statement_id: sha256:a3c76f635d3fda80d5e5b8d7c1b2a552486e81143ead947af1e2bb7de3369327.
D5/S3/Quantum/FiniteDimensional.qubitX
statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7.
D5/S3/Quantum/FiniteDimensional.qubitZ
statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c.
D5/S3/Quantum/FiniteDimensional.qubit_weyl_star
statement_id: sha256:be07b0533dfdb8741136a43d8272fd7a664770fb9b4a851805c5db573532362d.
D5/S3/Quantum/FiniteDimensional.QubitMatrix
statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30.
proof_shape: realMap_mul: bind-only; consumers: ppt_signed, forward_congruence.
proof_shape: realMap_sub: bind-only; consumer: forward_congruence.
proof_shape: realMap_conjTranspose: bind-only; consumers: ppt_signed, forward_congruence.
proof_shape: local_posDef: bind-only; consumer: physical_blocks_posDef.
proof_shape: physical_blocks_posDef: bind-only; consumer: ppt_both_directions.
proof_shape: ppt_signed: bind-only; consumer: ppt_both_directions.
proof_shape: psd_entrywise_conj: bind-only; consumer: ppt_both_directions.
proof_shape: forward_congruence: bind-only; consumer: ppt_both_directions.
proof_shape: ppt_both_directions: bind-only; consumer: result.
proof_shape: result: bind-only; settling result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19151
The real-to-complex convention is inlined as Matrix.map Complex.ofReal,
not redeclared: DiscreteSteinCompressionStability.complexMatrix owns its
finite-index form; these proofs use the underlying generic Mathlib map.
The reverse expression is forwardX VB VA Cᵀ, inlined rather than aliased.
The symplectic form is the existing physicalJ2 = !![0, 1; -1, 0].
The one-mode covariance condition is normalized to the coordinates of
GeneralDyneSteadyStateOptimality.physical_forward, which supplies
positive definiteness and det A ≥ 1.
The momentum-flip square and symplectic sign change use qubit_weyl_star
through real-to-complex entry correspondences.
The public physical_forward owner has an unfinished escape audit under #19151.
The source constructions use Matrix.fromBlocks, Matrix.map, Matrix.IsDiag,
Matrix.diagonal and the nonsingular inverse directly. The source expressions
are those in #19029; no independent separability theorem is asserted.
-/


import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Measurements.GeneralDyneSteadyStateOptimality

/-! Binding conventions for M. Song et al., "Gaussian Atemporality: When Gaussian Quantum Correlations Imply
Common Cause", arXiv:2508.11804v2, Sections II.2 and III.1–III.4, Eqs. (2) and (5)–(8); units ħ = 2.
A two-mode covariance matrix is `V = [[V_A, C], [Cᵀ, V_B]]` in the quadrature order `(q_A, p_A, q_B, p_B)`. -/

noncomputable section
namespace D5.S3.Estimation.GaussianAtemporalityEntanglement

open Matrix
open D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
open scoped ComplexOrder

/-- Eq. (2): the space-time covariance matrix `V_AB = [[V_A, C], [Cᵀ, V_B]]`. -/
def covariance (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fromBlocks VA C Cᵀ VB

/-- Definition 1: standard form, with locally diagonal covariance matrices `V_A` and `V_B`. -/
def IsStandardForm (VA VB : Matrix (Fin 2) (Fin 2) ℝ) : Prop := VA.IsDiag ∧ VB.IsDiag

/-- A spatially distributed two-mode Gaussian state: the uncertainty principle `V_AB + i(Ω ⊕ Ω) ≥ 0`. -/
def IsSpatiallyPhysical (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ((covariance VA VB C).map Complex.ofReal +
    Complex.I • (fromBlocks physicalJ2 0 0 physicalJ2).map Complex.ofReal).PosSemidef

/-- Eqs. (7)–(8): the forward atemporality matrix `X(T, N) = N + iΩ − i T Ω Tᵀ` with `T = Cᵀ V_A⁻¹` and
`N = V_B − Cᵀ V_A⁻¹ C`. -/
def forwardX (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let T := Cᵀ * VA⁻¹
  let N := VB - Cᵀ * VA⁻¹ * C
  N.map Complex.ofReal + Complex.I • physicalJ2.map Complex.ofReal -
    Complex.I • (T * physicalJ2 * Tᵀ).map Complex.ofReal

/-- Section III.2: `V_AB` is Gaussian atemporal if it is Gaussian-atemporal in both temporal directions, that is,
both atemporality matrices fail to be positive semidefinite. -/
def IsGaussianAtemporal (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ (forwardX VA VB C).PosSemidef ∧ ¬ (forwardX VB VA Cᵀ).PosSemidef

/-- The partial transpose on mode `A` flips `p_A`: `Λ V Λ` with `Λ = diag(1, −1, 1, 1)`. -/
def partialTransposeA (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  let Λ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fromBlocks (diagonal ![1, -1]) 0 0 1
  Λ * covariance VA VB C * Λ

/-- The PPT criterion (Peres; Horodecki), the source's entanglement test for two-mode Gaussian states:
the state is entangled iff its partially transposed covariance matrix violates the uncertainty principle. -/
def IsEntangled (VA VB C : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ¬ ((partialTransposeA VA VB C).map Complex.ofReal + Complex.I • (fromBlocks physicalJ2 0 0 physicalJ2).map Complex.ofReal).PosSemidef

/-- Section III.4: "From Fig. 3, Gaussian-atemporality appears to imply entanglement." -/
def claim : Prop :=
  ∀ VA VB C : Matrix (Fin 2) (Fin 2) ℝ,
    IsStandardForm VA VB → IsSpatiallyPhysical VA VB C → IsGaussianAtemporal VA VB C → IsEntangled VA VB C

end D5.S3.Estimation.GaussianAtemporalityEntanglement

namespace D5.S3.Estimation.GaussianAtemporalityEntanglement
open Matrix
open D5.S3.Quantum.Thermal.PositiveOneModeWilliamson
open scoped ComplexOrder

@[simp] private theorem realMap_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℝ) (B : Matrix n p ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

@[simp] private theorem realMap_sub {m n : Type*} (A B : Matrix m n ℝ) :
    (A - B).map Complex.ofReal = A.map Complex.ofReal - B.map Complex.ofReal :=
  Matrix.map_sub Complex.ofReal Complex.ofReal_sub A B
@[simp] private theorem realMap_conjTranspose {m n : Type*} (A : Matrix m n ℝ) :
    (A.map Complex.ofReal)ᴴ = (Aᵀ).map Complex.ofReal  := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.conjTranspose_map (A := A) Complex.ofReal (fun _ => by simp)).symm
private theorem local_posDef (A : Matrix (Fin 2) (Fin 2) ℝ)
    (h : (A.map Complex.ofReal + Complex.I • physicalJ2.map Complex.ofReal).PosSemidef) : A.PosDef := by
  have hsym : A.IsHermitian := by
    ext i j
    have he := congrArg Complex.re (h.1.apply i j)
    simpa using he
  have hcov :
      D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov
        (m := 1) A := by
    constructor
    · exact hsym.isSymm
    · convert h using 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [D5.S3.Estimation.GaussianThermometryJointMeasurementRefutation.IsGaussianMeasurementCov,
          Matrix.J, Matrix.fromBlocks, Matrix.submatrix, Fin.divNat,
          Matrix.one_apply, physicalJ2, sub_eq_add_neg]
  exact (D5.S3.Quantum.Measurements.GeneralDyneSteadyStateOptimality.physical_forward A hcov).1


private theorem physical_blocks_posDef (VA VB C : Matrix (Fin 2) (Fin 2) ℝ)
    (h : IsSpatiallyPhysical VA VB C) : VA.PosDef ∧ VB.PosDef := by
  constructor
  · apply local_posDef
    exact h.submatrix Sum.inl
  · apply local_posDef
    exact h.submatrix Sum.inr

private theorem ppt_signed (VA VB C : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ((partialTransposeA VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks physicalJ2 0 0 physicalJ2).map Complex.ofReal).PosSemidef) :
    ((covariance VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks (-physicalJ2) 0 0 physicalJ2).map Complex.ofReal).PosSemidef := by
  let D : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, -1]
  let E : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := fromBlocks D 0 0 1
  have hD : D.map Complex.ofReal = D5.S3.Quantum.FiniteDimensional.qubitZ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, D5.S3.Quantum.FiniteDimensional.qubitZ]
  have hDD : D * D = 1 := by
    apply Matrix.map_injective (f := Complex.ofReal) Complex.ofReal_injective
    change (D * D).map Complex.ofReal =
      (1 : Matrix (Fin 2) (Fin 2) ℝ).map Complex.ofReal
    rw [realMap_mul, hD]
    change D5.S3.Quantum.FiniteDimensional.qubitZ *
      D5.S3.Quantum.FiniteDimensional.qubitZ =
        Complex.ofRealHom.mapMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ)
    rw [map_one]
    simpa only [pow_two] using D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2
  have hJ : physicalJ2.map Complex.ofReal =
      D5.S3.Quantum.FiniteDimensional.qubitZ * D5.S3.Quantum.FiniteDimensional.qubitX := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [physicalJ2, D5.S3.Quantum.FiniteDimensional.qubitZ,
        D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.mul_apply, Fin.sum_univ_two]
  have hDO : D * physicalJ2 * D = -physicalJ2 := by
    apply Matrix.map_injective (f := Complex.ofReal) Complex.ofReal_injective
    change Complex.ofRealHom.mapMatrix (D * physicalJ2 * D) =
      Complex.ofRealHom.mapMatrix (-physicalJ2)
    rw [map_mul, map_mul, map_neg]
    change D.map Complex.ofReal * physicalJ2.map Complex.ofReal * D.map Complex.ofReal =
      -physicalJ2.map Complex.ofReal
    rw [hD, hJ]
    rw [← Matrix.mul_assoc, ← pow_two,
      D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.2.2.2.2, Matrix.one_mul,
      D5.S3.Quantum.FiniteDimensional.qubit_weyl_star.1, neg_neg]
  have hEE : E * E = 1 := by
    simp [E, fromBlocks_multiply, hDD, fromBlocks_one]
  have hET : Eᵀ = E := by
    simp [E, D, fromBlocks_transpose]
  have hEO : E * fromBlocks physicalJ2 0 0 physicalJ2 * E =
      fromBlocks (-physicalJ2) 0 0 physicalJ2 := by
    simp [E, fromBlocks_multiply, hDO]
  have heq : E.map Complex.ofReal * ((partialTransposeA VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks physicalJ2 0 0 physicalJ2).map Complex.ofReal) * (E.map Complex.ofReal)ᴴ =
      (covariance VA VB C).map Complex.ofReal + Complex.I • (fromBlocks (-physicalJ2) 0 0 physicalJ2).map Complex.ofReal := by
    rw [realMap_conjTranspose, hET]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      ← realMap_mul]
    change (E * (E * covariance VA VB C * E) * E).map Complex.ofReal +
      Complex.I • (E * fromBlocks physicalJ2 0 0 physicalJ2 * E).map Complex.ofReal = _
    rw [show E * (E * covariance VA VB C * E) * E = covariance VA VB C by
      simp only [← Matrix.mul_assoc, hEE, Matrix.one_mul]
      rw [Matrix.mul_assoc, hEE, Matrix.mul_one], hEO]
  rw [← heq]
  exact h.mul_mul_conjTranspose_same (E.map Complex.ofReal)

private theorem psd_entrywise_conj {n : Type*} (H : Matrix n n ℂ) (h : H.PosSemidef) :
    (H.map star).PosSemidef := by
  convert h.transpose using 1
  ext i j
  exact h.1.apply j i

private theorem forward_congruence (VA VB C : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : IsUnit VA.det) :
    let T := Cᵀ * VA⁻¹
    let K := fromCols (-T) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    K.map Complex.ofReal * ((covariance VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks (-physicalJ2) 0 0 physicalJ2).map Complex.ofReal) * (K.map Complex.ofReal)ᴴ = forwardX VA VB C := by
  dsimp only
  let T := Cᵀ * VA⁻¹
  let K := fromCols (-T) (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hTA : T * VA = Cᵀ := by
    exact Matrix.nonsing_inv_mul_cancel_right VA Cᵀ hA
  have hKV : K * covariance VA VB C * Kᵀ = VB - Cᵀ * VA⁻¹ * C := by
    simp only [K, covariance, transpose_fromCols, transpose_neg, transpose_one,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows, neg_mul, mul_neg, one_mul, mul_one]
    rw [hTA]
    simp [T, sub_eq_add_neg, add_comm]
  have hKO : K * fromBlocks (-physicalJ2) 0 0 physicalJ2 * Kᵀ = physicalJ2 - T * physicalJ2 * Tᵀ := by
    simp [K, transpose_fromCols, fromCols_mul_fromBlocks, fromCols_mul_fromRows,
      sub_eq_add_neg]
    abel
  change K.map Complex.ofReal * _ * (K.map Complex.ofReal)ᴴ = _
  rw [realMap_conjTranspose]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← realMap_mul, hKV, hKO]
  simp [forwardX, T, smul_sub]
  abel


private theorem ppt_both_directions (VA VB C : Matrix (Fin 2) (Fin 2) ℝ)
    (hp : IsSpatiallyPhysical VA VB C)
    (hP : ((partialTransposeA VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks physicalJ2 0 0 physicalJ2).map Complex.ofReal).PosSemidef) :
    (forwardX VA VB C).PosSemidef ∧ (forwardX VB VA Cᵀ).PosSemidef := by
  have hab := physical_blocks_posDef VA VB C hp
  have hA : IsUnit VA.det := (Matrix.isUnit_iff_isUnit_det VA).mp hab.1.isUnit
  have hB : IsUnit VB.det := (Matrix.isUnit_iff_isUnit_det VB).mp hab.2.isUnit
  have hH := ppt_signed VA VB C hP
  have hbar : ((covariance VA VB C).map Complex.ofReal +
      Complex.I • (fromBlocks physicalJ2 0 0 (-physicalJ2)).map Complex.ofReal).PosSemidef := by
    convert psd_entrywise_conj _ hH using 1
    ext (i | i) (j | j) <;>
      simp [Matrix.map_apply, smul_eq_mul]
  have hswap : ((covariance VB VA Cᵀ).map Complex.ofReal +
      Complex.I • (fromBlocks (-physicalJ2) 0 0 physicalJ2).map Complex.ofReal).PosSemidef := by
    convert hbar.submatrix Sum.swap using 1
    ext (i | i) (j | j) <;> rfl
  constructor
  · rw [← forward_congruence VA VB C hA]
    exact hH.mul_mul_conjTranspose_same _
  · rw [← forward_congruence VB VA Cᵀ hB]
    exact hswap.mul_mul_conjTranspose_same _

theorem result : claim := by
  intro VA VB C _ hp ha hP
  exact ha.1 (ppt_both_directions VA VB C hp hP).1

end D5.S3.Estimation.GaussianAtemporalityEntanglement

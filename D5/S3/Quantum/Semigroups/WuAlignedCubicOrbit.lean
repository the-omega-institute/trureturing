/- GID: D5/S3/Quantum/Semigroups/WuAlignedCubicOrbit
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuAlignedCubicOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Directed mixed traces and Wu's cubic inequality under exterior odd-sector rotations. -/

import D5.S3.Quantum.Semigroups.WuPhysicalHighHigh
import D5.S3.Quantum.Semigroups.WuParityOrbit
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Two-mode CAR trace interpolation and the cubic Wu source inequality for aligned fibers.
The odd basis is (01, 10), and the complex even unitary acts on (00, 11).
A physical rotation of the odd basis acts by its determinant on the filled state. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit

section MixedTraces

open Matrix Kronecker
open scoped BigOperators Matrix

open WuPhysicalHighHigh (Occupation Mat phi psi)
open TwistedTwoModeOUComparison (modeJump)
open private jump_zero jump_one from D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

abbrev Block := Matrix (Fin 2) (Fin 2) ℂ

/-- The two even, odd and cross entries in the common singular coordinates.
For a real function of the original matrix these are the entries of its two real
symmetric coupled blocks. The cross entries may have either sign. -/
structure AlignedData where
  even : Fin 2 → ℝ
  odd : Fin 2 → ℝ
  cross : Fin 2 → ℝ

/-- The even-to-even block in the physical frame. -/
private def evenBlock (U : Block) (a : Fin 2 → ℝ) : Block :=
  U * diagonal (fun i => (a i : ℂ)) * Uᴴ

/-- The even-row, odd-column block in the physical frame. -/
private def crossBlock (U : Block) (k : Fin 2 → ℝ) : Block :=
  U * diagonal (fun i => (k i : ℂ))

private def parityMatrix (A B : Block) (c : Fin 2 → ℝ) : Mat :=
  Matrix.of fun i j =>
    if i.1 = i.2 then
      if j.1 = j.2 then A i.1 j.1 else B i.1 j.1
    else
      if j.1 = j.2 then star (B j.1 i.1)
      else (diagonal (fun k => (c k : ℂ)) : Block) i.1 j.1

/-- In parity order this has blocks `U diag(a) Uᴴ`, `U diag(k)` and `diag(c)`,
with the adjoint cross block below. The result is indexed by physical occupations. -/
def orbitMatrix (U : Block) (d : AlignedData) : Mat :=
  parityMatrix (evenBlock U d.even) (crossBlock U d.cross) d.odd

private def rowDet (u v : Fin 2 → ℂ) : ℂ := u 0 * v 1 - u 1 * v 0

/-- Multiply the cofactor formula for the inverse by the determinant. -/
private theorem unitary_diagonal_products (U : Block) (hU : Uᴴ * U = 1) :
    U 0 0 * U 1 1 = U.det * (Complex.normSq (U 0 0) : ℂ) ∧
    -(U 0 1 * U 1 0) = U.det * ((1 - Complex.normSq (U 0 0) : ℝ) : ℂ) := by
  have hadj : U.adjugate = U.det • Uᴴ := calc
    U.adjugate = Uᴴ * (U * U.adjugate) := by
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = U.det • Uᴴ := by rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  have h11 : U 1 1 = U.det * star (U 0 0) := by
    simpa [Matrix.adjugate_fin_two, Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul]
      using congrArg (fun V : Block => V 0 0) hadj
  have hdiag : U 0 0 * U 1 1 = U.det * (Complex.normSq (U 0 0) : ℂ) := calc
    U 0 0 * U 1 1 = U.det * (U 0 0 * star (U 0 0)) := by rw [h11]; ring
    _ = _ := by rw [Complex.star_def, Complex.mul_conj]
  refine ⟨hdiag, ?_⟩
  calc
    -(U 0 1 * U 1 0) = U.det - U 0 0 * U 1 1 := by rw [Matrix.det_fin_two]; ring
    _ = _ := by rw [hdiag, Complex.ofReal_sub, Complex.ofReal_one]; ring

private theorem row_norm_sum (U : Block) (hU : U * Uᴴ = 1) (i : Fin 2) :
    Complex.normSq (U i 0) + Complex.normSq (U i 1) = 1 := by
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.star_def, Complex.mul_conj, Complex.add_re, Complex.ofReal_re,
    Matrix.one_apply_eq, Complex.one_re]
    using congrArg (fun V : Block => (V i i).re) hU

private theorem norm_weights (U : Block) (hU : Uᴴ * U = 1) :
    let p := Complex.normSq (U 0 0)
    Complex.normSq (U 0 1) = 1 - p ∧
    Complex.normSq (U 1 0) = 1 - p ∧ Complex.normSq (U 1 1) = p := by
  have hrow : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hr0 := row_norm_sum U hrow 0
  have hr1 := row_norm_sum U hrow 1
  have hc0 : Complex.normSq (U 0 0) + Complex.normSq (U 1 0) = 1 := by
    have hcol : Uᴴ * (Uᴴ)ᴴ = 1 := by rwa [Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
      using row_norm_sum Uᴴ hcol 0
  dsimp only
  constructor
  · linarith only [hr0]
  constructor
  · linarith only [hc0]
  · linarith only [hr1, hc0]

/-- Both physical even diagonals are affine in the same real weight. -/
private theorem even_diagonal_moments (U : Block) (hU : Uᴴ * U = 1) (a : Fin 2 → ℝ) :
    let p := Complex.normSq (U 0 0)
    evenBlock U a 0 0 = ((p * a 0 + (1 - p) * a 1 : ℝ) : ℂ) ∧
    evenBlock U a 1 1 = ((p * a 1 + (1 - p) * a 0 : ℝ) : ℂ) := by
  have entry (i : Fin 2) : evenBlock U a i i =
      ∑ j : Fin 2, ((Complex.normSq (U i j) * a j : ℝ) : ℂ) := by
    simp only [evenBlock, Matrix.mul_apply (N := Uᴴ), Matrix.mul_diagonal,
      Matrix.conjTranspose_apply, Complex.star_def]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_right_comm, Complex.mul_conj, Complex.ofReal_mul]
  obtain ⟨h01, h10, h11⟩ := norm_weights U hU
  dsimp only
  constructor
  · rw [entry 0, Fin.sum_univ_two, h01, Complex.ofReal_add]
  · rw [entry 1, Fin.sum_univ_two, h10, h11, Complex.ofReal_add, add_comm]

private theorem cross_rowDet (U : Block) (hU : Uᴴ * U = 1) (k l : Fin 2 → ℝ) :
    rowDet (crossBlock U k 0) (crossBlock U l 1) =
      U.det * ((Complex.normSq (U 0 0) * (k 0 * l 1) +
        (1 - Complex.normSq (U 0 0)) * (k 1 * l 0) : ℝ) : ℂ) := by
  obtain ⟨hd, ha⟩ := unitary_diagonal_products U hU
  calc
    _ = (U 0 0 * U 1 1) * (k 0 : ℂ) * (l 1 : ℂ) +
        (-(U 0 1 * U 1 0)) * (k 1 : ℂ) * (l 0 : ℂ) := by
      simp only [rowDet, crossBlock, Matrix.mul_diagonal]
      ring
    _ = _ := by
      rw [hd, ha]
      push_cast
      ring

set_option maxHeartbeats 2000000 in
-- Expanding both signed jump sandwiches and the trace into entries needs extra heartbeats.
private theorem trace_mul_phi_entries (M N : Mat) :
    (N * phi M).trace =
      N (0, 0) (0, 0) * M (1, 0) (1, 0) + N (0, 1) (0, 1) * M (1, 1) (1, 1) +
      N (0, 0) (0, 1) * M (1, 1) (1, 0) + N (0, 1) (0, 0) * M (1, 0) (1, 1) +
      N (0, 0) (0, 0) * M (0, 1) (0, 1) + N (1, 0) (1, 0) * M (1, 1) (1, 1) -
      N (0, 0) (1, 0) * M (1, 1) (0, 1) - N (1, 0) (0, 0) * M (0, 1) (1, 1) := by
  norm_num [phi, jump_zero, jump_one, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private theorem trace_psi_eq_trace_phi_swap (M N : Mat) :
    (N * psi M).trace = (M * phi N).trace := by
  have cycle (J : Mat) : (N * (Jᴴ * M * J)).trace = (M * (J * N * Jᴴ)).trace := by
    simpa only [← Matrix.mul_assoc] using Matrix.trace_mul_comm (N * Jᴴ) (M * J)
  simp only [phi, psi, Fin.sum_univ_two, Matrix.mul_add, Matrix.trace_add,
    cycle (modeJump 0), cycle (modeJump 1)]

private theorem trace_phi_of_blocks (A B E F : Block) (c d : Fin 2 → ℝ) :
    (parityMatrix E F d * phi (parityMatrix A B c)).trace =
      E 0 0 * ((c 0 + c 1 : ℝ) : ℂ) + ((d 0 + d 1 : ℝ) : ℂ) * A 1 1 +
        rowDet (F 0) (B 1) + star (rowDet (F 0) (B 1)) := by
  rw [trace_mul_phi_entries]
  norm_num [parityMatrix, Matrix.of_apply, Matrix.diagonal_apply, rowDet,
    Complex.star_def, Complex.ofReal_add, map_mul, map_sub]
  ring

private def loweringValue (p : ℝ) (z : ℂ) (M N : AlignedData) : ℝ :=
  (p * N.even 0 + (1 - p) * N.even 1) * (M.odd 0 + M.odd 1) +
  (N.odd 0 + N.odd 1) * (p * M.even 1 + (1 - p) * M.even 0) +
  2 * (z * ((p * (N.cross 0 * M.cross 1) + (1 - p) * (N.cross 1 * M.cross 0) : ℝ) : ℂ)).re

private theorem trace_phi_eval (U : Block) (hU : Uᴴ * U = 1) (M N : AlignedData) :
    (orbitMatrix U N * phi (orbitMatrix U M)).trace.re =
      loweringValue (Complex.normSq (U 0 0)) U.det M N := by
  simp only [orbitMatrix]
  rw [trace_phi_of_blocks, (even_diagonal_moments U hU N.even).1,
    (even_diagonal_moments U hU M.even).2, cross_rowDet U hU N.cross M.cross]
  simp only [loweringValue, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re,
    Complex.star_def, Complex.conj_re]
  ring

private theorem det_phase (U : Block) (hU : Uᴴ * U = 1) : star U.det * U.det = 1 := by
  simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one]
    using congrArg (fun V : Block => V.det) hU

/-- The diagonal endpoint at determinant `z`. -/
def diagonalFrame (z : ℂ) : Block := !![1,0;0,z]

/-- The antidiagonal endpoint at determinant `z`. -/
def antidiagonalFrame (z : ℂ) : Block := !![0,-z;1,0]

/-- Both endpoints are unitary at a unit determinant phase and attain weights one and zero. -/
private theorem endpoint_frames (z : ℂ) (hz : star z * z = 1) :
    (diagonalFrame z)ᴴ * diagonalFrame z = 1 ∧ (diagonalFrame z).det = z ∧
    Complex.normSq (diagonalFrame z 0 0) = 1 ∧
    (antidiagonalFrame z)ᴴ * antidiagonalFrame z = 1 ∧ (antidiagonalFrame z).det = z ∧
    Complex.normSq (antidiagonalFrame z 0 0) = 0 := by
  have hz' : (starRingEnd ℂ) z * z = 1 := hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonalFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fin.sum_univ_two, hz']
  · norm_num [diagonalFrame, Matrix.det_fin_two]
  · norm_num [diagonalFrame, Complex.normSq_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [antidiagonalFrame, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.one_apply, Fin.sum_univ_two, star_neg, hz']
  · norm_num [antidiagonalFrame, Matrix.det_fin_two]
  · norm_num [antidiagonalFrame, Complex.normSq_apply]

/-- The diagonal endpoint preserves the first occupation and the antidiagonal
endpoint preserves the second occupation. -/
private theorem endpoint_occupation_blocks (z : ℂ) (d : AlignedData) :
    (∀ i j : Occupation, i.1 ≠ j.1 → orbitMatrix (diagonalFrame z) d i j = 0) ∧
    (∀ i j : Occupation, i.2 ≠ j.2 → orbitMatrix (antidiagonalFrame z) d i j = 0) := by
  constructor <;> rintro ⟨i, j⟩ ⟨k, l⟩ h <;>
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num at h <;>
    norm_num [orbitMatrix, parityMatrix, Matrix.of_apply, evenBlock, crossBlock,
      diagonalFrame, antidiagonalFrame, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vecMul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- At fixed determinant the literal lowering and raising trace pairings each equal the
same affine average of their values at the physical diagonal and antidiagonal endpoints.
`M` and `N` may be the data for distinct real functions of the original coupled blocks. -/
private theorem directed_mixed_traces_in_frame (U : Block) (hU : Uᴴ * U = 1) (M N : AlignedData) :
    let p := Complex.normSq (U 0 0)
    let D := diagonalFrame U.det
    let S := antidiagonalFrame U.det
    0 ≤ p ∧ p ≤ 1 ∧
    (orbitMatrix U N * phi (orbitMatrix U M)).trace.re =
      p * (orbitMatrix D N * phi (orbitMatrix D M)).trace.re +
      (1 - p) * (orbitMatrix S N * phi (orbitMatrix S M)).trace.re ∧
    (orbitMatrix U N * psi (orbitMatrix U M)).trace.re =
      p * (orbitMatrix D N * psi (orbitMatrix D M)).trace.re +
      (1 - p) * (orbitMatrix S N * psi (orbitMatrix S M)).trace.re := by
  obtain ⟨hD, hDdet, hDnorm, hS, hSdet, hSnorm⟩ := endpoint_frames U.det (det_phase U hU)
  have lower (m n : AlignedData) :
      (orbitMatrix U n * phi (orbitMatrix U m)).trace.re =
        Complex.normSq (U 0 0) *
          (orbitMatrix (diagonalFrame U.det) n *
            phi (orbitMatrix (diagonalFrame U.det) m)).trace.re +
        (1 - Complex.normSq (U 0 0)) *
          (orbitMatrix (antidiagonalFrame U.det) n *
            phi (orbitMatrix (antidiagonalFrame U.det) m)).trace.re := by
    rw [trace_phi_eval U hU, trace_phi_eval _ hD, trace_phi_eval _ hS,
      hDdet, hDnorm, hSdet, hSnorm]
    simp only [loweringValue, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  dsimp only
  refine ⟨Complex.normSq_nonneg _, ?_, lower M N, ?_⟩
  · linarith only [(norm_weights U hU).1, Complex.normSq_nonneg (U 0 1)]
  · simpa only [trace_psi_eq_trace_phi_swap] using lower N M

end MixedTraces

section CubicInequality

open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.L2Operator

open WuCubicOperatorBridge
  (D G GInv Mat Occupation dissipator generator operator_trace_modular_identity)
open WuPhysicalHighHigh (parity phi psi)
open TwistedTwoModeOUComparison (modeJump)
open WuRepeatedMiddleCubic (alpha)
open private gibbsLow gibbsHigh jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private GInv_mul_G G_mul_GInv from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private occupationBlocks occupationBlocksHom occupationBlocks_apply occupationBlocks_trace from
  D5.S3.Quantum.Semigroups.WuCubicConditionalTensorization
open private xorBit parityIndex parityBlocksHom parityBlocks_apply logGibbs logGibbs_matrix
  trace_anticommutator jump_projections energy from D5.S3.Quantum.Semigroups.WuParityOrbit

/-- Coupled block `i` uses physical even vector `i` followed by physical odd vector `i`.
Its entries are real, including the common cross entry. -/
def pairedBlock (d : AlignedData) (i : Fin 2) : Block :=
  !![(d.even i : ℂ), (d.cross i : ℂ); (d.cross i : ℂ), (d.odd i : ℂ)]

private theorem pairedBlock_hermitian (d : AlignedData) (i : Fin 2) :
    (pairedBlock d i).IsHermitian := by
  change (pairedBlock d i)ᴴ = pairedBlock d i
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [pairedBlock, Matrix.conjTranspose_apply]

private def coupledIndex : Occupation ≃ Occupation :=
  parityIndex.symm.trans (Equiv.prodComm (Fin 2) (Fin 2))

private def coupledHom : (Fin 2 → Block) →⋆ₐ[ℂ] Mat where
  __ := (Matrix.reindexAlgEquiv ℂ ℂ coupledIndex.symm).toAlgHom.comp
    occupationBlocksHom.toAlgHom
  map_star' _ := by
    change (occupationBlocksHom (star _)).submatrix coupledIndex coupledIndex = _
    rw [map_star]
    rfl

private theorem coupled_apply (C : Fin 2 → Block) (i j k l : Fin 2) :
    coupledHom C (i,j) (k,l) = if i = k then C i (xorBit i j) (xorBit k l) else 0 :=
  occupationBlocks_apply _ _ _ _ _

private theorem coupled_trace (C : Fin 2 → Block) :
    (coupledHom C).trace = ∑ i, (C i).trace := by
  change ((occupationBlocks C).submatrix coupledIndex coupledIndex).trace = _
  rw [← occupationBlocks_trace]
  exact coupledIndex.sum_comp (fun i => occupationBlocks C i i)

private def evenRotation (U : Block) : Mat := WuParityOrbit.parityBlocks ![U,1]

private def evenUnitary (U : Block) (hU : Uᴴ * U = 1) : unitary Mat :=
  ⟨evenRotation U, by
    have h : star (evenRotation U) * evenRotation U = 1 := by
      change star (parityBlocksHom ![U,1]) * parityBlocksHom ![U,1] = 1
      rw [← map_star, ← map_mul, ← map_one parityBlocksHom]
      congr 1
      funext i
      fin_cases i
      · exact hU
      · simp
    exact Unitary.mem_iff.mpr ⟨h, mul_eq_one_comm.mp h⟩⟩

private def pairedHom (U : Block) (hU : Uᴴ * U = 1) : (Fin 2 → Block) →⋆ₐ[ℂ] Mat :=
  (Unitary.conjStarAlgAut ℂ Mat (evenUnitary U hU)).toStarAlgHom.comp coupledHom

private theorem pairedHom_apply (U : Block) (hU : Uᴴ * U = 1) (C : Fin 2 → Block) :
    pairedHom U hU C = evenRotation U * coupledHom C * (evenRotation U)ᴴ := rfl

set_option maxHeartbeats 1800000 in
-- Entrywise expansion of the two matrix products at all 16 entries needs extra heartbeats.
private theorem pairedHom_data (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData) :
    pairedHom U hU (pairedBlock d) = orbitMatrix U d := by
  rw [pairedHom_apply]
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [evenRotation, parityBlocks_apply, coupled_apply, xorBit, pairedBlock,
      orbitMatrix, parityMatrix, evenBlock, crossBlock,
      Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      map_mul, Complex.star_def] <;> ring

private theorem unitary_trace (V : unitary Mat) (M : Mat) :
    (Unitary.conjStarAlgAut ℂ Mat V M).trace = M.trace := by
  change (((V : Mat) * M) * (star V : Mat)).trace = _
  rw [Matrix.trace_mul_comm ((V : Mat) * M), ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul]

private theorem pairedHom_trace (U : Block) (hU : Uᴴ * U = 1) (C : Fin 2 → Block) :
    (pairedHom U hU C).trace = ∑ i, (C i).trace := by
  change (Unitary.conjStarAlgAut ℂ Mat (evenUnitary U hU) (coupledHom C)).trace = _
  rw [unitary_trace, coupled_trace]

private theorem orbit_psd (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData)
    (hd : ∀ i, (pairedBlock d i).PosSemidef) : (orbitMatrix U d).PosSemidef := by
  choose B hB using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hd i).nonneg
  have h : pairedBlock d = star B * B := funext hB
  rw [← pairedHom_data U hU, h, map_mul, map_star]
  exact (star_mul_self_nonneg _).posSemidef

private def realPairedBlock (d : AlignedData) (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![d.even i, d.cross i; d.cross i, d.odd i]

private theorem realPairedBlock_symm (d : AlignedData) (i : Fin 2) :
    (realPairedBlock d i).IsSymm := by
  ext j k
  fin_cases j <;> fin_cases k <;> rfl

private def powerData (d : AlignedData) (n : ℕ) : AlignedData where
  even i := (realPairedBlock d i ^ n) 0 0
  odd i := (realPairedBlock d i ^ n) 1 1
  cross i := (realPairedBlock d i ^ n) 0 1

private theorem pairedBlock_power (d : AlignedData) (n : ℕ) :
    pairedBlock (powerData d n) = pairedBlock d ^ n := by
  funext i
  change pairedBlock (powerData d n) i = pairedBlock d i ^ n
  have hcast : pairedBlock d i = (realPairedBlock d i).map Complex.ofRealHom := by
    ext j k
    fin_cases j <;> fin_cases k <;> rfl
  rw [hcast, ← Matrix.map_pow]
  have hsymm := (realPairedBlock_symm d i).pow n
  have h10 : (realPairedBlock d i ^ n) 1 0 = (realPairedBlock d i ^ n) 0 1 :=
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) hsymm
  ext j k
  fin_cases j <;> fin_cases k <;> simp [pairedBlock, powerData, h10]

private theorem orbit_pow (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData) (n : ℕ) :
    orbitMatrix U d ^ n = orbitMatrix U (powerData d n) := by
  rw [← pairedHom_data U hU, ← map_pow, ← pairedBlock_power, pairedHom_data]

private theorem paired_cfc_log (U : Block) (hU : Uᴴ * U = 1) (C : Fin 2 → Block)
    (hC : ∀ i, (C i).IsHermitian) :
    cfc Real.log (pairedHom U hU C) = pairedHom U hU (fun i => cfc Real.log (C i)) := by
  let : ContinuousFunctionalCalculus ℝ (Fin 2 → Block) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hC' : IsSelfAdjoint C := Pi.isSelfAdjoint.mpr hC
  have hc : ContinuousOn Real.log (spectrum ℝ C) := by
    rw [Pi.spectrum_eq]
    exact (Set.finite_iUnion (fun i => (C i).finite_real_spectrum)).continuousOn _
  have hmap := (pairedHom U hU).map_cfc Real.log C hc
    (pairedHom U hU).toLinearMap.continuous_of_finiteDimensional hC' (hC'.map _)
  rw [cfc_map_pi (S := ℂ) Real.log C (by rwa [Pi.spectrum_eq] at hc) hC' hC] at hmap
  exact hmap.symm

-- Both ordinary-trace spectral terms are frame independent. The logarithm
-- only needs continuity on the finite real spectrum, which may contain zero.
private theorem spectral_terms (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData) :
    let C := pairedBlock d ^ 3
    let N := orbitMatrix U d ^ 3
    N.trace = ∑ i, (C i).trace ∧
    (N * cfc Real.log N).trace = ∑ i, (C i * cfc Real.log (C i)).trace := by
  dsimp only
  rw [← pairedHom_data U hU, ← map_pow,
    paired_cfc_log U hU (pairedBlock d ^ 3) (fun i => (pairedBlock_hermitian d i).pow 3), ← map_mul]
  exact ⟨pairedHom_trace _ _ _, pairedHom_trace _ _ _⟩

private theorem diagonal_pairing_affine (U : Block) (hU : Uᴴ * U = 1) (d : AlignedData)
    (q : Occupation → ℂ) :
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    (orbitMatrix U d * diagonal q).trace.re =
      p * (orbitMatrix V d * diagonal q).trace.re +
      (1 - p) * (orbitMatrix W d * diagonal q).trace.re := by
  obtain ⟨hV, _, hVp, hW, _, hWp⟩ := endpoint_frames U.det (det_phase U hU)
  dsimp only
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, Fintype.sum_prod_type,
    Fin.sum_univ_two, orbitMatrix, parityMatrix,
    Matrix.of_apply]
  norm_num [Matrix.diagonal_apply, (even_diagonal_moments U hU d.even).1,
    (even_diagonal_moments U hU d.even).2,
    (even_diagonal_moments _ hV d.even).1, (even_diagonal_moments _ hV d.even).2,
    (even_diagonal_moments _ hW d.even).1, (even_diagonal_moments _ hW d.even).2,
    hVp, hWp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private def lowerProjection : Mat := ∑ k : Fin 2, (modeJump k)ᴴ * modeJump k
private def upperProjection : Mat := ∑ k : Fin 2, modeJump k * (modeJump k)ᴴ

private theorem energy_terms {r : ℝ} (hr : 1 ≤ r) (M : Mat) :
    energy r M = (9 / 4 : ℝ) *
      (gibbsLow r * ((M ^ 3 * lowerProjection).trace.re -
        r * (M ^ 2 * psi M).trace.re) +
       gibbsHigh r * ((M ^ 3 * upperProjection).trace.re -
        r⁻¹ * (M ^ 2 * phi M).trace.re)) := by
  unfold energy
  rw [operator_trace_modular_identity hr]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
    ← Matrix.sum_mul, ← Matrix.mul_sum]
  change (9 / 8 : ℝ) * (M ^ 2 * ((gibbsLow r : ℂ) •
      (lowerProjection * M + M * lowerProjection) -
      (2 * (gibbsLow r : ℂ) * (r : ℂ)) • psi M +
      (gibbsHigh r : ℂ) • (upperProjection * M + M * upperProjection) -
      (2 * (gibbsHigh r : ℂ) * (r : ℂ)⁻¹) • phi M)).trace.re = _
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hProjection (Q : Mat) :
      (M ^ 2 * (Q * M)).trace + (M ^ 2 * (M * Q)).trace =
        2 * (M ^ 3 * Q).trace := by
    rw [← Matrix.trace_add, ← Matrix.mul_add, trace_anticommutator]
  rw [hProjection, hProjection, ← Complex.ofReal_inv]
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re]
  ring

/-- Exact affine interpolation of the cubic deficit in the literal jump coordinates
at fixed determinant, with the full Gibbs entropy. -/
private theorem cubicDeficit_aligned_affine {r : ℝ} (hr : 1 ≤ r) (c : ℝ) (U : Block)
    (hU : Uᴴ * U = 1) (d : AlignedData) :
    let p := Complex.normSq (U 0 0)
    let V := diagonalFrame U.det
    let W := antidiagonalFrame U.det
    0 ≤ p ∧ p ≤ 1 ∧
    WuParityOrbit.cubicDeficit r c (orbitMatrix U d) =
      p * WuParityOrbit.cubicDeficit r c (orbitMatrix V d) +
      (1 - p) * WuParityOrbit.cubicDeficit r c (orbitMatrix W d) := by
  obtain ⟨hV, _, _, hW, _, _⟩ := endpoint_frames U.det (det_phase U hU)
  obtain ⟨hp, hp₁, hphi, hpsi⟩ := directed_mixed_traces_in_frame U hU d (powerData d 2)
  have projectionLower := diagonal_pairing_affine U hU (powerData d 3)
    (fun i : Occupation => ![0,1,1,2] (finProdFinEquiv i))
  have projectionUpper := diagonal_pairing_affine U hU (powerData d 3)
    (fun i : Occupation => ![2,1,1,0] (finProdFinEquiv i))
  have gibbsLog := diagonal_pairing_affine U hU (powerData d 3)
    (fun i : Occupation => (logGibbs r i.1 i.2 : ℂ))
  have spectralU := spectral_terms U hU d
  have spectralV := spectral_terms (diagonalFrame U.det) hV d
  have spectralW := spectral_terms (antidiagonalFrame U.det) hW d
  refine ⟨hp, hp₁, ?_⟩
  dsimp only at spectralU spectralV spectralW hphi hpsi projectionLower projectionUpper gibbsLog ⊢
  simp only [WuParityOrbit.cubicDeficit, energy_terms hr, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re, logGibbs_matrix, lowerProjection, upperProjection,
    jump_projections.1, jump_projections.2]
  rw [spectralU.1, spectralU.2, spectralV.1, spectralV.2, spectralW.1, spectralW.2]
  simp only [orbit_pow U hU d 2, orbit_pow U hU d 3,
    orbit_pow (diagonalFrame U.det) hV d 2, orbit_pow (diagonalFrame U.det) hV d 3,
    orbit_pow (antidiagonalFrame U.det) hW d 2, orbit_pow (antidiagonalFrame U.det) hW d 3,
    projectionLower, projectionUpper, gibbsLog, hphi, hpsi]
  ring

/-- Physical exterior action on the vacuum, one-particle sector (01, 10), and filled state. -/
def oddRotation (V : Block) : Mat :=
  WuParityOrbit.parityBlocks ![diagonal ![1, V.det], V]

private def oddUnitary (V : Block) (hV : Vᴴ * V = 1) : unitary Mat :=
  ⟨oddRotation V, by
    have h : star (oddRotation V) * oddRotation V = 1 := by
      change star (parityBlocksHom ![diagonal ![1, V.det], V]) * parityBlocksHom _ = 1
      rw [← map_star, ← map_mul, ← map_one parityBlocksHom]
      congr 1
      funext i
      fin_cases i
      · change (diagonal ![1, V.det] : Block)ᴴ * diagonal ![1, V.det] = 1
        rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext j
        fin_cases j
        · simp
        · exact det_phase V hV
      · exact hV
    exact Unitary.mem_iff.mpr ⟨h, mul_eq_one_comm.mp h⟩⟩

/-- Conjugation by the physical exterior action. -/
def oddConj (V : Block) (hV : Vᴴ * V = 1) : Mat ≃⋆ₐ[ℂ] Mat :=
  Unitary.conjStarAlgAut ℂ Mat (oddUnitary V hV)

private theorem oddConj_apply (V : Block) (hV : Vᴴ * V = 1) (X : Mat) :
    oddConj V hV X = oddRotation V * X * (oddRotation V)ᴴ := rfl

private theorem oddConj_diagonal (V : Block) (hV : Vᴴ * V = 1) (f : Occupation → ℂ)
    (hf : f (0, 1) = f (1, 0)) :
    oddConj V hV (diagonal f) = diagonal f := by
  rw [oddConj_apply]
  have hcomm : oddRotation V * diagonal f = diagonal f * oddRotation V := by
    ext ⟨i,j⟩ ⟨k,l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      norm_num [Matrix.mul_diagonal, Matrix.diagonal_mul, oddRotation, parityBlocks_apply,
        xorBit, Matrix.diagonal_apply, hf, mul_comm]
  have h : oddRotation V * (oddRotation V)ᴴ = 1 :=
    Unitary.coe_mul_star_self (oddUnitary V hV)
  rw [hcomm, Matrix.mul_assoc, h, Matrix.mul_one]

private theorem oddConj_D (V : Block) (hV : Vᴴ * V = 1) (r : ℝ) :
    oddConj V hV (D r) = D r := by
  apply oddConj_diagonal
  simp [mul_comm]

private theorem oddConj_G (V : Block) (hV : Vᴴ * V = 1) (r : ℝ) :
    oddConj V hV (G r) = G r := by
  apply oddConj_diagonal
  rfl

private theorem oddConj_GInv (V : Block) (hV : Vᴴ * V = 1) (r : ℝ) :
    oddConj V hV (GInv r) = GInv r := by
  apply oddConj_diagonal
  rfl

/-- The signs of the literal jumps give this creation basis in physical odd order. -/
private def creator (i : Fin 2) : Mat := ![(-modeJump 1)ᴴ, (modeJump 0)ᴴ] i

set_option maxHeartbeats 1200000 in
-- Expand the four physical occupations and use the two-by-two determinant formula.
private theorem oddRotation_creator (V : Block) (k : Fin 2) :
    oddRotation V * creator k = (∑ i : Fin 2, V i k • creator i) * oddRotation V := by
  ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [oddRotation, parityBlocks_apply, xorBit, creator, jump_zero, jump_one,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem oddConj_creator (V : Block) (hV : Vᴴ * V = 1) (k : Fin 2) :
    oddConj V hV (creator k) = ∑ i : Fin 2, V i k • creator i := by
  have h : oddRotation V * (oddRotation V)ᴴ = 1 :=
    Unitary.coe_mul_star_self (oddUnitary V hV)
  rw [oddConj_apply, oddRotation_creator, Matrix.mul_assoc, h, Matrix.mul_one]

private theorem oddConj_creator_adjoint (V : Block) (hV : Vᴴ * V = 1) (k : Fin 2) :
    oddConj V hV (creator k)ᴴ = ∑ i : Fin 2, star (V i k) • (creator i)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose, map_star, oddConj_creator,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul]

private theorem row_inner (V : Block) (hV : Vᴴ * V = 1) (i k : Fin 2) :
    ∑ j : Fin 2, V i j * star (V k j) = if i = k then 1 else 0 := by
  have h : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    using congrArg (fun A : Block => A i k) h

private theorem sandwich_sum_mix (v : Block)
    (hv : ∀ i k, ∑ j : Fin 2, star (v i j) * v k j = if i = k then 1 else 0)
    (A : Fin 2 → Mat) (X : Mat) :
    (∑ j : Fin 2, (∑ i : Fin 2, v i j • A i)ᴴ * X * (∑ k : Fin 2, v k j • A k)) =
      ∑ i : Fin 2, (A i)ᴴ * X * A i := by
  calc
    _ = ∑ j : Fin 2, ∑ i : Fin 2, ∑ k : Fin 2,
          (star (v i j) * v k j) • ((A i)ᴴ * X * A k) := by
      simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Finset.sum_mul,
        Matrix.smul_mul, Finset.mul_sum, Matrix.mul_smul, smul_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp only [mul_comm (v _ j)]
    _ = ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
          (star (v i j) * v k j) • ((A i)ᴴ * X * A k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [← Finset.sum_smul, hv, ite_smul, one_smul, zero_smul,
        Fintype.sum_ite_eq]

private theorem dissipator_sum_mix (v : Block)
    (hv : ∀ i k, ∑ j : Fin 2, star (v i j) * v k j = if i = k then 1 else 0)
    (A : Fin 2 → Mat) (X : Mat) :
    (∑ j : Fin 2, dissipator (∑ i : Fin 2, v i j • A i) X) =
      ∑ i : Fin 2, dissipator (A i) X := by
  have h := sandwich_sum_mix v hv A (1 : Mat)
  simp only [Matrix.mul_one] at h
  simp only [dissipator, Finset.sum_sub_distrib, ← Finset.smul_sum,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, h,
    sandwich_sum_mix v hv A X]

private theorem map_dissipator (F : Mat ≃⋆ₐ[ℂ] Mat) (J X : Mat) :
    F (dissipator J X) = dissipator (F J) (F X) := by
  simp only [dissipator, map_add, map_sub, map_mul, map_smul,
    ← Matrix.star_eq_conjTranspose, map_star]

private theorem dissipator_neg (J X : Mat) : dissipator (-J) X = dissipator J X := by
  simp [dissipator]

private theorem sum_creator (X : Mat) :
    (∑ k : Fin 2, dissipator (creator k) X) = ∑ k : Fin 2, dissipator (modeJump k)ᴴ X := by
  simp only [Fin.sum_univ_two]
  change dissipator (-modeJump 1)ᴴ X + dissipator (modeJump 0)ᴴ X = _
  rw [Matrix.conjTranspose_neg, dissipator_neg, add_comm]

private theorem sum_annihilator (X : Mat) :
    (∑ k : Fin 2, dissipator (creator k)ᴴ X) = ∑ k : Fin 2, dissipator (modeJump k) X := by
  simp only [Fin.sum_univ_two]
  change dissipator ((-modeJump 1)ᴴ)ᴴ X + dissipator ((modeJump 0)ᴴ)ᴴ X = _
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    dissipator_neg, add_comm]

/-- The raising dissipator sum is covariant on all matrices. -/
private theorem oddConj_raising (V : Block) (hV : Vᴴ * V = 1) (X : Mat) :
    oddConj V hV (∑ k : Fin 2, dissipator (modeJump k)ᴴ X) =
      ∑ k : Fin 2, dissipator (modeJump k)ᴴ (oddConj V hV X) := by
  simp only [← sum_creator, map_sum, map_dissipator, oddConj_creator]
  apply dissipator_sum_mix
  intro i k
  simpa only [mul_comm (star (V i _)), eq_comm] using row_inner V hV k i

/-- The lowering dissipator sum is covariant on all matrices. -/
private theorem oddConj_lowering (V : Block) (hV : Vᴴ * V = 1) (X : Mat) :
    oddConj V hV (∑ k : Fin 2, dissipator (modeJump k) X) =
      ∑ k : Fin 2, dissipator (modeJump k) (oddConj V hV X) := by
  simp only [← sum_annihilator, map_sum, map_dissipator, oddConj_creator_adjoint]
  exact dissipator_sum_mix (V.map star) (fun i k => by
    simpa only [Matrix.map_apply, star_star] using row_inner V hV i k)
    (fun i => (creator i)ᴴ) (oddConj V hV X)

private theorem oddConj_generator (V : Block) (hV : Vᴴ * V = 1) (r : ℝ) (X : Mat) :
    oddConj V hV (generator r X) = generator r (oddConj V hV X) := by
  simp only [generator, Finset.sum_add_distrib, ← Finset.smul_sum, map_add, map_smul,
    oddConj_lowering, oddConj_raising]

private theorem oddConj_trace (V : Block) (hV : Vᴴ * V = 1) (M : Mat) :
    (oddConj V hV M).trace = M.trace := unitary_trace (oddUnitary V hV) M

private theorem map_log (F : Mat ≃⋆ₐ[ℂ] Mat)
    (M : Mat) (hM : M.IsHermitian) :
    F (cfc Real.log M) = cfc Real.log (F M) :=
  F.toStarAlgHom.map_cfc Real.log M (M.finite_real_spectrum.continuousOn _)
    F.toStarAlgHom.toLinearMap.continuous_of_finiteDimensional hM
    ((show IsSelfAdjoint M from hM).map F.toStarAlgHom)

/-- The normalized cubic CFC entropy with Gibbs reference is invariant. -/
private theorem unitaryConj_entropy (W : unitary Mat) (r : ℝ)
    (hFix : Unitary.conjStarAlgAut ℂ Mat W (D r) = D r)
    (M : Mat) (hM : M.IsHermitian) :
    let N := Unitary.conjStarAlgAut ℂ Mat W M
    (N ^ 3 * (cfc Real.log (N ^ 3) - cfc Real.log (D r))).trace.re -
        (N ^ 3).trace.re * Real.log (N ^ 3).trace.re =
      (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
        (M ^ 3).trace.re * Real.log (M ^ 3).trace.re := by
  have hD : (D r).IsHermitian := by
    simp [D, Matrix.isHermitian_diagonal_iff, IsSelfAdjoint]
  let F := Unitary.conjStarAlgAut ℂ Mat W
  have h :
      F (M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))) =
        (F M) ^ 3 * (cfc Real.log ((F M) ^ 3) - cfc Real.log (D r)) := by
    change F (D r) = D r at hFix
    simp only [map_mul, map_sub, map_log F _ (hM.pow 3), map_log F _ hD, map_pow, hFix]
  change ((F M) ^ 3 * (cfc Real.log ((F M) ^ 3) - cfc Real.log (D r))).trace.re -
      ((F M) ^ 3).trace.re * Real.log ((F M) ^ 3).trace.re = _
  rw [← h, ← map_pow, unitary_trace, unitary_trace]

private theorem oddConj_deficit (V : Block) (hV : Vᴴ * V = 1)
    (r c : ℝ) (M : Mat) (hM : M.IsHermitian) :
    WuParityOrbit.cubicDeficit r c (oddConj V hV M) = WuParityOrbit.cubicDeficit r c M := by
  have hEnergy :
      oddConj V hV (M ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r)) =
        (oddConj V hV M) ^ 2 *
          (G r * generator r (GInv r * oddConj V hV M * GInv r) * G r) := by
    simp only [map_mul, map_pow, oddConj_generator, oddConj_G, oddConj_GInv]
  unfold WuParityOrbit.cubicDeficit energy
  rw [← hEnergy, oddConj_trace]
  rw [show oddConj V hV M = Unitary.conjStarAlgAut ℂ Mat (oddUnitary V hV) M from rfl,
    unitaryConj_entropy (oddUnitary V hV) r (oddConj_D V hV r) M hM]

private theorem oddConj_sandwich_sum (V : Block) (hV : Vᴴ * V = 1) (v : Block)
    (hv : ∀ i k, ∑ j : Fin 2, star (v i j) * v k j = if i = k then 1 else 0)
    (A : Fin 2 → Mat) (hA : ∀ j, oddConj V hV (A j) = ∑ i : Fin 2, v i j • A i)
    (X : Mat) :
    oddConj V hV (∑ j : Fin 2, (A j)ᴴ * X * A j) =
      ∑ j : Fin 2, (A j)ᴴ * oddConj V hV X * A j := by
  have mapAdjoint (Y : Mat) :
      oddConj V hV Yᴴ = (oddConj V hV Y)ᴴ := by
    simpa only [Matrix.star_eq_conjTranspose] using map_star (oddConj V hV) Y
  simp only [map_sum, map_mul, mapAdjoint, hA]
  exact sandwich_sum_mix v hv A (oddConj V hV X)

private theorem oddConj_phi (V : Block) (hV : Vᴴ * V = 1) (X : Mat) :
    oddConj V hV (phi X) = phi (oddConj V hV X) := by
  have hsum (Y : Mat) : (∑ k : Fin 2, (creator k)ᴴ * Y * creator k) = phi Y := by
    simp only [phi, Fin.sum_univ_two]
    change ((-modeJump 1)ᴴ)ᴴ * Y * (-modeJump 1)ᴴ +
      ((modeJump 0)ᴴ)ᴴ * Y * (modeJump 0)ᴴ = _
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg, neg_mul,
      mul_neg, neg_neg]
    exact add_comm _ _
  rw [← hsum X, ← hsum (oddConj V hV X)]
  exact oddConj_sandwich_sum V hV V (fun i k => by
    simpa only [mul_comm (star (V i _)), eq_comm] using row_inner V hV k i)
    creator (oddConj_creator V hV) X

private theorem oddConj_psi (V : Block) (hV : Vᴴ * V = 1) (X : Mat) :
    oddConj V hV (psi X) = psi (oddConj V hV X) := by
  have hsum (Y : Mat) : (∑ k : Fin 2, ((creator k)ᴴ)ᴴ * Y * (creator k)ᴴ) = psi Y := by
    simp only [psi, Fin.sum_univ_two, Matrix.conjTranspose_conjTranspose]
    change (-modeJump 1)ᴴ * Y * ((-modeJump 1)ᴴ)ᴴ +
      (modeJump 0)ᴴ * Y * ((modeJump 0)ᴴ)ᴴ = _
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg, neg_mul,
      mul_neg, neg_neg]
    exact add_comm _ _
  rw [← hsum X, ← hsum (oddConj V hV X)]
  exact oddConj_sandwich_sum V hV (V.map star) (fun i k => by
    simpa only [Matrix.map_apply, star_star] using row_inner V hV i k)
    (fun i => (creator i)ᴴ) (oddConj_creator_adjoint V hV) X

/-- In the literal jump coordinates, both directed CAR trace pairings on a common
physical odd rotation equal the affine averages of the unrotated endpoint pairings
at fixed even determinant. -/
theorem directed_mixed_traces_affine (U : Block) (hU : Uᴴ * U = 1)
    (V : Block) (hV : Vᴴ * V = 1) (M N : AlignedData) :
    let p := Complex.normSq (U 0 0)
    let D := diagonalFrame U.det
    let S := antidiagonalFrame U.det
    0 ≤ p ∧ p ≤ 1 ∧
    (oddConj V hV (orbitMatrix U N) * phi (oddConj V hV (orbitMatrix U M))).trace.re =
      p * (orbitMatrix D N * phi (orbitMatrix D M)).trace.re +
      (1 - p) * (orbitMatrix S N * phi (orbitMatrix S M)).trace.re ∧
    (oddConj V hV (orbitMatrix U N) * psi (oddConj V hV (orbitMatrix U M))).trace.re =
      p * (orbitMatrix D N * psi (orbitMatrix D M)).trace.re +
      (1 - p) * (orbitMatrix S N * psi (orbitMatrix S M)).trace.re := by
  dsimp only
  rw [← oddConj_phi, ← oddConj_psi, ← map_mul, ← map_mul, oddConj_trace, oddConj_trace]
  exact directed_mixed_traces_in_frame U hU M N

private def swapFrame : Block := !![0,1;1,0]

private theorem swapFrame_unitary : swapFrameᴴ * swapFrame = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapFrame, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two]

private def swapConj : Mat ≃⋆ₐ[ℂ] Mat := oddConj swapFrame swapFrame_unitary

private def swapSign (i : Occupation) : ℂ := if i = (1,1) then -1 else 1

private theorem swapRotation_apply (i j : Occupation) :
    oddRotation swapFrame i j = if i = (j.2, j.1) then swapSign j else 0 := by
  rcases i with ⟨i₀,i₁⟩
  rcases j with ⟨j₀,j₁⟩
  fin_cases i₀ <;> fin_cases i₁ <;> fin_cases j₀ <;> fin_cases j₁ <;>
    norm_num [oddRotation, parityBlocks_apply, xorBit, swapFrame, swapSign,
      Matrix.diagonal_apply, Matrix.det_fin_two]

private theorem swapConj_apply (M : Mat) (i j : Occupation) :
    swapConj M i j = swapSign i * M (i.2, i.1) (j.2, j.1) * swapSign j := by
  change (oddConj swapFrame swapFrame_unitary M) i j = _
  rw [oddConj_apply]
  rcases i with ⟨i₀,i₁⟩
  rcases j with ⟨j₀,j₁⟩
  fin_cases i₀ <;> fin_cases i₁ <;> fin_cases j₀ <;> fin_cases j₁ <;>
    norm_num [swapRotation_apply, swapSign, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem first_occupation_bound {r : ℝ} (hr : 1 ≤ r) {M : Mat}
    (hM : M.PosSemidef) (hs : ∀ i j : Occupation, i.1 ≠ j.1 → M i j = 0) :
    0 ≤ WuParityOrbit.cubicDeficit r (alpha r) M := by
  let C (i : Fin 2) : Block := M.submatrix (fun j => (i,j)) (fun j => (i,j))
  have hC (i : Fin 2) : (C i).PosSemidef := hM.submatrix _
  have hblocks : occupationBlocks ![C 0,C 1] = M := by
    have hvec : (![C 0,C 1] : Fin 2 → Block) = C := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    ext ⟨i,j⟩ ⟨k,l⟩
    rw [occupationBlocks_apply]
    by_cases h : i = k
    · subst k
      simp [C]
    · rw [ite_eq_right h, hs _ _ h]
  have hbound := WuCubicConditionalTensorization.occupation_conditional_bound hr (hC 0) (hC 1)
  have h : 0 ≤ WuParityOrbit.cubicDeficit r (alpha r) (occupationBlocks ![C 0,C 1]) :=
    sub_nonneg.mpr hbound
  rwa [hblocks] at h

private theorem second_occupation_bound {r : ℝ} (hr : 1 ≤ r) {M : Mat}
    (hM : M.PosSemidef) (hs : ∀ i j : Occupation, i.2 ≠ j.2 → M i j = 0) :
    0 ≤ WuParityOrbit.cubicDeficit r (alpha r) M := by
  have hswap : (swapConj M).PosSemidef := by
    change (oddConj swapFrame swapFrame_unitary M).PosSemidef
    rw [oddConj_apply]
    exact hM.mul_mul_conjTranspose_same _
  rw [← oddConj_deficit swapFrame swapFrame_unitary r (alpha r) M hM.1]
  apply first_occupation_bound hr hswap
  intro i j hij
  rw [swapConj_apply, hs (i.2,i.1) (j.2,j.1) hij, mul_zero, zero_mul]

/-- Nonnegativity of the literal cubic deficit on the aligned PSD orbit. -/
private theorem cubicDeficit_aligned_nonneg {r : ℝ} (hr : 1 ≤ r) (U : Block)
    (hU : Uᴴ * U = 1) (d : AlignedData) (hd : ∀ i, (pairedBlock d i).PosSemidef) :
    0 ≤ WuParityOrbit.cubicDeficit r (alpha r) (orbitMatrix U d) := by
  obtain ⟨hp, hp₁, hOrbit⟩ := cubicDeficit_aligned_affine hr (alpha r) U hU d
  obtain ⟨hV, _, _, hW, _, _⟩ := endpoint_frames U.det (det_phase U hU)
  obtain ⟨hFirst, hSecond⟩ := endpoint_occupation_blocks U.det d
  rw [hOrbit]
  exact add_nonneg (mul_nonneg hp (first_occupation_bound hr (orbit_psd _ hV d hd) hFirst))
    (mul_nonneg (sub_nonneg.mpr hp₁) (second_occupation_bound hr (orbit_psd _ hW d hd) hSecond))

/-- The cubic bound in the literal jump coordinates. -/
private theorem cubic_inequality_literal {r : ℝ} (hr : 1 ≤ r) {X : Mat}
    (U : Block) (hU : Uᴴ * U = 1) (V : Block) (hV : Vᴴ * V = 1)
    (d : AlignedData) (hd : ∀ i, (pairedBlock d i).PosSemidef)
    (hAligned : G r * X * G r = oddConj V hV (orbitMatrix U d)) :
    let M := G r * X * G r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * generator r X * G r)).trace.re := by
  let M := G r * X * G r
  have hTransport : GInv r * M * GInv r = X := by
    calc
      _ = (GInv r * G r) * X * (G r * GInv r) := by simp only [M, Matrix.mul_assoc]
      _ = X := by rw [GInv_mul_G hr, G_mul_GInv hr, Matrix.one_mul, Matrix.mul_one]
  have h : 0 ≤ WuParityOrbit.cubicDeficit r (alpha r) M := by
    change G r * X * G r = _ at hAligned
    dsimp only [M]
    rw [hAligned, oddConj_deficit V hV r (alpha r) _ (orbit_psd U hU d hd).1]
    exact cubicDeficit_aligned_nonneg hr U hU d hd
  unfold WuParityOrbit.cubicDeficit energy at h
  dsimp only
  exact sub_nonneg.mp (by simpa only [M, hTransport] using h)

/-- The positive two-CAR Wick generator in direct occupation coordinates. The
thermal rates multiply dissipators of the parity-twisted jumps and their adjoints. -/
def wickGenerator (r : ℝ) (X : Mat) : Mat :=
  ∑ k : Fin 2,
    ((2 * (gibbsLow r : ℂ)) • dissipator (modeJump k * parity) X +
      (2 * (gibbsHigh r : ℂ)) • dissipator (modeJump k * parity)ᴴ X)

private def wickPhase (o : Occupation) : ℂ := if o.1 = o.2 then 1 else Complex.I

private def wickUnitary : unitary Mat :=
  ⟨diagonal wickPhase, by
    have h : (diagonal wickPhase : Mat)ᴴ * diagonal wickPhase = 1 := by
      rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext o
      by_cases ho : o.1 = o.2 <;> simp [wickPhase, ho]
    exact Unitary.mem_iff.mpr ⟨h, mul_eq_one_comm.mp h⟩⟩

private def wickConj : Mat ≃⋆ₐ[ℂ] Mat := Unitary.conjStarAlgAut ℂ Mat wickUnitary

private theorem wickConj_entry (X : Mat) (i j : Occupation) :
    wickConj X i j = wickPhase i * X i j * star (wickPhase j) := by
  change ((diagonal wickPhase : Mat) * X * (diagonal wickPhase : Mat)ᴴ) i j = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

private theorem wickConj_diagonal (f : Occupation → ℂ) : wickConj (diagonal f) = diagonal f := by
  have hComm : (diagonal wickPhase : Mat) * diagonal f = diagonal f * diagonal wickPhase := by
    simp only [Matrix.diagonal_mul_diagonal, mul_comm (wickPhase _)]
  have hW : (diagonal wickPhase : Mat) * (diagonal wickPhase : Mat)ᴴ = 1 :=
    Unitary.coe_mul_star_self wickUnitary
  change (diagonal wickPhase : Mat) * diagonal f * (diagonal wickPhase : Mat)ᴴ = diagonal f
  rw [hComm, Matrix.mul_assoc, hW, Matrix.mul_one]

private theorem wickConj_jump (k : Fin 2) :
    wickConj (modeJump k) = Complex.I • (modeJump k * parity) := by
  ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases k <;> fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [wickConj_entry, wickPhase, parity, Matrix.smul_apply, Matrix.mul_diagonal,
      jump_zero, jump_one, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Complex.star_def]

private theorem dissipator_unit_smul (z : ℂ) (hz : star z * z = 1) (J X : Mat) :
    dissipator (z • J) X = dissipator J X := by
  have hz' : z * star z = 1 := (mul_comm _ _).trans hz
  simp only [dissipator, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hz', one_smul]

private theorem wickConj_generator (r : ℝ) (X : Mat) :
    wickConj (generator r X) = wickGenerator r (wickConj X) := by
  have hAdjoint (k : Fin 2) : wickConj (modeJump k)ᴴ =
      star Complex.I • (modeJump k * parity)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose, map_star, wickConj_jump,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul]
  have hI : star Complex.I * Complex.I = 1 := by simp
  have hIstar : star (star Complex.I) * star Complex.I = 1 := by
    rw [star_star, mul_comm, hI]
  simp only [generator, wickGenerator, map_sum, map_add, map_smul, map_dissipator,
    hAdjoint, wickConj_jump, dissipator_unit_smul _ hI, dissipator_unit_smul _ hIstar]

private theorem wickConj_rotation (V : Block) : wickConj (oddRotation V) = oddRotation V := by
  ext ⟨i,j⟩ ⟨a,b⟩
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [wickConj_entry, wickPhase, oddRotation, parityBlocks_apply, xorBit,
      Matrix.diagonal_apply, Complex.star_def] <;> ring_nf <;> simp [pow_two]

private theorem wickConj_orbit (U : Block) (d : AlignedData) :
    wickConj (orbitMatrix (Complex.I • U) d) = orbitMatrix U d := by
  have hEven : evenBlock (Complex.I • U) d.even = evenBlock U d.even := by
    simp only [evenBlock, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hCross : crossBlock (Complex.I • U) d.cross = Complex.I • crossBlock U d.cross := by
    rw [crossBlock, Matrix.smul_mul]
    rfl
  ext ⟨i,j⟩ ⟨a,b⟩
  rw [wickConj_entry, orbitMatrix, orbitMatrix, hEven, hCross]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [wickPhase, parityMatrix, Matrix.of_apply, Matrix.diagonal_apply, Matrix.smul_apply,
      map_mul, Complex.star_def] <;> ring_nf <;> simp [pow_two]

/-- Wu v1 (3.54) at exponent three for the direct two-CAR Wick generator on
transported observables in the physically rotated aligned positive semidefinite class. -/
theorem cubic_inequality_rotated_aligned {r : ℝ} (hr : 1 ≤ r) {X : Mat}
    (U : Block) (hU : Uᴴ * U = 1) (V : Block) (hV : Vᴴ * V = 1)
    (d : AlignedData) (hd : ∀ i, (pairedBlock d i).PosSemidef)
    (hAligned : G r * X * G r = oddConj V hV (orbitMatrix U d)) :
    let M := G r * X * G r
    alpha r * ((M ^ 3 * (cfc Real.log (M ^ 3) - cfc Real.log (D r))).trace.re -
      (M ^ 3).trace.re * Real.log (M ^ 3).trace.re) ≤
      (9 / 8 : ℝ) * (M ^ 2 * (G r * wickGenerator r X * G r)).trace.re := by
  let X₀ := wickConj.symm X
  let M₀ := G r * X₀ * G r
  have hGX : wickConj (G r) = G r := wickConj_diagonal _
  have hDX : wickConj (D r) = D r := wickConj_diagonal _
  have hX : wickConj X₀ = X := wickConj.apply_symm_apply X
  have hM : wickConj M₀ = G r * X * G r := by simp only [M₀, map_mul, hGX, hX]
  have hU₀ : (Complex.I • U)ᴴ * (Complex.I • U) = 1 := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, one_smul, hU]
  have hAligned₀ : M₀ = oddConj V hV (orbitMatrix (Complex.I • U) d) := by
    apply wickConj.injective
    change wickConj M₀ = wickConj (oddConj V hV (orbitMatrix (Complex.I • U) d))
    rw [hM, hAligned, oddConj_apply, oddConj_apply]
    simp only [map_mul, ← Matrix.star_eq_conjTranspose, map_star,
      wickConj_rotation, wickConj_orbit]
  have hHermitian : M₀.IsHermitian := by
    rw [hAligned₀]
    exact (show IsSelfAdjoint _ from (orbit_psd _ hU₀ d hd).1).map (oddConj V hV).toStarAlgHom
  have hEntropy := unitaryConj_entropy wickUnitary r hDX M₀ hHermitian
  change ((wickConj M₀) ^ 3 * (cfc Real.log ((wickConj M₀) ^ 3) -
      cfc Real.log (D r))).trace.re -
    ((wickConj M₀) ^ 3).trace.re * Real.log ((wickConj M₀) ^ 3).trace.re = _ at hEntropy
  have hEnergy : wickConj (M₀ ^ 2 * (G r * generator r X₀ * G r)) =
      (G r * X * G r) ^ 2 * (G r * wickGenerator r X * G r) := by
    simp only [map_mul, map_pow, hM, hGX, wickConj_generator, hX]
  dsimp only
  rw [← hEnergy, show ∀ Y, (wickConj Y).trace = Y.trace from unitary_trace wickUnitary,
    ← hM, hEntropy]
  exact cubic_inequality_literal hr (Complex.I • U) hU₀ V hV d hd hAligned₀

end CubicInequality

end D5.S3.Quantum.Semigroups.WuAlignedCubicOrbit

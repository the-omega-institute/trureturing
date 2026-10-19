/- GID: D5/S3/Quantum/Recovery/S154B0SchurCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/S154B0SchurCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Schur interface and trace slack for the fixed rank-three B0 recovery probe. -/

/-
proof_shape: b0_inverse_identity: content
escape_witness: b0_inverse_identity
proof_shape: b0_schur_interface: content
escape_witness: b0_schur_interface
proof_shape: b0_trace_bound: content
escape_witness: b0_trace_bound
admission_basis: escape-witness (b0_schur_interface)
The three public conclusions are explicit finite matrix and real-arithmetic
certificates for one registered B0 instance. The private matrix definitions and
the arithmetic helper are consumed by the public conclusions. No universal
S.154 quantifier, arbitrary third column, or recovery optimality claim is made.
-/

import D5.S3.Quantum.Matrix.SchurMinimum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix

noncomputable section

/-! Exact rational data for the fixed rank-three recovery probe and its Schur certificate. -/

namespace D5.S3.Quantum.Recovery.S154B0SchurCertificate

private def E0 : Matrix (Fin 5) (Fin 3) ℝ :=
  !![Real.sqrt (1 / 2 : ℝ), 0, 0;
      0, 0, 0;
      0, Real.sqrt (1 / 2 : ℝ), 0;
      0, 0, 0;
      0, 0, 0]
private def E1 : Matrix (Fin 5) (Fin 3) ℝ :=
  !![0, 0, 0;
      Real.sqrt (1 / 2 : ℝ), 0, 0;
      0, 0, 0;
      0, Real.sqrt (1 / 2 : ℝ), 0;
      0, 0, 0]
private def T : Matrix (Fin 5) (Fin 3) ℝ :=
  !![0, Real.sqrt (1 / 5 : ℝ), 0;
      0, 0, 0;
      0, 0, Real.sqrt (1 / 20 : ℝ);
      0, 0, 0;
      Real.sqrt (3 / 4 : ℝ), 0, 0]
private def Y : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![(1 / 6 : ℝ), 1 / 8, 5 / 56, 5 / 56, 1 / 3]

private def Yinv : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.diagonal ![(6 : ℝ), 8, 56 / 5, 56 / 5, 3]

private theorem b0_inverse_identity_calc : Yinv * Y = 1 ∧ Y * Yinv = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Y, Yinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

private theorem b0_schur_interface_calc :
    (1 / 16 : ℝ) • (E0.transpose * Yinv * E0 + E1.transpose * Yinv * E1) +
      (1 / 4 : ℝ) • T.transpose * Yinv * T =
      Matrix.diagonal ![(1 : ℝ), 1, 7 / 50] := by
  ext i j
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have h3 : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have h4 : Real.sqrt (4 : ℝ) ≠ 0 := by positivity
  have h5 : Real.sqrt (5 : ℝ) ≠ 0 := by positivity
  have h20 : Real.sqrt (20 : ℝ) ≠ 0 := by positivity
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hs3 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
  have hs4 : (Real.sqrt (4 : ℝ)) ^ 2 = 4 := by norm_num
  have hs5 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by norm_num
  have hs20 : (Real.sqrt (20 : ℝ)) ^ 2 = 20 := by norm_num
  fin_cases i <;> fin_cases j <;>
    norm_num [E0, E1, T, Yinv, Matrix.mul_apply, Fin.sum_univ_succ,
      Real.sq_sqrt] <;>
    field_simp [h2, h3, h4, h5, h20] <;>
    nlinarith [hs2, hs3, hs4, hs5, hs20]

theorem b0_inverse_identity :
    let Y : Matrix (Fin 5) (Fin 5) ℝ :=
      Matrix.diagonal ![(1 / 6 : ℝ), 1 / 8, 5 / 56, 5 / 56, 1 / 3]
    let Yinv : Matrix (Fin 5) (Fin 5) ℝ :=
      Matrix.diagonal ![(6 : ℝ), 8, 56 / 5, 56 / 5, 3]
    Yinv * Y = 1 ∧ Y * Yinv = 1 := by
  simpa [Y, Yinv] using b0_inverse_identity_calc

theorem b0_schur_interface :
    let E0 : Matrix (Fin 5) (Fin 3) ℝ :=
      !![Real.sqrt (1 / 2 : ℝ), 0, 0;
          0, 0, 0;
          0, Real.sqrt (1 / 2 : ℝ), 0;
          0, 0, 0;
          0, 0, 0]
    let E1 : Matrix (Fin 5) (Fin 3) ℝ :=
      !![0, 0, 0;
          Real.sqrt (1 / 2 : ℝ), 0, 0;
          0, 0, 0;
          0, Real.sqrt (1 / 2 : ℝ), 0;
          0, 0, 0]
    let T : Matrix (Fin 5) (Fin 3) ℝ :=
      !![0, Real.sqrt (1 / 5 : ℝ), 0;
          0, 0, 0;
          0, 0, Real.sqrt (1 / 20 : ℝ);
          0, 0, 0;
          Real.sqrt (3 / 4 : ℝ), 0, 0]
    let Yinv : Matrix (Fin 5) (Fin 5) ℝ :=
      Matrix.diagonal ![(6 : ℝ), 8, 56 / 5, 56 / 5, 3]
    (1 / 16 : ℝ) • (E0.transpose * Yinv * E0 + E1.transpose * Yinv * E1) +
      (1 / 4 : ℝ) • T.transpose * Yinv * T =
      Matrix.diagonal ![(1 : ℝ), 1, 7 / 50] := by
  dsimp
  simpa [E0, E1, T, Yinv] using b0_schur_interface_calc

theorem b0_trace_bound :
    (45 / 56 : ℝ) < (1 + 1 / Real.sqrt 2) / 2 := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hpos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : (17 : ℝ) * Real.sqrt 2 < 28 := by
    have hsq' : ((17 : ℝ) * Real.sqrt 2) ^ 2 < (28 : ℝ) ^ 2 := by
      nlinarith [hs]
    nlinarith [hpos]
  have hdiv : (17 / 28 : ℝ) < 1 / Real.sqrt 2 := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 28) hpos).2
    nlinarith [hsq]
  nlinarith [hdiv]

end D5.S3.Quantum.Recovery.S154B0SchurCertificate

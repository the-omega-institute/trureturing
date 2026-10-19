/- GID: D5/S3/Quantum/Matrix/HayajnehConjectureRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HayajnehConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.conjecture; result=D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.result; claim=D5/S3/Quantum/Matrix/HayajnehConjectureRefutation.conjecture
   digest: The Hayajneh–Hayajneh–Kittaneh unitarily invariant norm conjecture is false. -/

import D5.S3.Quantum.Matrix.SpectralPower
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Schatten.TraceNorm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.HayajnehConjectureRefutation
open SpectralPower (mpow)
open D5.S3.Quantum.Schatten
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)

/-- Conjecture 1, with every matrix, parameter and norm quantifier retained. -/
def conjecture : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef → B.IsHermitian →
    ∀ s t : ℝ, 1 / 2 ≤ s → s ≤ t → t ≤ 1 → ∀ N : UINorm n,
      N.N (mpow A s * B + B * mpow A (1 - s)) ≤
        N.N (mpow A t * B + B * mpow A (1 - t))

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
private def A : Mat := diagonal ![((1 / 81 : ℝ) : ℂ), 1]
private def B : Mat := !![1, 3 / 4; 3 / 4, 1]
private def L : Mat := !![2 / 9, 5 / 6; 5 / 6, 2]
private def R : Mat := !![10 / 27, 7 / 9; 1, 2]

private lemma A_pos : A.PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  fin_cases i
  · apply Complex.nonneg_iff.mpr
    constructor <;> norm_num [A, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail,
      Fin.reduceFinMk]
  · apply Complex.nonneg_iff.mpr
    constructor <;> norm_num [A, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail,
      Fin.reduceFinMk]

private lemma B_hermitian : B.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [B, Matrix.conjTranspose_apply]

private lemma scalar_powers :
    (1 / 81 : ℝ) ^ (1 / 2 : ℝ) = 1 / 9 ∧
    (1 / 81 : ℝ) ^ (1 / 4 : ℝ) = 1 / 3 ∧
    (1 / 81 : ℝ) ^ (3 / 4 : ℝ) = 1 / 27 := by
  have hhalf : (1 / 81 : ℝ) ^ (1 / 2 : ℝ) = 1 / 9 := by
    convert Real.pow_rpow_inv_natCast (x := (1 / 9 : ℝ)) (n := 2)
      (show (0 : ℝ) ≤ 1 / 9 by norm_num) (show (2 : ℕ) ≠ 0 by decide) using 1 <;>
      norm_num
  have hquarter : (1 / 81 : ℝ) ^ (1 / 4 : ℝ) = 1 / 3 := by
    convert Real.pow_rpow_inv_natCast (x := (1 / 3 : ℝ)) (n := 4)
      (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (4 : ℕ) ≠ 0 by decide) using 1 <;>
      norm_num
  refine ⟨hhalf, hquarter, ?_⟩
  calc
    (1 / 81 : ℝ) ^ (3 / 4 : ℝ) = ((1 / 81 : ℝ) ^ (1 / 4 : ℝ)) ^ (3 : ℕ) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      norm_num
    _ = 1 / 27 := by rw [hquarter]; norm_num

private lemma power_values :
    mpow A (1 / 2) = diagonal ![(1 / 9 : ℂ), 1] ∧
    mpow A (1 / 4) = diagonal ![(1 / 3 : ℂ), 1] ∧
    mpow A (3 / 4) = diagonal ![(1 / 27 : ℂ), 1] := by
  have h (p : ℝ) : mpow A p =
      diagonal (fun i => (( (![1 / 81, 1] : Fin 2 → ℝ) i ^ p : ℝ) : ℂ)) := by
    have hA : A = diagonal (fun i =>
        ((![1 / 81, 1] : Fin 2 → ℝ) i : ℂ)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]
    change cfc (fun t : ℝ => t ^ p) A = _
    rw [hA]
    exact D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
      (fun x : ℝ => x ^ p) ![1 / 81, 1]
  constructor
  · rw [h]
    congr 1
    funext i
    fin_cases i
    · simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using
        congrArg (fun x : ℝ => (x : ℂ)) scalar_powers.1
    · norm_num
  constructor
  · rw [h]
    congr 1
    funext i
    fin_cases i
    · simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using
        congrArg (fun x : ℝ => (x : ℂ)) scalar_powers.2.1
    · norm_num
  · rw [h]
    congr 1
    funext i
    fin_cases i
    · simpa [Matrix.cons_val_zero, Matrix.cons_val_one] using
        congrArg (fun x : ℝ => (x : ℂ)) scalar_powers.2.2
    · norm_num

private lemma expressions :
    mpow A (1 / 2) * B + B * mpow A (1 - 1 / 2) = L ∧
    mpow A (3 / 4) * B + B * mpow A (1 - 3 / 4) = R := by
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num]
  rw [power_values.1, power_values.2.1, power_values.2.2]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [B, L, R, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk]

private lemma norm_squares :
    traceNorm L ^ 2 = 481 / 81 ∧ traceNorm R ^ 2 = 4240 / 729 := by
  change (CFC.sqrt (Lᴴ * L)).trace.re ^ 2 = 481 / 81 ∧
    (CFC.sqrt (Rᴴ * R)).trace.re ^ 2 = 4240 / 729
  rw [TraceNorm.transitionMass_sq, TraceNorm.transitionMass_sq]
  norm_num [L, R, RHLinalg.frobSq, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Matrix.det_fin_two, Matrix.vecHead, Matrix.vecTail,
    Fin.reduceFinMk, Complex.star_def, Complex.ext_iff, Complex.mul_re,
    Complex.mul_im, Complex.div_re, Complex.div_im]

/-- The trace norm on two by two complex matrices refutes Conjecture 1. -/
theorem result : ¬ conjecture := by
  intro h
  have bad := h 2 A B A_pos B_hermitian (1 / 2) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (TraceNorm.traceNormUINorm 2)
  change traceNorm _ ≤ traceNorm _ at bad
  rw [expressions.1, expressions.2] at bad
  have hL := traceNorm_nonneg L
  have hR := traceNorm_nonneg R
  have hs := (sq_le_sq₀ hL hR).2 bad
  rw [norm_squares.1, norm_squares.2] at hs
  norm_num at hs

#print axioms result

end D5.S3.Quantum.Matrix.HayajnehConjectureRefutation

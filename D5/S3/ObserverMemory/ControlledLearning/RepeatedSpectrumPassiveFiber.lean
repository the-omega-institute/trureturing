/- GID: D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber
   mirror-E: none(waiver:unbounded-exact-passive-observation-classification)
   anchors: []
   utility: none
   digest: Symmetric commutant fibers at repeated spectra and resonance. -/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Repeated positive spectra in passive two-layer learning

These are the exact external Gram recurrences of simultaneous equal-step
Euclidean gradient descent on the fixed loss `||VU||_F^2 / 2`.
The output gradient is the current output, rather than a free control.

The one public theorem classifies the complete symmetric-matrix fiber of
both output steps. It allows repeated positive initial singular values and
allows `1 - eta^2 * sigma(i)^2 = 0`. Thus resonant erased directions remain
in the classification. PSD and width/rank restrictions can subsequently be
intersected with this exact affine fiber.

The conclusion is limited to symmetric-block recurrences. Positive
semidefiniteness, width/rank realizability, later-step genericity, resonance
collapse and stability require additional hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace D5.S3.ObserverMemory.ControlledLearning.RepeatedSpectrumPassiveFiber

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Actual output after one fixed-zero-label passive step. -/
def outputStep (A B W : Matrix I I ℝ) (eta : ℝ) : Matrix I I ℝ :=
  W - eta • (B * W + W * A) + eta ^ 2 • (W * W.transpose * W)

/-- Input-side Gram block after that same step. -/
def inputStep (A B W : Matrix I I ℝ) (eta : ℝ) : Matrix I I ℝ :=
  A - (2 * eta) • (W.transpose * W) + eta ^ 2 • (W.transpose * B * W)

/-- Output-side Gram block after that same step. -/
def gramOutputStep (A B W : Matrix I I ℝ) (eta : ℝ) : Matrix I I ℝ :=
  B - (2 * eta) • (W * W.transpose) + eta ^ 2 • (W * A * W.transpose)

/-- Two actual passive steps, with the second gradient equal to the first output. -/
def twoStepOutput (A B W : Matrix I I ℝ) (eta tau : ℝ) : Matrix I I ℝ :=
  outputStep (inputStep A B W eta) (gramOutputStep A B W eta)
    (outputStep A B W eta) tau

/-- Complete two-step fiber for an arbitrary positive diagonal spectrum.
No distinctness or nonresonance assumption is imposed on `sigma`.
The difference `X` must commute with the initial diagonal matrix;
its transported difference `(1-eta^2*S*S)*X` must commute with the
observed first output. All such differences, including erased ones,
produce exactly the same first two outputs. -/
theorem two_step_outputs_iff_commuting_difference
    (sigma : I → ℝ) (hsigma : ∀ i, 0 < sigma i)
    (A1 B1 A2 B2 : Matrix I I ℝ)
    (hA1 : A1.transpose = A1) (hB1 : B1.transpose = B1)
    (hA2 : A2.transpose = A2) (hB2 : B2.transpose = B2)
    (eta tau : ℝ) (heta : eta ≠ 0) (htau : tau ≠ 0) :
    let S : Matrix I I ℝ := Matrix.diagonal sigma
    let D : Matrix I I ℝ := 1 - eta ^ 2 • (S * S)
    let W1 : Matrix I I ℝ := outputStep A1 B1 S eta
    (outputStep A1 B1 S eta = outputStep A2 B2 S eta ∧
      twoStepOutput A1 B1 S eta tau = twoStepOutput A2 B2 S eta tau) ↔
    ∃ X : Matrix I I ℝ,
      X.transpose = X ∧ X * S = S * X ∧
      A2 = A1 + X ∧ B2 = B1 - X ∧
      (D * X) * W1 = W1 * (D * X) := by
  classical
  dsimp only
  let S : Matrix I I ℝ := Matrix.diagonal sigma
  let D : Matrix I I ℝ := 1 - eta ^ 2 • (S * S)
  let W1 : Matrix I I ℝ := outputStep A1 B1 S eta
  change (outputStep A1 B1 S eta = outputStep A2 B2 S eta ∧
      twoStepOutput A1 B1 S eta tau = twoStepOutput A2 B2 S eta tau) ↔
    ∃ X : Matrix I I ℝ,
      X.transpose = X ∧ X * S = S * X ∧
      A2 = A1 + X ∧ B2 = B1 - X ∧
      (D * X) * W1 = W1 * (D * X)
  have hST : S.transpose = S := by simp [S]
  have firstTransport (X : Matrix I I ℝ) (hXS : X * S = S * X) :
      outputStep (A1 + X) (B1 - X) S eta = W1 := by
    dsimp [outputStep, W1]
    simp only [Matrix.sub_mul, Matrix.mul_add, hXS]
    module
  have inputTransport (X : Matrix I I ℝ) (hXS : X * S = S * X) :
      inputStep (A1 + X) (B1 - X) S eta =
        inputStep A1 B1 S eta + D * X := by
    dsimp [inputStep, D]
    rw [hST]
    simp only [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hXS]
    module
  have outputTransport (X : Matrix I I ℝ) (hXS : X * S = S * X) :
      gramOutputStep (A1 + X) (B1 - X) S eta =
        gramOutputStep A1 B1 S eta - D * X := by
    dsimp [gramOutputStep, D]
    rw [hST]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hXS]
    module
  have signal (X : Matrix I I ℝ) (hXS : X * S = S * X) :
      twoStepOutput (A1 + X) (B1 - X) S eta tau -
        twoStepOutput A1 B1 S eta tau =
      tau • ((D * X) * W1 - W1 * (D * X)) := by
    unfold twoStepOutput
    rw [inputTransport X hXS, outputTransport X hXS, firstTransport X hXS]
    change outputStep (inputStep A1 B1 S eta + D * X)
        (gramOutputStep A1 B1 S eta - D * X) W1 tau -
      outputStep (inputStep A1 B1 S eta) (gramOutputStep A1 B1 S eta) W1 tau = _
    simp only [outputStep, Matrix.sub_mul, Matrix.mul_add, smul_add, smul_sub]
    module
  constructor
  · rintro ⟨hfirst, hsecond⟩
    let X : Matrix I I ℝ := A2 - A1
    let Y : Matrix I I ℝ := B2 - B1
    have hXT : X.transpose = X := by simp [X, Matrix.transpose_sub, hA1, hA2]
    have hYT : Y.transpose = Y := by simp [Y, Matrix.transpose_sub, hB1, hB2]
    have hlinear : B2 * S + S * A2 = B1 * S + S * A1 := by
      ext i j
      have h := congrArg (fun M : Matrix I I ℝ => M i j) hfirst
      simp only [outputStep, Matrix.add_apply, Matrix.sub_apply,
        Matrix.smul_apply, smul_eq_mul] at h
      apply mul_left_cancel₀ heta
      change eta * ((B2 * S) i j + (S * A2) i j) =
        eta * ((B1 * S) i j + (S * A1) i j)
      linarith
    have hzero : Y * S + S * X = 0 := by
      ext i j
      have h := congrArg (fun M : Matrix I I ℝ => M i j) hlinear
      simp only [Matrix.add_apply] at h
      simp only [X, Y, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_apply,
        Matrix.sub_apply, Matrix.zero_apply]
      linarith
    have hentry (i j : I) : Y i j * sigma j + sigma i * X i j = 0 := by
      have h := congrArg (fun M : Matrix I I ℝ => M i j) hzero
      simpa [S] using h
    have hXsym (i j : I) : X j i = X i j := by
      have h := congrArg (fun M : Matrix I I ℝ => M i j) hXT
      simpa only [Matrix.transpose_apply] using h
    have hYsym (i j : I) : Y j i = Y i j := by
      have h := congrArg (fun M : Matrix I I ℝ => M i j) hYT
      simpa only [Matrix.transpose_apply] using h
    have hneg (i j : I) : Y i j = - X i j := by
      have h1 := hentry i j
      have h2 := hentry j i
      rw [hXsym i j, hYsym i j] at h2
      have hp : (sigma i + sigma j) * (Y i j + X i j) = 0 := by nlinarith
      have hs : sigma i + sigma j ≠ 0 := ne_of_gt (add_pos (hsigma i) (hsigma j))
      have hz := (mul_eq_zero.mp hp).resolve_left hs
      linarith
    have hXS : X * S = S * X := by
      ext i j
      have h := hentry i j
      rw [hneg i j] at h
      simp only [S, Matrix.mul_diagonal, Matrix.diagonal_mul]
      nlinarith
    have hA : A2 = A1 + X := by dsimp [X]; abel
    have hB : B2 = B1 - X := by
      ext i j
      have h := hneg i j
      simp only [Y, Matrix.sub_apply] at h
      simp only [Matrix.sub_apply]
      linarith
    have heq : twoStepOutput (A1 + X) (B1 - X) S eta tau =
        twoStepOutput A1 B1 S eta tau := by
      simpa only [hA, hB] using hsecond.symm
    have hz : tau • ((D * X) * W1 - W1 * (D * X)) = 0 := by
      rw [← signal X hXS, heq, sub_self]
    refine ⟨X, hXT, hXS, hA, hB, ?_⟩
    ext i j
    have h := congrArg (fun M : Matrix I I ℝ => M i j) hz
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.zero_apply] at h
    have hh := (mul_eq_zero.mp h).resolve_left htau
    linarith
  · rintro ⟨X, _, hXS, hA, hB, hcomm⟩
    constructor
    · rw [hA, hB]
      exact (firstTransport X hXS).symm
    · rw [hA, hB]
      have hz : twoStepOutput (A1 + X) (B1 - X) S eta tau -
          twoStepOutput A1 B1 S eta tau = 0 := by
        rw [signal X hXS, hcomm, sub_self, smul_zero]
      exact (sub_eq_zero.mp hz).symm

#print axioms two_step_outputs_iff_commuting_difference

end D5.S3.ObserverMemory.ControlledLearning.RepeatedSpectrumPassiveFiber

/- GID: D5/S3/ObserverMemory/ControlledLearning/TwoStepGramObservability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/ControlledLearning/TwoStepGramObservability
   mirror-E: none(waiver:unbounded-controlled-matrix-identification)
   anchors: []
   utility: none
   digest: All reset one-step outputs and one noncommuting two-step probe determine both external Gram blocks. -/

import Mathlib

/-!
# Finite-step identification beyond the instantaneous tangent response

The definitions are the exact external Gram recurrences of simultaneous,
equal-step Euclidean gradient descent in a two-layer real linear network.
The control is a prescribed output gradient, realizable by a linear loss.

The single public theorem identifies both Gram blocks from every reset
one-step output and one specified two-step output. Its proof constructs the
entire scalar ambiguity of the one-step response and transports that ambiguity
through two actual discrete updates. The nonzero premise concerns only the
chosen controls, never a hidden coupling, Gram eigenvalue or parameter.

Positivity and factor realizability are not required for this stronger algebraic
identity. The accompanying ordinary theory supplies realizations and coordinate
controls, and separates the scalar-input/scalar-output exception. This file does
not formalize the continuous-time flow, noise minimax law or quantum instrument.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.ObserverMemory.ControlledLearning.TwoStepGramObservability

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- Output after one simultaneous controlled gradient step. -/
def outputStep (A : Matrix I I ℝ) (B : Matrix O O ℝ)
    (W G : Matrix O I ℝ) (eta : ℝ) : Matrix O I ℝ :=
  W - eta • (B * G + G * A) + eta ^ 2 • (G * W.transpose * G)

/-- Input Gram block after the same step. -/
def inputGramStep (A : Matrix I I ℝ) (B : Matrix O O ℝ)
    (W G : Matrix O I ℝ) (eta : ℝ) : Matrix I I ℝ :=
  A - eta • (W.transpose * G + G.transpose * W) +
    eta ^ 2 • (G.transpose * B * G)

/-- Output Gram block after the same step. -/
def outputGramStep (A : Matrix I I ℝ) (B : Matrix O O ℝ)
    (W G : Matrix O I ℝ) (eta : ℝ) : Matrix O O ℝ :=
  B - eta • (W * G.transpose + G * W.transpose) +
    eta ^ 2 • (G * A * G.transpose)

/-- Apply the second prescribed gradient to the actual first-step Gram state. -/
def twoStepOutput (A : Matrix I I ℝ) (B : Matrix O O ℝ)
    (W G H : Matrix O I ℝ) (eta tau : ℝ) : Matrix O I ℝ :=
  outputStep (inputGramStep A B W G eta) (outputGramStep A B W G eta)
    (outputStep A B W G eta) H tau

/-- The reset one-step family has a scalar Gram ambiguity. A fixed two-step
control whose rectangular Gram commutator has a nonzero entry removes exactly
that ambiguity. No nondegeneracy of the unknown state is assumed. -/
theorem one_step_and_cross_probe_determine_gram
    [Nonempty I] [Nonempty O]
    (A1 A2 : Matrix I I ℝ) (B1 B2 : Matrix O O ℝ)
    (W G H : Matrix O I ℝ) (eta tau : ℝ)
    (heta : eta ≠ 0) (htau : tau ≠ 0)
    (i : O) (j : I)
    (hprobe : (H * G.transpose * G - G * G.transpose * H) i j ≠ 0)
    (hone : ∀ P : Matrix O I ℝ,
      outputStep A1 B1 W P eta = outputStep A2 B2 W P eta)
    (htwo : twoStepOutput A1 B1 W G H eta tau =
      twoStepOutput A2 B2 W G H eta tau) :
    A1 = A2 ∧ B1 = B2 := by
  classical
  let DA : Matrix I I ℝ := A2 - A1
  let DB : Matrix O O ℝ := B2 - B1
  have hlinear (P : Matrix O I ℝ) : B2 * P + P * A2 = B1 * P + P * A1 := by
    ext a b
    have h := congrArg (fun M : Matrix O I ℝ => M a b) (hone P)
    simp only [outputStep, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul] at h
    apply mul_left_cancel₀ heta
    change eta * ((B2 * P) a b + (P * A2) a b) =
      eta * ((B1 * P) a b + (P * A1) a b)
    linarith
  have hzero (P : Matrix O I ℝ) : DB * P + P * DA = 0 := by
    ext a b
    have h := congrArg (fun M : Matrix O I ℝ => M a b) (hlinear P)
    simp only [Matrix.add_apply] at h
    simp only [DA, DB, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
    linarith
  let unitProbe (a : O) (b : I) : Matrix O I ℝ :=
    fun u v => if u = a ∧ v = b then 1 else 0
  have hentry (a u : O) (b v : I) :
      (if v = b then DB u a else 0) + (if u = a then DA b v else 0) = 0 := by
    have h := congrArg (fun M : Matrix O I ℝ => M u v) (hzero (unitProbe a b))
    by_cases hv : v = b <;> by_cases hu : u = a <;>
      simpa [Matrix.mul_apply, unitProbe, hv, hu] using h
  let i0 : O := Classical.choice inferInstance
  let j0 : I := Classical.choice inferInstance
  let c : ℝ := DA j0 j0
  have hdiag (a : O) (b : I) : DB a a + DA b b = 0 := by
    simpa using hentry a a b b
  have hDAoff (a b : I) (hab : a ≠ b) : DA a b = 0 := by
    simpa [hab, Ne.symm hab] using hentry i0 i0 a b
  have hDBoff (a b : O) (hab : a ≠ b) : DB a b = 0 := by
    simpa [hab] using hentry b a j0 j0
  have hDAdiag (a : I) : DA a a = c := by
    have h1 := hdiag i0 a
    have h2 := hdiag i0 j0
    dsimp [c]
    linarith
  have hDBdiag (a : O) : DB a a = -c := by
    have h := hdiag a j0
    dsimp [c]
    linarith
  have hDA : DA = c • (1 : Matrix I I ℝ) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [hDAdiag]
    · simp [Matrix.one_apply, hab, hDAoff a b hab]
  have hDB : DB = (-c) • (1 : Matrix O O ℝ) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [hDBdiag]
    · simp [Matrix.one_apply, hab, hDBoff a b hab]
  have hA : A2 = A1 + c • (1 : Matrix I I ℝ) := by
    ext a b
    have h := congrArg (fun M : Matrix I I ℝ => M a b) hDA
    simp only [DA, Matrix.sub_apply] at h
    simp only [Matrix.add_apply]
    linarith
  have hB : B2 = B1 - c • (1 : Matrix O O ℝ) := by
    ext a b
    have h := congrArg (fun M : Matrix O O ℝ => M a b) hDB
    simp only [DB, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  have hWstep : outputStep A2 B2 W G eta = outputStep A1 B1 W G eta :=
    (hone G).symm
  have hAstep : inputGramStep A2 B2 W G eta =
      inputGramStep A1 B1 W G eta +
        c • ((1 : Matrix I I ℝ) - eta ^ 2 • (G.transpose * G)) := by
    rw [hA, hB]
    simp only [inputGramStep, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, smul_add, smul_sub, smul_smul]
    module
  have hBstep : outputGramStep A2 B2 W G eta =
      outputGramStep A1 B1 W G eta -
        c • ((1 : Matrix O O ℝ) - eta ^ 2 • (G * G.transpose)) := by
    rw [hA, hB]
    simp only [outputGramStep, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, smul_add, smul_sub, smul_smul]
    module
  have hsignal : twoStepOutput A2 B2 W G H eta tau -
      twoStepOutput A1 B1 W G H eta tau =
      (c * eta ^ 2 * tau) • (H * G.transpose * G - G * G.transpose * H) := by
    unfold twoStepOutput
    rw [hAstep, hBstep, hWstep]
    simp only [outputStep, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, smul_add, smul_sub, smul_smul]
    module
  have hsignalzero :
      (c * eta ^ 2 * tau) • (H * G.transpose * G - G * G.transpose * H) = 0 := by
    rw [← hsignal, htwo, sub_self]
  have hscalar := congrArg (fun M : Matrix O I ℝ => M i j) hsignalzero
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hscalar
  have hproduct : c * (eta ^ 2 * tau *
      (H * G.transpose * G - G * G.transpose * H) i j) = 0 := by
    simpa only [mul_assoc] using hscalar
  have hn : eta ^ 2 * tau *
      (H * G.transpose * G - G * G.transpose * H) i j ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 heta) htau) hprobe
  have hc : c = 0 := (mul_eq_zero.mp hproduct).resolve_right hn
  constructor
  · simpa [hc] using hA.symm
  · simpa [hc] using hB.symm

#print axioms one_step_and_cross_probe_determine_gram

end D5.S3.ObserverMemory.ControlledLearning.TwoStepGramObservability

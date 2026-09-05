/- GID: D5/S3/Observer/Hankel/ProjectedRealizationError
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ProjectedRealizationError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Constructed reduced dynamics has residual-based finite-time and uniform output bounds. -/

import D5.S3.Observer.Hankel.HankelMinimalStateDimension
import Mathlib.Analysis.Normed.Operator.Basic

/- Library search (2026-09-05): no D5 reducedDynamics owner or exact projected
   realization error theorem was found. Reuse FiniteLinearRealization and
   Mathlib continuous linear maps, operator norms and finite sums. The bound is
   derived from the actual full and reduced recurrences, not from an assumed
   error identity. This is a residual certificate, not a balanced-truncation or
   singular-value optimality theorem. The uniform result requires contraction
   in the chosen norms; spectral-radius stability alone is not substituted. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.ProjectedRealizationError

open D5.S3.Observer.Hankel.HankelMinimalStateDimension

variable {U V W Y : Type}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Zero-initial-state response to an arbitrary input sequence. -/
def drivenState (A : V →L[ℝ] V) (B : U →L[ℝ] V) (input : ℕ → U) : ℕ → V
  | 0 => 0
  | n + 1 => A (drivenState A B input n) + B (input n)

/-- The actual reduced state transition `P A J`, on the reduced carrier W. -/
def reducedDynamics (A : V →L[ℝ] V) (P : V →L[ℝ] W) (J : W →L[ℝ] V) :
    W →L[ℝ] W := P.comp (A.comp J)

/-- The actual reduced input map `P B`. -/
def reducedInput (B : U →L[ℝ] V) (P : V →L[ℝ] W) : U →L[ℝ] W := P.comp B

/-- The actual reduced output map `C J`. -/
def reducedOutput (C : V →L[ℝ] Y) (J : W →L[ℝ] V) : W →L[ℝ] Y := C.comp J

/-- Package the constructed maps in the existing finite-realization interface.
The error results remain valid without assuming `P J = id`; that additional
identity makes the pair a retraction/projection in the usual sense. -/
def projectedRealization [FiniteDimensional ℝ W]
    (A : V →L[ℝ] V) (B : U →L[ℝ] V) (C : V →L[ℝ] Y)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) : FiniteLinearRealization ℝ U Y where
  State := W
  dynamics := (reducedDynamics A P J).toLinearMap
  input := (reducedInput B P).toLinearMap
  output := (reducedOutput C J).toLinearMap

/-- Failure of the lift to intertwine the full and reduced transitions. -/
def dynamicsResidual (A : V →L[ℝ] V) (P : V →L[ℝ] W) (J : W →L[ℝ] V) :
    W →L[ℝ] V := A.comp J - J.comp (reducedDynamics A P J)

/-- Input information omitted by lifting the reduced input. -/
def inputResidual (B : U →L[ℝ] V) (P : V →L[ℝ] W) (J : W →L[ℝ] V) :
    U →L[ℝ] V := B - J.comp (reducedInput B P)

/-- Full state minus the lifted state of the constructed reduced model. -/
def stateError (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) (input : ℕ → U) (n : ℕ) : V :=
  drivenState A B input n -
    J (drivenState (reducedDynamics A P J) (reducedInput B P) input n)

/-- The exact error equation is proved from the two system recurrences. -/
theorem stateError_succ (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) (input : ℕ → U) (n : ℕ) :
    stateError A B P J input (n + 1) =
      A (stateError A B P J input n) +
        dynamicsResidual A P J
          (drivenState (reducedDynamics A P J) (reducedInput B P) input n) +
        inputResidual B P J (input n) := by
  simp only [stateError, drivenState, dynamicsResidual, inputResidual,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel

private theorem stateError_step_bound (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) (input : ℕ → U) (n : ℕ) :
    ‖stateError A B P J input (n + 1)‖ ≤
      ‖A‖ * ‖stateError A B P J input n‖ +
        ‖dynamicsResidual A P J‖ *
          ‖drivenState (reducedDynamics A P J) (reducedInput B P) input n‖ +
        ‖inputResidual B P J‖ * ‖input n‖ := by
  rw [stateError_succ]
  exact (norm_add_le _ _).trans
    ((add_le_add_right (norm_add_le _ _) _).trans
      (add_le_add
        (add_le_add (A.le_opNorm _) ((dynamicsResidual A P J).le_opNorm _))
        ((inputResidual B P J).le_opNorm _)))

private def weightedResidual (q : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, q ^ (n - 1 - k) * r k

private theorem weightedResidual_succ (q : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    weightedResidual q r (n + 1) = q * weightedResidual q r n + r n := by
  unfold weightedResidual
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have index : n - k = (n - 1 - k) + 1 := by
    have smaller := Finset.mem_range.mp hk
    omega
  rw [index, pow_succ]
  ring

/-- A finite-horizon a posteriori bound, valid even for unstable models. -/
theorem stateError_le_residual_sum (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) (input : ℕ → U) (n : ℕ) :
    ‖stateError A B P J input n‖ ≤
      ∑ k ∈ Finset.range n, ‖A‖ ^ (n - 1 - k) *
        (‖dynamicsResidual A P J‖ *
            ‖drivenState (reducedDynamics A P J) (reducedInput B P) input k‖ +
          ‖inputResidual B P J‖ * ‖input k‖) := by
  let r := fun k => ‖dynamicsResidual A P J‖ *
      ‖drivenState (reducedDynamics A P J) (reducedInput B P) input k‖ +
    ‖inputResidual B P J‖ * ‖input k‖
  change ‖stateError A B P J input n‖ ≤ weightedResidual ‖A‖ r n
  induction n with
  | zero => simp [stateError, drivenState, weightedResidual]
  | succ n ih =>
      rw [weightedResidual_succ]
      calc
        ‖stateError A B P J input (n + 1)‖ ≤
            ‖A‖ * ‖stateError A B P J input n‖ + r n := by
          simpa only [r, add_assoc] using stateError_step_bound A B P J input n
        _ ≤ ‖A‖ * weightedResidual ‖A‖ r n + r n :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih (norm_nonneg A)) _

/-- Convert the residual state certificate into an output-error certificate. -/
theorem outputError_le_residual_sum (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (C : V →L[ℝ] Y) (P : V →L[ℝ] W) (J : W →L[ℝ] V)
    (input : ℕ → U) (n : ℕ) :
    ‖C (drivenState A B input n) -
        reducedOutput C J
          (drivenState (reducedDynamics A P J) (reducedInput B P) input n)‖ ≤
      ‖C‖ * (∑ k ∈ Finset.range n, ‖A‖ ^ (n - 1 - k) *
        (‖dynamicsResidual A P J‖ *
            ‖drivenState (reducedDynamics A P J) (reducedInput B P) input k‖ +
          ‖inputResidual B P J‖ * ‖input k‖)) := by
  have outputIdentity :
      C (drivenState A B input n) -
          reducedOutput C J
            (drivenState (reducedDynamics A P J) (reducedInput B P) input n) =
        C (stateError A B P J input n) := by
    simp only [stateError, reducedOutput, ContinuousLinearMap.comp_apply, map_sub]
  rw [outputIdentity]
  exact (C.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (stateError_le_residual_sum A B P J input n)
      (norm_nonneg C))

private theorem scalarBudget_fixedpoint (a b : ℝ) (contractive : a < 1) :
    a * (b / (1 - a)) + b = b / (1 - a) := by
  have denominator : 1 - a ≠ 0 := ne_of_gt (sub_pos.mpr contractive)
  field_simp [denominator] <;> ring

/-- A contractive system maps bounded inputs to a uniform state bound. -/
theorem drivenState_norm_le_of_contraction (A : V →L[ℝ] V) (B : U →L[ℝ] V)
    (input : ℕ → U) (M : ℝ) (nonnegative : 0 ≤ M)
    (inputBound : ∀ k, ‖input k‖ ≤ M) (contractive : ‖A‖ < 1) (n : ℕ) :
    ‖drivenState A B input n‖ ≤ ‖B‖ * M / (1 - ‖A‖) := by
  let S := ‖B‖ * M / (1 - ‖A‖)
  have denominator : 0 < 1 - ‖A‖ := sub_pos.mpr contractive
  have stateBoundNonnegative : 0 ≤ S :=
    div_nonneg (mul_nonneg (norm_nonneg B) nonnegative) (le_of_lt denominator)
  have invariant : ‖A‖ * S + ‖B‖ * M = S := by
    simpa only [S] using scalarBudget_fixedpoint ‖A‖ (‖B‖ * M) contractive
  change ‖drivenState A B input n‖ ≤ S
  induction n with
  | zero => simpa only [drivenState, norm_zero] using stateBoundNonnegative
  | succ n ih =>
      calc
        ‖drivenState A B input (n + 1)‖ ≤
            ‖A‖ * ‖drivenState A B input n‖ + ‖B‖ * ‖input n‖ :=
          (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) (B.le_opNorm _))
        _ ≤ ‖A‖ * S + ‖B‖ * M :=
          add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg A))
            (mul_le_mul_of_nonneg_left (inputBound n) (norm_nonneg B))
        _ = S := invariant

/-- An explicit uniform output bound under contraction of both actual dynamics.
No singular-value or general spectral-radius stability claim is made. -/
theorem outputError_uniform_of_contraction
    (A : V →L[ℝ] V) (B : U →L[ℝ] V) (C : V →L[ℝ] Y)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V) (input : ℕ → U)
    (M : ℝ) (nonnegative : 0 ≤ M) (inputBound : ∀ k, ‖input k‖ ≤ M)
    (fullContractive : ‖A‖ < 1) (reducedContractive : ‖reducedDynamics A P J‖ < 1)
    (n : ℕ) :
    ‖C (drivenState A B input n) -
        reducedOutput C J
          (drivenState (reducedDynamics A P J) (reducedInput B P) input n)‖ ≤
      ‖C‖ * ((‖dynamicsResidual A P J‖ *
          (‖reducedInput B P‖ * M / (1 - ‖reducedDynamics A P J‖)) +
        ‖inputResidual B P J‖ * M) / (1 - ‖A‖)) := by
  let Z := ‖reducedInput B P‖ * M / (1 - ‖reducedDynamics A P J‖)
  let E := (‖dynamicsResidual A P J‖ * Z + ‖inputResidual B P J‖ * M) /
    (1 - ‖A‖)
  have fullDenominator : 0 < 1 - ‖A‖ := sub_pos.mpr fullContractive
  have reducedDenominator : 0 < 1 - ‖reducedDynamics A P J‖ :=
    sub_pos.mpr reducedContractive
  have zNonnegative : 0 ≤ Z :=
    div_nonneg (mul_nonneg (norm_nonneg _) nonnegative) (le_of_lt reducedDenominator)
  have eNonnegative : 0 ≤ E :=
    div_nonneg (add_nonneg (mul_nonneg (norm_nonneg _) zNonnegative)
      (mul_nonneg (norm_nonneg _) nonnegative)) (le_of_lt fullDenominator)
  have reducedBound (k : ℕ) :
      ‖drivenState (reducedDynamics A P J) (reducedInput B P) input k‖ ≤ Z :=
    drivenState_norm_le_of_contraction _ _ input M nonnegative inputBound
      reducedContractive k
  have invariant :
      ‖A‖ * E + ‖dynamicsResidual A P J‖ * Z + ‖inputResidual B P J‖ * M = E := by
    simpa only [E, add_assoc] using
      scalarBudget_fixedpoint ‖A‖
        (‖dynamicsResidual A P J‖ * Z + ‖inputResidual B P J‖ * M) fullContractive
  have errorBound (k : ℕ) : ‖stateError A B P J input k‖ ≤ E := by
    induction k with
    | zero => simpa [stateError, drivenState] using eNonnegative
    | succ k ih =>
        calc
          ‖stateError A B P J input (k + 1)‖ ≤
              ‖A‖ * ‖stateError A B P J input k‖ +
                ‖dynamicsResidual A P J‖ *
                  ‖drivenState (reducedDynamics A P J) (reducedInput B P) input k‖ +
                ‖inputResidual B P J‖ * ‖input k‖ :=
            stateError_step_bound A B P J input k
          _ ≤ ‖A‖ * E + ‖dynamicsResidual A P J‖ * Z + ‖inputResidual B P J‖ * M :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg A))
                (mul_le_mul_of_nonneg_left (reducedBound k) (norm_nonneg _)))
              (mul_le_mul_of_nonneg_left (inputBound k) (norm_nonneg _))
          _ = E := invariant
  change ‖C (drivenState A B input n) -
      reducedOutput C J
        (drivenState (reducedDynamics A P J) (reducedInput B P) input n)‖ ≤ ‖C‖ * E
  have outputIdentity :
      C (drivenState A B input n) -
          reducedOutput C J
            (drivenState (reducedDynamics A P J) (reducedInput B P) input n) =
        C (stateError A B P J input n) := by
    simp only [stateError, reducedOutput, ContinuousLinearMap.comp_apply, map_sub]
  rw [outputIdentity]
  exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (errorBound n) (norm_nonneg C))

/-- Vanishing computed residuals give exact output preservation at every time,
without a contraction assumption. -/
theorem zero_residuals_preserve_outputs
    (A : V →L[ℝ] V) (B : U →L[ℝ] V) (C : V →L[ℝ] Y)
    (P : V →L[ℝ] W) (J : W →L[ℝ] V)
    (dynamicsExact : dynamicsResidual A P J = 0)
    (inputExact : inputResidual B P J = 0) (input : ℕ → U) (n : ℕ) :
    C (drivenState A B input n) =
      reducedOutput C J
        (drivenState (reducedDynamics A P J) (reducedInput B P) input n) := by
  have bound := outputError_le_residual_sum A B C P J input n
  simp only [dynamicsExact, inputExact, norm_zero, zero_mul, add_zero,
    mul_zero, Finset.sum_const_zero] at bound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm bound (norm_nonneg _)))

#print axioms stateError_succ
#print axioms outputError_le_residual_sum
#print axioms outputError_uniform_of_contraction
#print axioms zero_residuals_preserve_outputs

end D5.S3.Observer.Hankel.ProjectedRealizationError

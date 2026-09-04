/- GID: D5/S3/Quantum/Tomography/MUBCompletionPositivstellensatzCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionPositivstellensatzCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact SOS and semialgebraic identities certify positive three-frame-potential margins and therefore exclude fixed-edge double completions. -/

import D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential

/- Library-search audit trail (2026-09-04):
   * Repository searches for Positivstellensatz, SOS certificate, polynomial
     infeasibility certificate, and Gram certificate found no reusable checker.
   * The theorem is stated at the evaluation level. External SDP, Gröbner, or
     elimination software may discover coefficient functions, while Lean only
     trusts the exact identity, equality constraints, and sign hypotheses.
   * Reuses `no_doubleCompletion_of_threeFramePotential_margin`; no second MUB
     feasibility predicate or potential is introduced.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionPositivstellensatzCertificate

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential

/-- Evaluation-level Positivstellensatz margin checker.

An identity

`objective - epsilon = sum squares + sum q_i f_i + sum t_j g_j`

proves `objective >= epsilon` on the semialgebraic set `f_i = 0`, `g_j >= 0`
when every inequality multiplier `t_j` is nonnegative. -/
theorem lower_bound_of_sos_semialgebraic_identity
    {α equationIndex inequalityIndex squareIndex : Type*}
    [Fintype equationIndex] [Fintype inequalityIndex] [Fintype squareIndex]
    (objective : α → ℝ) (epsilon : ℝ)
    (equation : equationIndex → α → ℝ)
    (inequality : inequalityIndex → α → ℝ)
    (squareTerm : squareIndex → α → ℝ)
    (equationMultiplier : equationIndex → α → ℝ)
    (inequalityMultiplier : inequalityIndex → α → ℝ)
    (hIdentity : ∀ x,
      objective x - epsilon =
        (∑ k, (squareTerm k x) ^ 2) +
        (∑ i, equationMultiplier i x * equation i x) +
        ∑ j, inequalityMultiplier j x * inequality j x)
    (hMultiplierNonneg : ∀ x j, 0 ≤ inequalityMultiplier j x)
    (x : α)
    (hEquation : ∀ i, equation i x = 0)
    (hInequality : ∀ j, 0 ≤ inequality j x) :
    epsilon ≤ objective x := by
  have hSquares : 0 ≤ ∑ k, (squareTerm k x) ^ 2 :=
    Finset.sum_nonneg fun k hk ↦ sq_nonneg (squareTerm k x)
  have hEquationSum :
      (∑ i, equationMultiplier i x * equation i x) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hEquation i, mul_zero]
  have hInequalitySum :
      0 ≤ ∑ j, inequalityMultiplier j x * inequality j x :=
    Finset.sum_nonneg fun j hj ↦
      mul_nonneg (hMultiplierNonneg x j) (hInequality j)
  rw [hIdentity x, hEquationSum]
  linarith

/-- The special `-1` identity excludes every point of the represented
semialgebraic set. -/
theorem no_feasible_point_of_neg_one_sos_identity
    {α equationIndex inequalityIndex squareIndex : Type*}
    [Fintype equationIndex] [Fintype inequalityIndex] [Fintype squareIndex]
    (equation : equationIndex → α → ℝ)
    (inequality : inequalityIndex → α → ℝ)
    (squareTerm : squareIndex → α → ℝ)
    (equationMultiplier : equationIndex → α → ℝ)
    (inequalityMultiplier : inequalityIndex → α → ℝ)
    (hIdentity : ∀ x,
      (-1 : ℝ) =
        (∑ k, (squareTerm k x) ^ 2) +
        (∑ i, equationMultiplier i x * equation i x) +
        ∑ j, inequalityMultiplier j x * inequality j x)
    (hMultiplierNonneg : ∀ x j, 0 ≤ inequalityMultiplier j x) :
    ¬ ∃ x : α,
      (∀ i, equation i x = 0) ∧
      ∀ j, 0 ≤ inequality j x := by
  rintro ⟨x, hEquation, hInequality⟩
  have hBound :=
    lower_bound_of_sos_semialgebraic_identity
      (fun _ : α ↦ (0 : ℝ)) 1
      equation inequality squareTerm equationMultiplier inequalityMultiplier
      (fun y ↦ by simpa using hIdentity y)
      hMultiplierNonneg x hEquation hInequality
  norm_num at hBound

/-- A branch-specific Positivstellensatz identity for the exact three-frame
potential excludes fixed-edge double completion.

The branch compiler supplies equality and inequality constraints that hold for
every scaled-Hadamard relative Gram in the branch. Lean checks only the exact
identity and signs, then applies the already proved potential-margin theorem. -/
theorem no_doubleCompletion_of_threeFramePotential_positivstellensatz
    {n equationIndex inequalityIndex squareIndex : Type*}
    [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype equationIndex] [Fintype inequalityIndex] [Fintype squareIndex]
    (H X Y : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (equation : equationIndex → ComplexSquare n → ℝ)
    (inequality : inequalityIndex → ComplexSquare n → ℝ)
    (squareTerm : squareIndex → ComplexSquare n → ℝ)
    (equationMultiplier : equationIndex → ComplexSquare n → ℝ)
    (inequalityMultiplier : inequalityIndex → ComplexSquare n → ℝ)
    (hIdentity : ∀ P,
      completionThreeFramePotential X Y P - epsilon =
        (∑ k, (squareTerm k P) ^ 2) +
        (∑ i, equationMultiplier i P * equation i P) +
        ∑ j, inequalityMultiplier j P * inequality j P)
    (hMultiplierNonneg : ∀ P j, 0 ≤ inequalityMultiplier j P)
    (hEquationOnBranch : ∀ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) →
      P * Pᴴ =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
          (1 : ComplexSquare n) →
      ∀ i, equation i P = 0)
    (hInequalityOnBranch : ∀ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) →
      P * Pᴴ =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
          (1 : ComplexSquare n) →
      ∀ j, 0 ≤ inequality j P) :
    ¬ ∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ) := by
  apply no_doubleCompletion_of_threeFramePotential_margin
    H X Y hH hX hY epsilon hEpsilon
  intro P hPFlat hPGram
  exact lower_bound_of_sos_semialgebraic_identity
    (completionThreeFramePotential X Y) epsilon
    equation inequality squareTerm equationMultiplier inequalityMultiplier
    hIdentity hMultiplierNonneg P
    (hEquationOnBranch P hPFlat hPGram)
    (hInequalityOnBranch P hPFlat hPGram)

#print axioms lower_bound_of_sos_semialgebraic_identity
#print axioms no_feasible_point_of_neg_one_sos_identity
#print axioms no_doubleCompletion_of_threeFramePotential_positivstellensatz

end D5.S3.Quantum.Tomography.MUBCompletionPositivstellensatzCertificate

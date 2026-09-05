/- GID: D5/S3/Quantum/Bogoliubov/HankelBogoliubovLift
   generality: G
   mirror-B: D5/B/S3/Quantum/Bogoliubov/HankelBogoliubovLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite contractive singular-value families admit the canonical Bogoliubov lift. -/

import D5.S3.Quantum.Bogoliubov.BogoliubovNormConservation
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Bogoliubov.HankelBogoliubovLift

open scoped BigOperators

/-! A finite singular-value family is represented by a function on `Fin n`.
The diagonal matrices below are the finite-dimensional coefficient operators. -/

def alpha {n : ℕ} (sigma : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.cosh (Real.artanh (sigma j))

def beta {n : ℕ} (sigma : Fin n → ℝ) (j : Fin n) : ℝ :=
  Real.sinh (Real.artanh (sigma j))

def alphaMatrix {n : ℕ} (sigma : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (alpha sigma)

def betaMatrix {n : ℕ} (sigma : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (beta sigma)

def particleNumber {n : ℕ} (sigma : Fin n → ℝ) (j : Fin n) : ℝ :=
  beta sigma j ^ 2

theorem hankel_bogoliubov_lift
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ : ∀ j, 0 ≤ sigma j ∧ sigma j < 1) :
    Matrix.transpose (alphaMatrix sigma) * alphaMatrix sigma -
          Matrix.transpose (betaMatrix sigma) * betaMatrix sigma =
        (1 : Matrix (Fin n) (Fin n) ℝ) ∧
      (∀ j, |alpha sigma j| = 1 / Real.sqrt (1 - sigma j ^ 2)) ∧
      (∀ j, |beta sigma j| = sigma j / Real.sqrt (1 - sigma j ^ 2)) ∧
      (∀ j, particleNumber sigma j = sigma j ^ 2 / (1 - sigma j ^ 2)) := by
  have hσmem : ∀ j, sigma j ∈ Set.Ioo (-1 : ℝ) 1 := by
    intro j
    exact ⟨by linarith [hσ j |>.1], hσ j |>.2⟩
  have hdenpos : ∀ j, 0 < 1 - sigma j ^ 2 := by
    intro j
    nlinarith [hσ j |>.1, hσ j |>.2]
  have halpha : ∀ j, |alpha sigma j| = 1 / Real.sqrt (1 - sigma j ^ 2) := by
    intro j
    unfold alpha
    rw [Real.cosh_artanh (hσmem j)]
    exact abs_of_pos
      (div_pos (by norm_num) (Real.sqrt_pos.2 (hdenpos j)))
  have hbeta : ∀ j, |beta sigma j| = sigma j / Real.sqrt (1 - sigma j ^ 2) := by
    intro j
    unfold beta
    rw [Real.sinh_artanh (hσmem j), abs_of_nonneg]
    exact div_nonneg (hσ j |>.1) (Real.sqrt_nonneg _)
  have hccr : ∀ j, alpha sigma j ^ 2 - beta sigma j ^ 2 = 1 := by
    intro j
    simpa only [alpha, beta] using
      Real.cosh_sq_sub_sinh_sq (Real.artanh (sigma j))
  have hmatrix :
      Matrix.transpose (alphaMatrix sigma) * alphaMatrix sigma -
          Matrix.transpose (betaMatrix sigma) * betaMatrix sigma =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [show Matrix.transpose (alphaMatrix sigma) = alphaMatrix sigma by
      simp [alphaMatrix, Matrix.diagonal_transpose],
      show Matrix.transpose (betaMatrix sigma) = betaMatrix sigma by
      simp [betaMatrix, Matrix.diagonal_transpose]]
    rw [show alphaMatrix sigma * alphaMatrix sigma =
        Matrix.diagonal (fun i => alpha sigma i * alpha sigma i) by
      simp [alphaMatrix, Matrix.diagonal_mul_diagonal],
      show betaMatrix sigma * betaMatrix sigma =
        Matrix.diagonal (fun i => beta sigma i * beta sigma i) by
      simp [betaMatrix, Matrix.diagonal_mul_diagonal]]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.diagonal_apply_eq, pow_two] using hccr i
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply, hij]
  refine ⟨hmatrix, halpha, hbeta, ?_⟩
  intro j
  unfold particleNumber
  have hbetaSq : beta sigma j ^ 2 =
      (sigma j / Real.sqrt (1 - sigma j ^ 2)) ^ 2 := by
    rw [← sq_abs, hbeta j]
  rw [hbetaSq]
  have hsqrt : (Real.sqrt (1 - sigma j ^ 2)) ^ 2 = 1 - sigma j ^ 2 :=
    Real.sq_sqrt (le_of_lt (hdenpos j))
  field_simp [ne_of_gt (hdenpos j), ne_of_gt (Real.sqrt_pos.2 (hdenpos j))]
  nlinarith

#print axioms hankel_bogoliubov_lift

end D5.S3.Quantum.Bogoliubov.HankelBogoliubovLift

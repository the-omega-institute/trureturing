/- GID: D5/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/FiniteSignedNormalAtomicLocalizingCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite positive atomic moments separate mass positivity from signed support localization. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import D5.S3.Weil.ZetaLinear.Sylvester
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches for `FiniteSignedNormalAtomicLocalizingCone`,
     `SignedNormalSpectralAtom`, `LocalizingPolynomialWitness`, and finite
     atomic localizing matrices found theory targets and digestion records but
     no Lean owner on `dev`.
   * `ReflectedGrowthPairNegativeSquare` already owns the signed normal
     coordinate `reflectionPairSignedDeterminant delta = -delta^2`; the
     specialization below imports that declaration rather than defining a
     second normal coordinate.
   * `FiniteVandermondeTomography` already owns injectivity and the nonzero
     determinant of a Vandermonde matrix at distinct nodes. The interpolation
     witness below reuses its determinant theorem together with Mathlib's
     `Matrix.cramer` and `Matrix.mulVec_cramer`.
   * `RHLinalg.hermForm`, `Matrix.PosSemidef.diagonal`,
     `Matrix.PosSemidef.conjTranspose_mul_mul_same`, and
     `RHLinalg.hermForm_nonneg_of_posSemidef` provide the quadratic-form and
     positivity interfaces. No parallel PSD or negative-direction notion is
     introduced.
   * The result is finite and atomic. It does not construct the completed-xi
     normal measure, control analytic tails, or prove RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset

namespace D5.S3.Analytic.ReflectedSpectrum.FiniteSignedNormalAtomicLocalizingCone

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open RHLinalg

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Evaluation of the first `depth` monomials at a finite family of real
support nodes. -/
def atomicEvaluationMatrix (support : Atom → ℝ) (depth : ℕ) :
    Matrix Atom (Fin depth) ℝ :=
  Matrix.rectVandermonde support (fun _ => 1) depth

/-- A finite atomic moment matrix with arbitrary real atom weights. -/
def finiteAtomicMomentMatrix
    (support weight : Atom → ℝ) (depth : ℕ) :
    Matrix (Fin depth) (Fin depth) ℝ :=
  (atomicEvaluationMatrix support depth)ᴴ *
    Matrix.diagonal weight *
      atomicEvaluationMatrix support depth

/-- The ordinary Hankel moment matrix of a finite atomic measure. -/
def finiteAtomicHankelMatrix
    (support mass : Atom → ℝ) (depth : ℕ) :
    Matrix (Fin depth) (Fin depth) ℝ :=
  finiteAtomicMomentMatrix support mass depth

/-- The first support-localizing matrix, whose atom weights are `mass * support`. -/
def finiteAtomicShiftedLocalizingMatrix
    (support mass : Atom → ℝ) (depth : ℕ) :
    Matrix (Fin depth) (Fin depth) ℝ :=
  finiteAtomicMomentMatrix support (fun atom => mass atom * support atom) depth

/-- The rectangular evaluation matrix really evaluates monomials. -/
theorem atomic_evaluation_matrix_apply
    (support : Atom → ℝ) (depth : ℕ) (atom : Atom) (degree : Fin depth) :
    atomicEvaluationMatrix support depth atom degree =
      support atom ^ (degree : ℕ) := by
  simp [atomicEvaluationMatrix, Matrix.rectVandermonde_apply]

/-- Nonnegative atomic weights give a positive semidefinite moment matrix. -/
theorem finite_atomic_moment_matrix_posSemidef
    (support weight : Atom → ℝ) (depth : ℕ)
    (hweight : ∀ atom, 0 ≤ weight atom) :
    (finiteAtomicMomentMatrix support weight depth).PosSemidef := by
  unfold finiteAtomicMomentMatrix
  exact (Matrix.PosSemidef.diagonal hweight).conjTranspose_mul_mul_same _

/-- Positive masses make the ordinary Hankel matrix positive semidefinite,
independently of the signs of the support nodes. -/
theorem finite_atomic_hankel_posSemidef
    (support mass : Atom → ℝ) (depth : ℕ)
    (hmass : ∀ atom, 0 ≤ mass atom) :
    (finiteAtomicHankelMatrix support mass depth).PosSemidef := by
  simpa [finiteAtomicHankelMatrix] using
    finite_atomic_moment_matrix_posSemidef support mass depth hmass

/-- Positive masses on nonnegative support make the first shifted localizing
matrix positive semidefinite. -/
theorem finite_atomic_shifted_localizing_posSemidef_of_nonnegative_support
    (support mass : Atom → ℝ) (depth : ℕ)
    (hmass : ∀ atom, 0 ≤ mass atom)
    (hsupport : ∀ atom, 0 ≤ support atom) :
    (finiteAtomicShiftedLocalizingMatrix support mass depth).PosSemidef := by
  unfold finiteAtomicShiftedLocalizingMatrix
  apply finite_atomic_moment_matrix_posSemidef
  intro atom
  exact mul_nonneg (hmass atom) (hsupport atom)

/-- At matching atom count and moment depth, the generic evaluation matrix is
Mathlib's square Vandermonde matrix. -/
theorem atomic_evaluation_matrix_eq_vandermonde
    {n : ℕ} (support : Fin n → ℝ) :
    atomicEvaluationMatrix support n = Matrix.vandermonde support := by
  ext atom degree
  simp [atomicEvaluationMatrix, Matrix.rectVandermonde_apply]

/-- Coefficients of the polynomial that is one at `target` and zero at every
other supplied support node. The determinant normalization is total; the
interpolation theorem below assumes distinct nodes. -/
def lagrangeIsolationCoefficients
    {n : ℕ} (support : Fin n → ℝ) (target : Fin n) : Fin n → ℝ :=
  ((Matrix.vandermonde support).det)⁻¹ •
    Matrix.cramer (Matrix.vandermonde support) (Pi.single target 1)

/-- Distinct support nodes make the Cramer coefficients an exact point-isolating
polynomial evaluation vector. -/
theorem lagrange_isolation_evaluation
    {n : ℕ} {support : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective support) :
    atomicEvaluationMatrix support n *ᵥ
        lagrangeIsolationCoefficients support target =
      Pi.single target 1 := by
  rw [atomic_evaluation_matrix_eq_vandermonde]
  unfold lagrangeIsolationCoefficients
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer]
  have hdet : (Matrix.vandermonde support).det ≠ 0 :=
    vandermonde_det_ne_zero_of_injective hsupport
  ext atom
  simp [hdet]

private theorem hermForm_diagonal_single
    {n : ℕ} (weight : Fin n → ℝ) (target : Fin n) :
    hermForm (Matrix.diagonal weight) (Pi.single target 1) = weight target := by
  unfold hermForm
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.diagonal_apply,
    Finset.mul_sum, mul_ite, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- A vector whose evaluations isolate one atom reads exactly that atom's
weight from the congruence moment matrix. -/
theorem finite_atomic_moment_matrix_isolated_readout
    {n : ℕ} (support weight : Fin n → ℝ) (target : Fin n)
    (coefficients : Fin n → ℝ)
    (hevaluation :
      atomicEvaluationMatrix support n *ᵥ coefficients =
        Pi.single target 1) :
    hermForm (finiteAtomicMomentMatrix support weight n) coefficients =
      weight target := by
  unfold finiteAtomicMomentMatrix
  rw [hermForm_conj, hevaluation]
  exact hermForm_diagonal_single weight target

/-- The first shifted localizing matrix evaluated on the Lagrange isolator is
exactly `mass target * support target`. -/
theorem finite_atomic_shifted_localizing_lagrange_readout
    {n : ℕ} {support mass : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective support) :
    hermForm (finiteAtomicShiftedLocalizingMatrix support mass n)
        (lagrangeIsolationCoefficients support target) =
      mass target * support target := by
  unfold finiteAtomicShiftedLocalizingMatrix
  apply finite_atomic_moment_matrix_isolated_readout
  exact lagrange_isolation_evaluation target hsupport

/-- A positive-mass atom at a strictly negative, distinct support node gives an
explicit finite negative direction for the shifted localizing matrix. -/
theorem finite_atomic_negative_support_witness
    {n : ℕ} {support mass : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective support)
    (hmass : 0 < mass target)
    (hnegative : support target < 0) :
    hermForm (finiteAtomicShiftedLocalizingMatrix support mass n)
        (lagrangeIsolationCoefficients support target) < 0 := by
  rw [finite_atomic_shifted_localizing_lagrange_readout target hsupport]
  exact mul_neg_of_pos_of_neg hmass hnegative

/-- The explicit negative readout proves failure of support-localizing
positive semidefiniteness. -/
theorem finite_atomic_shifted_localizing_not_posSemidef
    {n : ℕ} {support mass : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective support)
    (hmass : 0 < mass target)
    (hnegative : support target < 0) :
    ¬(finiteAtomicShiftedLocalizingMatrix support mass n).PosSemidef := by
  intro hpsd
  have hnonnegative := hermForm_nonneg_of_posSemidef hpsd
    (lagrangeIsolationCoefficients support target)
  have hstrict := finite_atomic_negative_support_witness target hsupport hmass hnegative
  linarith

/-- The finite cone separation package: positive mass guarantees ordinary
Hankel positivity, while a distinct negative support atom is isolated by a
finite polynomial and forces the shifted localizing matrix outside its PSD
cone. -/
theorem finite_signed_normal_atomic_localizing_cone
    {n : ℕ} {support mass : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective support)
    (hmass_nonnegative : ∀ atom, 0 ≤ mass atom)
    (hmass_target : 0 < mass target)
    (hnegative : support target < 0) :
    (finiteAtomicHankelMatrix support mass n).PosSemidef ∧
      hermForm (finiteAtomicShiftedLocalizingMatrix support mass n)
          (lagrangeIsolationCoefficients support target) < 0 ∧
      ¬(finiteAtomicShiftedLocalizingMatrix support mass n).PosSemidef := by
  exact ⟨finite_atomic_hankel_posSemidef support mass n hmass_nonnegative,
    finite_atomic_negative_support_witness target hsupport hmass_target hnegative,
    finite_atomic_shifted_localizing_not_posSemidef target hsupport hmass_target hnegative⟩

/-- Specialization to the repository's signed normal support
`reflectionPairSignedDeterminant delta = -delta^2`. The injectivity hypothesis
means atoms are already indexed by distinct reflection-orbit support values. -/
theorem reflected_signed_normal_atomic_localizing_certificate
    {n : ℕ} {delta mass : Fin n → ℝ} (target : Fin n)
    (hsupport : Function.Injective
      (fun atom => reflectionPairSignedDeterminant (delta atom)))
    (hmass_nonnegative : ∀ atom, 0 ≤ mass atom)
    (hmass_target : 0 < mass target)
    (hdelta : delta target ≠ 0) :
    (finiteAtomicHankelMatrix
        (fun atom => reflectionPairSignedDeterminant (delta atom)) mass n).PosSemidef ∧
      hermForm
          (finiteAtomicShiftedLocalizingMatrix
            (fun atom => reflectionPairSignedDeterminant (delta atom)) mass n)
          (lagrangeIsolationCoefficients
            (fun atom => reflectionPairSignedDeterminant (delta atom)) target) < 0 ∧
      ¬(finiteAtomicShiftedLocalizingMatrix
          (fun atom => reflectionPairSignedDeterminant (delta atom)) mass n).PosSemidef := by
  apply finite_signed_normal_atomic_localizing_cone target hsupport
    hmass_nonnegative hmass_target
  rw [(reflection_pair_signed_determinant (delta target) 0).2.1]
  exact neg_lt_zero.mpr (sq_pos_of_ne_zero hdelta)

/-- A two-atom example showing that ordinary moment positivity can coexist with
a support-localizing negative direction. -/
example :
    let support : Fin 2 → ℝ := ![-1, 2]
    let mass : Fin 2 → ℝ := ![1, 1]
    (finiteAtomicHankelMatrix support mass 2).PosSemidef ∧
      ¬(finiteAtomicShiftedLocalizingMatrix support mass 2).PosSemidef := by
  dsimp
  have hsupport : Function.Injective (![(-1 : ℝ), 2] : Fin 2 → ℝ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; norm_num at hij)
  have hcertificate := finite_signed_normal_atomic_localizing_cone
    (support := (![(-1 : ℝ), 2] : Fin 2 → ℝ))
    (mass := (![1, 1] : Fin 2 → ℝ)) 0 hsupport
    (by intro atom; fin_cases atom <;> norm_num)
    (by norm_num) (by norm_num)
  exact ⟨hcertificate.1, hcertificate.2.2⟩

#print axioms finite_atomic_hankel_posSemidef
#print axioms lagrange_isolation_evaluation
#print axioms finite_atomic_negative_support_witness
#print axioms finite_signed_normal_atomic_localizing_cone
#print axioms reflected_signed_normal_atomic_localizing_certificate

end D5.S3.Analytic.ReflectedSpectrum.FiniteSignedNormalAtomicLocalizingCone

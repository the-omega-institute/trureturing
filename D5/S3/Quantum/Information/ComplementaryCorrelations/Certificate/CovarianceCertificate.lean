/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceMatrixAdapter.physical_posSemidef; instance=D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceCertificate.covariance_posSemidef
   digest: Exact polynomial and shifted Gram checks give a positive semidefinite qutrit covariance matrix. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificateDataA
import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificateDataB
import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificateDataC
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
The qutrit covariance certificate for Qian ACC₂×₃, §11(1).
The finite checks reconstruct the shifted Gram matrices and compare all sixteen
covariance entries as exact quartic polynomials. The matrix theorem consumes both checks.
-/

set_option autoImplicit false
open Matrix
open scoped BigOperators ComplexOrder

namespace QianACC.CovarianceCertificate

def block (w : Weight) : Block :=
  ![block00, block01, block02, block10, block11, block12, block20, block21, block22] w

def shift (n : ℕ) : Matrix (Fin n) (Fin n) Coeff :=
  Matrix.diagonal fun _ => rat (1 / 5)

def shiftedGram (B : Block) : Matrix (Fin B.dim) (Fin B.dim) Coeff :=
  B.gram - shift B.dim

def ldlEntry (B : Block) (i j : Fin B.dim) : Coeff :=
  sumFin fun k : Fin B.dim => B.lower i k * rat (B.pivots k) * star (B.lower j k)

private def allFin {n : ℕ} (p : Fin n → Bool) : Bool := (List.finRange n).all p

private theorem allFin_eq_true {n : ℕ} {p : Fin n → Bool} :
    allFin p = true ↔ ∀ i, p i = true := by
  simp [allFin]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ldl_entries (w : Weight) :
    ∀ i j, shiftedGram (block w) i j = ldlEntry (block w) i j := by
  have checked : allFin (fun i => allFin fun j =>
      decide (shiftedGram (block w) i j = ldlEntry (block w) i j)) = true := by
    fin_cases w <;> decide +kernel
  simpa only [allFin_eq_true, decide_eq_true_eq] using checked

theorem pivots_pos (w : Weight) : ∀ i, 0 < (block w).pivots i := by
  fin_cases w <;> decide +kernel

private theorem shiftedGram_eq_ldl (B : Block)
    (h : ∀ i j, shiftedGram B i j = ldlEntry B i j) :
    shiftedGram B = B.lower * Matrix.diagonal (fun i => rat (B.pivots i)) * B.lowerᴴ := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  exact (h i j).trans (sumFin_eq _)

private theorem lower_triangular (w : Weight) :
    ∀ i j : Fin (block w).dim, i < j → (block w).lower i j = 0 := by
  have checked : allFin (fun i => allFin fun j =>
      decide (i < j → (block w).lower i j = 0)) = true := by
    fin_cases w <;> decide +kernel
  simpa only [allFin_eq_true, decide_eq_true_eq] using checked

private theorem lower_diagonal (w : Weight) :
    ∀ i : Fin (block w).dim, (block w).lower i i = 1 := by
  fin_cases w <;> decide +kernel

/-- All nine shifted Gram matrices have exact positive pivots and a unit lower factor. -/
theorem shifted_gram_posDef (w : Weight) :
    (complexMatrix (shiftedGram (block w))).PosDef := by
  rw [shiftedGram_eq_ldl _ (ldl_entries w), complexMatrix_mul, complexMatrix_mul,
    complexMatrix_diag, complexMatrix_adjoint]
  have htri : (complexMatrix (block w).lower).IsLowerTriangular := by
    intro i j hij
    change toComplex ((block w).lower i j) = 0
    rw [lower_triangular w i j hij, map_zero]
  have hdet : (complexMatrix (block w).lower).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    change ∏ i : Fin (block w).dim, toComplex ((block w).lower i i) = 1
    simp [lower_diagonal w]
  have hdiag : (Matrix.diagonal (fun i : Fin (block w).dim =>
      (((block w).pivots i : ℝ) : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    exact_mod_cast pivots_pos w i
  apply hdiag.mul_mul_conjTranspose_same
  apply Matrix.vecMul_injective_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det (complexMatrix (block w).lower)).mpr
  rw [hdet]
  exact isUnit_one

private theorem gram_posSemidef (w : Weight) : (complexMatrix (block w).gram).PosSemidef := by
  have hshift : (complexMatrix (shift (block w).dim)).PosSemidef := by
    rw [shift, complexMatrix_diag]
    exact Matrix.PosSemidef.diagonal (fun _ => Complex.zero_le_real.mpr (by norm_num))
  have hsplit : complexMatrix (block w).gram =
      complexMatrix (shiftedGram (block w)) + complexMatrix (shift (block w).dim) := by
    apply Matrix.ext
    intro i j
    simp [complexMatrix, shiftedGram, Matrix.sub_apply, Matrix.add_apply]
  rw [hsplit]
  exact (shifted_gram_posDef w).posSemidef.add hshift

/-- A rational entry of N Y Nᴴ. Skip zero basis entries before doing arithmetic. -/
def gramEntry (B : Block) (i j : TermIndex) : Coeff :=
  sumFin fun k : Fin B.dim =>
    if B.basis i k = 0 then 0 else
      sumFin fun l : Fin B.dim =>
        if B.basis j l = 0 then 0 else
          B.basis i k * B.gram k l * star (B.basis j l)

private theorem gramEntry_eq (B : Block) (i j : TermIndex) :
    gramEntry B i j = (B.basis * B.gram * B.basisᴴ) i j := by
  calc
    gramEntry B i j =
        ∑ k : Fin B.dim, ∑ l : Fin B.dim, B.basis i k * B.gram k l * star (B.basis j l) := by
      simp only [gramEntry, sumFin_eq]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : B.basis i k = 0
      · simp [hk]
      · simp only [ite_eq_right hk]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : B.basis j l = 0 <;> simp [hl]
    _ = (B.basis * B.gram * B.basisᴴ) i j := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      exact Finset.sum_comm

private def gramTerm (w : Weight) (a b : Test) (i j : TermIndex) : Polynomial.Term :=
  let p := monomial w i
  let q := monomial w j
  ([negWeight p.left, negWeight p.right, q.left, q.right],
    if p.test = a ∧ q.test = b then gramEntry (block w) i j else 0)

def gramTerms (a b : Test) : Polynomial.Terms :=
  (List.finRange 9).flatMap fun w =>
    (List.finRange 20).flatMap fun i => (List.finRange 20).map (gramTerm w a b i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem coefficient_equality (a b : Test) :
    Polynomial.normalize (targetTerms a b) = Polynomial.normalize (gramTerms a b) := by
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Evaluation of the degree-two monomials with their four test directions. -/
noncomputable def monomialMatrix (x : Weight → ℂ) (w : Weight) :
    Matrix TermIndex Test ℂ :=
  fun i a =>
    let p := monomial w i
    if p.test = a then x p.left * x p.right else 0

/-- The block contribution Pᴴ N Y Nᴴ P, using P for the degree-two monomials. -/
noncomputable def gramForm (x : Weight → ℂ) (w : Weight) : Matrix Test Test ℂ :=
  let B := block w
  let N := complexMatrix B.basis
  let P := monomialMatrix x w
  Pᴴ * (N * complexMatrix B.gram * Nᴴ) * P

private theorem eval_gramTerm (x : Weight → ℂ) (hx : ∀ g, star (x g) = x (negWeight g))
    (w : Weight) (a b : Test) (i j : TermIndex) :
    Polynomial.evalTerm x (gramTerm w a b i j) =
      star (monomialMatrix x w i a) *
        (complexMatrix (block w).basis * complexMatrix (block w).gram *
          (complexMatrix (block w).basis)ᴴ) i j * monomialMatrix x w j b := by
  have hentry : toComplex (gramEntry (block w) i j) =
      (complexMatrix (block w).basis * complexMatrix (block w).gram *
        (complexMatrix (block w).basis)ᴴ) i j := by
    rw [← complexMatrix_adjoint, ← complexMatrix_mul, ← complexMatrix_mul]
    exact congrArg toComplex (gramEntry_eq (block w) i j)
  by_cases hi : (monomial w i).test = a <;> by_cases hj : (monomial w j).test = b
  all_goals
    simp [gramTerm, monomialMatrix, Polynomial.evalTerm, Polynomial.evalKey, hi, hj,
      hentry, star_mul, hx]
    all_goals ac_rfl

private theorem eval_gramTerms (x : Weight → ℂ) (hx : ∀ g, star (x g) = x (negWeight g))
    (a b : Test) : Polynomial.eval x (gramTerms a b) = (∑ w : Weight, gramForm x w) a b := by
  rw [gramTerms, Polynomial.eval_flatMap]
  simp only [Polynomial.eval_flatMap, Polynomial.eval_map, eval_gramTerm x hx,
    ← Fin.sum_univ_def, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  simp only [gramForm, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Exact polynomial certificate after imposing the Hermitian Weyl-coordinate relation. -/
theorem covariance_eq_sum_gram (x : Weight → ℂ)
    (hx : ∀ g, star (x g) = x (negWeight g)) :
    covarianceMatrix x = ∑ w : Weight, gramForm x w := by
  apply Matrix.ext
  intro a b
  rw [← eval_targetTerms x a b, ← eval_gramTerms x hx a b]
  exact Polynomial.eval_eq_of_normalize_eq (coefficient_equality a b) x

/-- Certificate interface for the physical covariance argument. It includes `x = 0`. -/
theorem covariance_posSemidef (x : Weight → ℂ)
    (hx : ∀ g, star (x g) = x (negWeight g)) :
    (covarianceMatrix x).PosSemidef := by
  rw [covariance_eq_sum_gram x hx]
  apply Matrix.posSemidef_sum
  intro w _
  have h := (gram_posSemidef w).mul_mul_conjTranspose_same (complexMatrix (block w).basis)
  exact h.conjTranspose_mul_mul_same (monomialMatrix x w)

end QianACC.CovarianceCertificate

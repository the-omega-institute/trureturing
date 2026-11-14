/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/Polynomial
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/Polynomial
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Subresultant/Polynomial.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Subresultant.Basic
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Polynomial.Coeff.Basic
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.GroupTheory.Perm.Inversion

/-!
# Subresultant polynomials

This file defines the fixed-bound subresultant polynomial of two polynomials.  At a strict index
`j < min m n`, its coefficient of degree `k ≤ j` is the Sylvester minor obtained by replacing the
first row of the principal subresultant matrix at index `j` by the row of coefficients of degree
`k`; in particular, its coefficient of degree `j` is the principal subresultant coefficient.
Outside the strict range the minors remain scalar data (for instance the terminal empty
determinant recorded by `psc`), and the subresultant polynomial is zero.

The construction retains explicit degree bounds, so it commutes with coefficient maps even when
specialization lowers the degrees.  Its degree bound and top coefficient identify the scalar minor
that controls the subresultant gcd criterion.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 4.
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3.
-/

public section

namespace Polynomial

open TauCeti

variable {R S : Type*}

/-- The coefficient matrix whose determinant is the coefficient of degree `k` in the subresultant
polynomial at a strict index `j < min m n` and formal degree bounds `m` and `n`.  The matrix is
defined for all indices; outside the strict range its determinant is only scalar data.

The first row of `subresultantMatrix p q m n j`, which reads coefficients of degree `j`, is
replaced by the row reading coefficients of degree `k`.  Applications use `k ≤ j`. -/
def subresultantCoeffMatrix [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    Matrix (Fin ((m - j) + (n - j))) (Fin ((m - j) + (n - j))) R :=
  Matrix.of fun i l =>
    let d := if i.val = 0 then k else i.val + j
    l.addCases
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0)
      (fun l => if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0)

/-- An entry in the first, `q`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem subresultantCoeffMatrix_castAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (m - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.castAdd (n - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + n then q.coeff (d - l.val) else 0 := by
  simp [subresultantCoeffMatrix]

/-- An entry in the second, `p`-column block of a subresultant coefficient matrix. -/
@[simp]
theorem subresultantCoeffMatrix_natAdd [Semiring R]
    (p q : R[X]) (m n j k : ℕ) (i : Fin ((m - j) + (n - j))) (l : Fin (n - j)) :
    subresultantCoeffMatrix p q m n j k i (Fin.natAdd (m - j) l) =
      let d := if i.val = 0 then k else i.val + j
      if (l : ℕ) ≤ d ∧ d ≤ l.val + m then p.coeff (d - l.val) else 0 := by
  simp [subresultantCoeffMatrix]

/-- When the formal bounds dominate the input degrees, coefficient-matrix entries are
coefficients of shifted input polynomials, including the replaced first row. -/
theorem subresultantCoeffMatrix_apply_eq_coeff [Semiring R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n)
    (j k : ℕ) (i l : Fin ((m - j) + (n - j))) :
    subresultantCoeffMatrix p q m n j k i l =
      l.addCases
        (fun l => (X ^ l.val * q).coeff (if i.val = 0 then k else i.val + j))
        (fun l => (X ^ l.val * p).coeff (if i.val = 0 then k else i.val + j)) := by
  induction l using Fin.addCases <;>
    simp [subresultantCoeffMatrix, coeff_X_pow_mul_of_natDegree_le hm,
      coeff_X_pow_mul_of_natDegree_le hn]

/-- A subresultant coefficient matrix replaces the row of degree `j` of the principal
matrix by the row of degree `k`. -/
theorem subresultantCoeffMatrix_eq_updateRow [Semiring R]
    (p q : R[X]) (m n j k : ℕ)
    (i₀ : Fin ((m - j) + (n - j))) (hi₀ : i₀.val = 0) :
    subresultantCoeffMatrix p q m n j k =
      (subresultantMatrix p q m n j).updateRow i₀
        (subresultantCoeffMatrix p q m n j k i₀) := by
  ext i l
  by_cases hi : i = i₀
  · subst i
    simp
  · have hi' : i.val ≠ 0 := fun h => hi (Fin.ext (h.trans hi₀.symm))
    induction l using Fin.addCases <;> simp [Matrix.updateRow_apply, hi, hi']

/-- A subresultant coefficient matrix reads coefficients of `A * q + B * p` from the
coefficient vector of `(A, B)`. Its first row reads degree `k`; the other rows read degrees
`i.val + j`. The formal bounds dominate the actual input degrees. -/
theorem subresultantCoeffMatrix_mulVec [CommSemiring R] [DecidableEq R]
    {p q : R[X]} {m n : ℕ} (hm : p.natDegree ≤ m) (hn : q.natDegree ≤ n) (j k : ℕ)
    (v : Fin ((m - j) + (n - j)) → R) (i : Fin ((m - j) + (n - j))) :
    (subresultantCoeffMatrix p q m n j k).mulVec v i =
      (ofFn (m - j) (fun l => v (Fin.castAdd (n - j) l)) * q +
        ofFn (n - j) (fun l => v (Fin.natAdd (m - j) l)) * p).coeff
        (if i.val = 0 then k else i.val + j) :=
  coefficientRow_dotProduct hm hn (m - j) (n - j) (if i.val = 0 then k else i.val + j) v

/-- At `k = j`, the coefficient matrix is the principal subresultant matrix. -/
@[simp]
theorem subresultantCoeffMatrix_self [Semiring R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeffMatrix p q m n j j = subresultantMatrix p q m n j := by
  ext i l
  induction l using Fin.addCases <;> by_cases hi : i.val = 0 <;> simp [hi]

/-- Swapping the polynomials and bounds swaps the column blocks of every subresultant coefficient
matrix. -/
theorem subresultantCoeffMatrix_comm [Semiring R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeffMatrix p q m n j k =
      (subresultantCoeffMatrix q p n m j k).reindex
        (finCongr (add_comm (n - j) (m - j))) finAddFlip := by
  ext i l
  induction l using Fin.addCases <;> simp [subresultantCoeffMatrix, finAddFlip]

/-- The scalar minor used as the coefficient of degree `k ≤ j` in the subresultant polynomial at
a strict index `j < min m n`.  It is defined for all indices; outside the strict range it is
scalar data only (the subresultant polynomial is then zero), e.g. the empty determinant `1` at
`m = n = j = 0`. -/
def subresultantCoeff [CommRing R]
    (p q : R[X]) (m n j k : ℕ) : R :=
  (subresultantCoeffMatrix p q m n j k).det

/-- A subresultant coefficient is the determinant of its coefficient matrix. -/
theorem subresultantCoeff_def [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k = (subresultantCoeffMatrix p q m n j k).det := by
  rw [subresultantCoeff]

/-- The coefficient minor at `k = j` is the principal subresultant coefficient. -/
@[simp]
theorem subresultantCoeff_self [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    subresultantCoeff p q m n j j = psc p q m n j := by
  simp [subresultantCoeff_def, psc_def]

/-- Swapping the inputs changes every coefficient minor by the Sylvester block-swap sign. -/
theorem subresultantCoeff_comm [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    subresultantCoeff p q m n j k =
      (-1) ^ ((m - j) * (n - j)) * subresultantCoeff q p n m j k := by
  rw [subresultantCoeff_def, subresultantCoeff_def, subresultantCoeffMatrix_comm,
    Matrix.det_reindex, finCongr_symm, sign_finAddFlip_trans_finCongr, mul_comm (n - j)]
  simp

/-- The fixed-bound subresultant polynomial at index `j`.

Its coefficient of degree `k ≤ j` is `subresultantCoeff p q m n j k`; all coefficients above
`j` vanish.  This definition is the subresultant polynomial only at strict indices
`j < min m n` and returns zero outside that range; terminal data, including the empty
determinant, is represented by `psc` instead. -/
noncomputable def subresultant [CommRing R]
    (p q : R[X]) (m n j : ℕ) : R[X] := by
  classical
  exact if j < min m n then
      ofFn (j + 1) fun k => subresultantCoeff p q m n j k
    else 0

/-- The coefficient formula for a fixed-bound subresultant polynomial. -/
@[simp]
theorem coeff_subresultant [CommRing R]
    (p q : R[X]) (m n j k : ℕ) :
    (subresultant p q m n j).coeff k =
      if j < min m n ∧ k ≤ j then subresultantCoeff p q m n j k else 0 := by
  by_cases hj : j < min m n
  · by_cases hkj : k ≤ j
    · simp [subresultant, hj, hkj]
    · have hk : j + 1 ≤ k := by omega
      simp [subresultant, hj, hkj, hk]
  · simp [subresultant, hj]

/-- `subresultant` returns zero at and beyond the terminal index `min m n`. -/
@[simp]
theorem subresultant_eq_zero_of_min_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) (hj : min m n ≤ j) :
    subresultant p q m n j = 0 := by
  simp [subresultant, Nat.not_lt.mpr hj]

/-- The subresultant polynomial at index `j` has degree at most `j`. -/
theorem degree_subresultant_le [CommRing R]
    (p q : R[X]) (m n j : ℕ) :
    (subresultant p q m n j).degree ≤ j := by
  rw [degree_le_iff_coeff_zero]
  intro k hk
  simp [show ¬ k ≤ j by exact_mod_cast hk.not_ge]

end Polynomial


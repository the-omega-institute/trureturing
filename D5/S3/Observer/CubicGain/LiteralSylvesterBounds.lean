/- GID: D5/S3/Observer/CubicGain/LiteralSylvesterBounds
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/LiteralSylvesterBounds
   mirror-E: none(waiver:literal-elimination-continuation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic]
   utility: none
   digest: Weighted degree bounds for the original fixed Sylvester and linear-minor determinants. -/

import D5.S3.Observer.CubicGain.LiteralElimination
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
noncomputable section

namespace D5.S3.Observer.CubicGain.LiteralSylvesterBounds

open Polynomial
open scoped BigOperators
open D5.S3.Observer.CubicGain.SelectedRootCommonZero
open D5.S3.Observer.CubicGain.ActualMinorLift
open D5.S3.Observer.CubicGain.LiteralElimination

/-- The coefficient ring is Z[b]; the outer polynomial variable is the original r. -/
def sourcePolynomial (i : Fin 3) : Polynomial (Polynomial ℤ) :=
  ![sourceE0 (X : Polynomial ℤ),sourceE1 (X : Polynomial ℤ),sourceE2 (X : Polynomial ℤ)] i

/-- All thirty rows in the original descending-shift order, independent of specialized degree. -/
def sylvesterRow (k : Fin 2) (i : Fin 30) : Polynomial (Polynomial ℤ) :=
  if i.val < 15 then X^(14-i.val)*sourcePolynomial 0
  else X^(29-i.val)*sourcePolynomial k.succ

/-- Columns are r^29,...,1; k=0 gives R1 and k=1 gives R2. -/
def literalSylvester (k : Fin 2) : Matrix (Fin 30) (Fin 30) (Polynomial ℤ) :=
  fun i j => (sylvesterRow k i).coeff (29-j.val)

def actualResultant (k : Fin 2) : Polynomial ℤ := (literalSylvester k).det

private theorem source_r_degree (i : Fin 3) : (sourcePolynomial i).natDegree ≤ 15 := by
  fin_cases i <;>
    simp only [sourcePolynomial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons] <;>
    simp only [sourceE0,sourceE1,sourceE2] <;> compute_degree

private theorem source_coefficient_weight (i : Fin 3) (j : ℕ)
    (hj : (sourcePolynomial i).coeff j ≠ 0) :
    ((sourcePolynomial i).coeff j).natDegree+j ≤ 17 := by
  have hle : j ≤ 15 := by
    by_contra hn
    exact hj (coeff_eq_zero_of_natDegree_lt ((source_r_degree i).trans_lt (by omega)))
  fin_cases i <;> interval_cases j <;>
    simp only [sourcePolynomial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      Matrix.head_cons,Matrix.tail_cons,sourceE0,sourceE1,sourceE2,coeff_add,
      coeff_C_mul_X_pow] <;> norm_num <;> compute_degree

private theorem shifted_coefficient_weight (i : Fin 3) (s c : ℕ)
    (hc : ((X^s*sourcePolynomial i).coeff c) ≠ 0) :
    ((X^s*sourcePolynomial i).coeff c).natDegree+c ≤ 17+s := by
  rw [coeff_X_pow_mul'] at hc ⊢
  split_ifs at hc ⊢ with hs
  · have h := source_coefficient_weight i (c-s) hc
    omega
  · exact (hc rfl).elim

private theorem weighted_det_bound {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Polynomial ℤ)) (alpha gamma : n → ℕ) (B : ℕ)
    (hbalance : (∑ i, alpha i) ≤ B+∑ j, gamma j)
    (hentry : ∀ i j, M i j ≠ 0 → (M i j).natDegree+gamma j ≤ alpha i) :
    M.det.natDegree ≤ B := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro sigma _
  apply (natDegree_smul_le _ _).trans
  by_cases hz : (∏ j, M (sigma j) j) = 0
  · simp [hz]
  · have hentries : ∀ j, M (sigma j) j ≠ 0 := by
      intro j hj
      exact hz (Finset.prod_eq_zero (Finset.mem_univ j) hj)
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      hentry (sigma j) j (hentries j))
    rw [Finset.sum_add_distrib, Equiv.sum_comp sigma alpha] at hsum
    have hprod := natDegree_prod_le Finset.univ (fun j => M (sigma j) j)
    omega

private def sylvesterWeight (i : Fin 30) : ℕ :=
  if i.val < 15 then 17+(14-i.val) else 17+(29-i.val)

private theorem sylvester_entry_weight (k : Fin 2) (i j : Fin 30)
    (h : literalSylvester k i j ≠ 0) :
    (literalSylvester k i j).natDegree+(29-j.val) ≤ sylvesterWeight i := by
  unfold literalSylvester sylvesterRow at h ⊢
  unfold sylvesterWeight
  split_ifs with hi
  · exact shifted_coefficient_weight 0 (14-i.val) (29-j.val) h
  · exact shifted_coefficient_weight k.succ (29-i.val) (29-j.val) h

/-- The actual fixed Sylvester determinants have parameter degree at most 285. -/
theorem literal_resultant_degree_bound (k : Fin 2) :
    (actualResultant k).natDegree ≤ 285 := by
  apply weighted_det_bound (literalSylvester k) sylvesterWeight (fun j => 29-j.val) 285
  · decide +kernel
  · exact sylvester_entry_weight k

private def minorRow (i : Fin 28) : Polynomial (Polynomial ℤ) :=
  if i.val < 14 then X^(13-i.val)*sourcePolynomial 0
  else X^(27-i.val)*sourcePolynomial 1

private def minorMatrix (constant : Bool) : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j => (minorRow i).coeff (if j.val < 27 then 28-j.val else if constant then 0 else 1)

private def minorWeight (i : Fin 28) : ℕ :=
  if i.val < 14 then 17+(13-i.val) else 17+(27-i.val)

private theorem minor_entry_weight (constant : Bool) (i j : Fin 28)
    (h : minorMatrix constant i j ≠ 0) :
    (minorMatrix constant i j).natDegree+
      (if j.val < 27 then 28-j.val else if constant then 0 else 1) ≤ minorWeight i := by
  unfold minorMatrix minorRow at h ⊢
  unfold minorWeight
  by_cases hi : i.val < 14
  · simp only [if_pos hi] at h ⊢
    exact shifted_coefficient_weight 0 (13-i.val) _ h
  · simp only [if_neg hi] at h ⊢
    exact shifted_coefficient_weight 1 (27-i.val) _ h

/-- The original r-column minor has degree at most 252 and the constant-column minor at most 253. -/
theorem literal_minor_degree_bounds :
    actualMinorA0.natDegree ≤ 252 ∧ actualMinorC0.natDegree ≤ 253 := by
  have ha : actualMinorA0 = (minorMatrix false).det := by
    change Matrix.det (fun i j : Fin 28 => if h : j.val < 27 then
      (minorRow i).coeff (28-j.val) else (minorRow i).coeff 1) = _
    congr 1
    ext i j
    by_cases hj : j.val < 27 <;> simp [minorMatrix,hj]
  have hc : actualMinorC0 = (minorMatrix true).det := by
    change Matrix.det (fun i j : Fin 28 => if h : j.val < 27 then
      (minorRow i).coeff (28-j.val) else (minorRow i).coeff 0) = _
    congr 1
    ext i j
    by_cases hj : j.val < 27 <;> simp [minorMatrix,hj]
  constructor
  · rw [ha]
    apply weighted_det_bound (minorMatrix false) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if false then 0 else 1) 252
    · decide +kernel
    · exact minor_entry_weight false
  · rw [hc]
    apply weighted_det_bound (minorMatrix true) minorWeight
      (fun j => if j.val < 27 then 28-j.val else if true then 0 else 1) 253
    · decide +kernel
    · exact minor_entry_weight true

end D5.S3.Observer.CubicGain.LiteralSylvesterBounds

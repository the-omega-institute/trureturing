/- GID: D5/S3/Observer/CubicGain/ActualMinorLift
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/ActualMinorLift
   mirror-E: none(waiver:actual-minor-lift-continuation)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Content]
   utility: none
   digest: Actual integer determinant polynomials and primitive gcd ratio bridge for the selected source minor. -/

import D5.S3.Observer.CubicGain.SelectedRootCommonZero
import D5.S3.Observer.CubicGain.SelectedMinorNonzero
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 0
noncomputable section

namespace D5.S3.Observer.CubicGain.ActualMinorLift

open Polynomial
open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.ExactW3Center
open D5.S3.Observer.CubicGain.SourceFixedMinor

/-! The source expressions are instantiated over `Polynomial ℤ`, so the outer
polynomial variable is `r` and every coefficient is an actual polynomial in
the source parameter `b`. -/

def sourceE0Coeff : Polynomial (Polynomial ℤ) :=
  sourceE0 (R := Polynomial ℤ) (Polynomial.X : Polynomial ℤ)

def sourceE1Coeff : Polynomial (Polynomial ℤ) :=
  sourceE1 (R := Polynomial ℤ) (Polynomial.X : Polynomial ℤ)

def literalRowCoeff (i : Fin 28) : Polynomial (Polynomial ℤ) :=
  if i.val < 14 then Polynomial.X ^ (13 - i.val) * sourceE0Coeff
  else Polynomial.X ^ (27 - i.val) * sourceE1Coeff

def literalMatrixCoeff : Matrix (Fin 28) (Fin 29) (Polynomial ℤ) :=
  fun i j => (literalRowCoeff i).coeff (28 - j.val)

def fixedMinorRCoeff : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j =>
    if h : j.val < 27 then literalMatrixCoeff i ⟨j.val, by omega⟩
    else literalMatrixCoeff i ⟨27, by omega⟩

def fixedMinorCCoeff : Matrix (Fin 28) (Fin 28) (Polynomial ℤ) :=
  fun i j =>
    if h : j.val < 27 then literalMatrixCoeff i ⟨j.val, by omega⟩
    else literalMatrixCoeff i ⟨28, by omega⟩

def actualMinorA0 : Polynomial ℤ := (fixedMinorRCoeff).det
def actualMinorC0 : Polynomial ℤ := (fixedMinorCCoeff).det

def evalB (b : ℝ) : Polynomial ℤ →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) b

/-! This is the exact coefficient-level source bridge. -/
theorem literalMatrixCoeff_eval (b : ℝ) :
    literalMatrixCoeff.map (evalB b) = literalMatrix b := by
  have h0 : sourceE0Coeff.map (evalB b) = sourceE0 b := by
    simp [sourceE0Coeff, sourceE0, evalB]
  have h1 : sourceE1Coeff.map (evalB b) = sourceE1 b := by
    simp [sourceE1Coeff, sourceE1, evalB]
  ext i j
  by_cases hi : i.val < 14
  · have hrow : (literalRowCoeff i).map (evalB b) = literalRow b i := by
      simp [literalRowCoeff, literalRow, hi, h0]
    change evalB b ((literalRowCoeff i).coeff (28 - j.val)) =
      (literalRow b i).coeff (28 - j.val)
    rw [← coeff_map, hrow]
  · have hrow : (literalRowCoeff i).map (evalB b) = literalRow b i := by
      simp [literalRowCoeff, literalRow, hi, h1]
    change evalB b ((literalRowCoeff i).coeff (28 - j.val)) =
      (literalRow b i).coeff (28 - j.val)
    rw [← coeff_map, hrow]

theorem fixedMinorRCoeff_eval (b : ℝ) :
    fixedMinorRCoeff.map (evalB b) = fixedMinorR (literalMatrix b) := by
  ext i j
  change evalB b (fixedMinorRCoeff i j) = _
  by_cases hj : j.val < 27
  · simp only [fixedMinorRCoeff, hj, dif_pos]
    have h := congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i ⟨j.val, by omega⟩)
      (literalMatrixCoeff_eval b)
    simpa [fixedMinorR, literalMatrix, hj] using h
  · have hj' : j.val = 27 := by omega
    simp only [fixedMinorRCoeff, hj, dif_neg]
    have h := congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i 27)
      (literalMatrixCoeff_eval b)
    simpa [fixedMinorR, literalMatrix, hj'] using h

theorem fixedMinorCCoeff_eval (b : ℝ) :
    fixedMinorCCoeff.map (evalB b) = fixedMinorC (literalMatrix b) := by
  ext i j
  change evalB b (fixedMinorCCoeff i j) = _
  by_cases hj : j.val < 27
  · simp only [fixedMinorCCoeff, hj, dif_pos]
    have h := congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i ⟨j.val, by omega⟩)
      (literalMatrixCoeff_eval b)
    simpa [fixedMinorC, literalMatrix, hj] using h
  · have hj' : j.val = 27 := by omega
    simp only [fixedMinorCCoeff, hj, dif_neg]
    have h := congrArg (fun M : Matrix (Fin 28) (Fin 29) ℝ => M i 28)
      (literalMatrixCoeff_eval b)
    simpa [fixedMinorC, literalMatrix, hj'] using h

theorem actualMinorA0_eval (b : ℝ) :
    (actualMinorA0.map (Int.castRingHom ℝ)).eval b =
      Matrix.det (fixedMinorR (literalMatrix b)) := by
  simpa [actualMinorA0, evalB, Polynomial.eval₂_eq_eval_map] using
    (RingHom.map_det (evalB b) fixedMinorRCoeff).trans
      (congrArg Matrix.det (fixedMinorRCoeff_eval b))

theorem actualMinorC0_eval (b : ℝ) :
    (actualMinorC0.map (Int.castRingHom ℝ)).eval b =
      Matrix.det (fixedMinorC (literalMatrix b)) := by
  simpa [actualMinorC0, evalB, Polynomial.eval₂_eq_eval_map] using
    (RingHom.map_det (evalB b) fixedMinorCCoeff).trans
      (congrArg Matrix.det (fixedMinorCCoeff_eval b))

/-! The positive primitive part of the polynomial gcd divides each source
determinant. The quotient witnesses are kept existentially, so no candidate
coefficient arrays are substituted for the source determinants. -/

theorem primitiveGcd_factorization (p q : Polynomial ℤ) :
    ∃ A C : Polynomial ℤ,
      p = (gcd p q).primPart * A ∧
      q = (gcd p q).primPart * C := by
  obtain ⟨A, hA⟩ :=
    (Polynomial.primPart_dvd (gcd p q)).trans (gcd_dvd_left p q)
  obtain ⟨C, hC⟩ :=
    (Polynomial.primPart_dvd (gcd p q)).trans (gcd_dvd_right p q)
  exact ⟨A, C, hA, hC⟩

theorem actualPrimitiveGcd_eval_ne_zero_of_A0_eval_ne_zero
    {b : ℝ} (hA0 : (actualMinorA0.map (Int.castRingHom ℝ)).eval b ≠ 0) :
    ((gcd actualMinorA0 actualMinorC0).primPart.map (Int.castRingHom ℝ)).eval b ≠ 0 := by
  intro hh
  obtain ⟨A, _, hA, _⟩ := primitiveGcd_factorization actualMinorA0 actualMinorC0
  have hmap :
      (actualMinorA0.map (Int.castRingHom ℝ)).eval b =
        (((gcd actualMinorA0 actualMinorC0).primPart.map (Int.castRingHom ℝ)).eval b) *
          ((A.map (Int.castRingHom ℝ)).eval b) := by
    calc
      (actualMinorA0.map (Int.castRingHom ℝ)).eval b =
          (((gcd actualMinorA0 actualMinorC0).primPart * A).map
            (Int.castRingHom ℝ)).eval b := congrArg
              (fun p : Polynomial ℤ => (p.map (Int.castRingHom ℝ)).eval b) hA
      _ = _ := by rw [Polynomial.map_mul, Polynomial.eval_mul]
  rw [hmap, hh, zero_mul] at hA0
  exact hA0 rfl

theorem actualPrimitiveQuotientA_eval_ne_zero_of_A0_eval_ne_zero
    {b : ℝ} (hA0 : (actualMinorA0.map (Int.castRingHom ℝ)).eval b ≠ 0) :
    ∃ A C : Polynomial ℤ,
      actualMinorA0 = (gcd actualMinorA0 actualMinorC0).primPart * A ∧
      actualMinorC0 = (gcd actualMinorA0 actualMinorC0).primPart * C ∧
      (A.map (Int.castRingHom ℝ)).eval b ≠ 0 := by
  obtain ⟨A, C, hA, hC⟩ := primitiveGcd_factorization actualMinorA0 actualMinorC0
  have hg := actualPrimitiveGcd_eval_ne_zero_of_A0_eval_ne_zero hA0
  have hAeval : (A.map (Int.castRingHom ℝ)).eval b ≠ 0 := by
    intro hz
    have : (actualMinorA0.map (Int.castRingHom ℝ)).eval b = 0 := by
      calc
        (actualMinorA0.map (Int.castRingHom ℝ)).eval b =
            (((gcd actualMinorA0 actualMinorC0).primPart * A).map
              (Int.castRingHom ℝ)).eval b := congrArg
                (fun p : Polynomial ℤ => (p.map (Int.castRingHom ℝ)).eval b) hA
        _ = 0 := by rw [Polynomial.map_mul, Polynomial.eval_mul, hg, hz, mul_zero]
    exact hA0 this
  exact ⟨A, C, hA, hC, hAeval⟩

/-! The selected literal relation therefore has the source-normalized ratio
`-C/A` at every point where the leading literal determinant is nonzero. -/
theorem source_normalized_ratio_at_selected_root
    (b r : ℝ)
    (hA0 : Matrix.det (fixedMinorR (literalMatrix b)) ≠ 0)
    (hrel : r * Matrix.det (fixedMinorR (literalMatrix b)) +
      Matrix.det (fixedMinorC (literalMatrix b)) = 0) :
    ∃ A C : Polynomial ℤ,
      actualMinorA0 = (gcd actualMinorA0 actualMinorC0).primPart * A ∧
      actualMinorC0 = (gcd actualMinorA0 actualMinorC0).primPart * C ∧
      (A.map (Int.castRingHom ℝ)).eval b ≠ 0 ∧
      r = -((C.map (Int.castRingHom ℝ)).eval b) /
        ((A.map (Int.castRingHom ℝ)).eval b) := by
  have hA0' : (actualMinorA0.map (Int.castRingHom ℝ)).eval b ≠ 0 := by
    rw [actualMinorA0_eval]
    exact hA0
  obtain ⟨A, C, hA, hC, hAe⟩ :=
    actualPrimitiveQuotientA_eval_ne_zero_of_A0_eval_ne_zero hA0'
  have hrel' :
      r * (((gcd actualMinorA0 actualMinorC0).primPart.map (Int.castRingHom ℝ)).eval b) *
          ((A.map (Int.castRingHom ℝ)).eval b) +
        (((gcd actualMinorA0 actualMinorC0).primPart.map (Int.castRingHom ℝ)).eval b) *
          ((C.map (Int.castRingHom ℝ)).eval b) = 0 := by
    rw [← actualMinorA0_eval, ← actualMinorC0_eval, hA, hC] at hrel
    change r * evalB b ((gcd actualMinorA0 actualMinorC0).primPart * A) +
      evalB b ((gcd actualMinorA0 actualMinorC0).primPart * C) = 0 at hrel
    simpa [evalB, Polynomial.eval₂_eq_eval_map, mul_assoc] using hrel
  have hg := actualPrimitiveGcd_eval_ne_zero_of_A0_eval_ne_zero hA0'
  have hratio : r * ((A.map (Int.castRingHom ℝ)).eval b) +
      ((C.map (Int.castRingHom ℝ)).eval b) = 0 := by
    exact (mul_eq_zero.mp (by
      simpa only [mul_add, mul_assoc] using hrel')).resolve_left
      (mul_ne_zero hg hAe)
  refine ⟨A, C, hA, hC, hAe, ?_⟩
  apply (eq_div_iff hAe).2
  linarith

end D5.S3.Observer.CubicGain.ActualMinorLift


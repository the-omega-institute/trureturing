/- GID: D5/S3/Observer/CubicGain/LegalMatrixMonoid
   generality: I
   mirror-B: D5/B/S3/Observer/CubicGain/LegalMatrixMonoid
   mirror-E: none(waiver:uniform-symbolic-generation)
   anchors: []
   utility: none
   digest: Forward native words are exactly nonnegative integral unimodular matrices. -/

import D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
import D5.S3.Observer.CubicGain.CommonWordSensitivity

/-! The full native monoid, with real entry and determinant conditions. -/

namespace D5.S3.Observer.CubicGain.LegalMatrixMonoid

open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced
open D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
open D5.S3.Observer.CubicGain
open D5.S3.Observer.CubicGain.CommonWordSensitivity
open scoped Matrix

private def realMatrix (A : PositiveMatrix) : Mat :=
  !![(A.a : ℝ), (A.b : ℝ); (A.c : ℝ), (A.d : ℝ)]

private theorem real_mul (A B : PositiveMatrix) :
    realMatrix (A.mul B) = realMatrix A * realMatrix B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realMatrix, PositiveMatrix.mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem product_append (u v : List Bool) :
    futureProduct (u ++ v) = futureProduct v * futureProduct u := by
  induction u with
  | nil => simp [futureProduct]
  | cons e u ih => simp only [List.cons_append, futureProduct, ih, Matrix.mul_assoc]

/-- The universal natural-coordinate correspondence proves integrality of every
actual product, rather than assuming an integral carrier for that product. -/
private theorem product_integral (u : List Bool) :
    ∃ A : PositiveMatrix, realMatrix A = futureProduct u := by
  induction u with
  | nil =>
    refine ⟨rootMatrix, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [realMatrix, rootMatrix, futureProduct]
  | cons e u ih =>
    obtain ⟨A, hA⟩ := ih
    cases e
    · refine ⟨A.mul ⟨0, 1, 1, 1⟩, ?_⟩
      rw [real_mul, hA]
      simp [futureProduct, realMatrix, actionM, actionJ]
    · refine ⟨A.mul ⟨0, 1, 1, 0⟩, ?_⟩
      rw [real_mul, hA]
      simp [futureProduct, realMatrix, actionM, actionJ]

private theorem product_det (u : List Bool) :
    (futureProduct u).det = 1 ∨ (futureProduct u).det = -1 := by
  induction u with
  | nil => simp [futureProduct]
  | cons e u ih =>
    have hM : actionM.det = -1 := by norm_num [actionM, Matrix.det_fin_two]
    have hJ : actionJ.det = -1 := by norm_num [actionJ, Matrix.det_fin_two]
    cases e <;> simp only [futureProduct, Bool.false_eq_true, ↓reduceIte,
      Matrix.det_mul, hM, hJ] <;> rcases ih with h | h <;> simp [h]

/-- Each L/U factor is replaced by its forward chronological native pair:
J then M gives L, while M then J gives U. -/
private theorem realize_word (w : List Bool) :
    ∃ u : List Bool, futureProduct u = realMatrix (wordMatrix w) := by
  induction w with
  | nil =>
    refine ⟨[], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [futureProduct, wordMatrix, realMatrix, rootMatrix]
  | cons e w ih =>
    obtain ⟨u, hu⟩ := ih
    cases e
    · refine ⟨u ++ [true, false], ?_⟩
      change futureProduct (u ++ [true, false]) = realMatrix (leftStep.mul (wordMatrix w))
      rw [product_append, hu, real_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [futureProduct, actionM, actionJ, realMatrix, leftStep,
          Matrix.mul_apply, Fin.sum_univ_two]
    · refine ⟨u ++ [false, true], ?_⟩
      change futureProduct (u ++ [false, true]) = realMatrix (rightStep.mul (wordMatrix w))
      rw [product_append, hu, real_mul]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [futureProduct, actionM, actionJ, realMatrix, rightStep,
          Matrix.mul_apply, Fin.sum_univ_two]

private theorem natural_entry {x : ℝ} (h : 0 ≤ x ∧ ∃ z : ℤ, x = (z : ℝ)) :
    ∃ n : ℕ, x = (n : ℝ) := by
  rcases h with ⟨hx, z, rfl⟩
  have hz : 0 ≤ z := by exact_mod_cast hx
  exact ⟨z.toNat, by exact_mod_cast (Int.toNat_of_nonneg hz).symm⟩

/-- The complete legal monoid on all real 2 by 2 matrices. A word is finite and
forward, the empty word is included, and its chronological head acts first.
The right side states actual entrywise nonnegativity, integrality and either
unimodular sign; it assumes neither positivity nor generation. -/
theorem legal_matrix_monoid (H : Mat) :
    (∃ u : List Bool, futureProduct u = H) ↔
      (∀ i j, 0 ≤ H i j ∧ ∃ z : ℤ, H i j = (z : ℝ)) ∧
        (H.det = 1 ∨ H.det = -1) := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨A, hA⟩ := product_integral u
    refine ⟨?_, product_det u⟩
    rw [← hA]
    intro i j
    fin_cases i <;> fin_cases j
    · exact ⟨Nat.cast_nonneg A.a, ⟨(A.a : ℤ), by simp [realMatrix]⟩⟩
    · exact ⟨Nat.cast_nonneg A.b, ⟨(A.b : ℤ), by simp [realMatrix]⟩⟩
    · exact ⟨Nat.cast_nonneg A.c, ⟨(A.c : ℤ), by simp [realMatrix]⟩⟩
    · exact ⟨Nat.cast_nonneg A.d, ⟨(A.d : ℤ), by simp [realMatrix]⟩⟩
  · rintro ⟨hentries, hdet⟩
    obtain ⟨a, ha⟩ := natural_entry (hentries 0 0)
    obtain ⟨b, hb⟩ := natural_entry (hentries 0 1)
    obtain ⟨c, hc⟩ := natural_entry (hentries 1 0)
    obtain ⟨d, hd⟩ := natural_entry (hentries 1 1)
    let A : PositiveMatrix := ⟨a, b, c, d⟩
    have hA : realMatrix A = H := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [realMatrix, A, ha, hb, hc, hd]
    rw [← hA] at hdet
    simp only [Matrix.det_fin_two, realMatrix, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hdet
    rcases hdet with hdet | hdet
    · have hnat : Unimodular A := by
        have hreal : (a : ℝ) * d = (b : ℝ) * c + 1 := by
          simpa [A, add_comm] using (sub_eq_iff_eq_add.mp hdet)
        exact_mod_cast hreal
      obtain ⟨w, hw⟩ := (unimodular_iff_wordMatrix A).mp hnat
      obtain ⟨u, hu⟩ := realize_word w
      exact ⟨u, by rw [hu, hw, hA]⟩
    · let B : PositiveMatrix := ⟨c, d, a, b⟩
      have hnat : Unimodular B := by
        have hreal : (c : ℝ) * b = (d : ℝ) * a + 1 := by dsimp [A] at hdet; nlinarith
        exact_mod_cast hreal
      obtain ⟨w, hw⟩ := (unimodular_iff_wordMatrix B).mp hnat
      obtain ⟨u, hu⟩ := realize_word w
      refine ⟨u ++ [true], ?_⟩
      rw [product_append, hu, hw]
      calc
        futureProduct [true] * realMatrix B = realMatrix A := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            norm_num [futureProduct, realMatrix, A, B, actionJ,
              Matrix.mul_apply, Fin.sum_univ_two]
        _ = H := hA

end D5.S3.Observer.CubicGain.LegalMatrixMonoid

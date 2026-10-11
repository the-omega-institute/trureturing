/- GID: D5/S1/Words/EvilOdious/MatrixBounds
   generality: I
   mirror-B: D5/B/S1/Words/EvilOdious/MatrixBounds
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S1/Words/EvilOdious/DyadicPrefixBounds.c_prefix; instance=D5/S1/Words/EvilOdious/MatrixBounds.c_five_checked
   digest: Sixfold Thue-Morse counts are controlled by dyadic coefficient states. -/

/-
admission_basis: escape-witness
Module escape_witness: c_word_bound
Direct frozen dependencies: aliases below denote declaration identities, not module pins.
none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15228.
Declaration rows: name | proof_shape | frozen dependencies | escape_witness | consumers.
Definitions carry bind-only as an organization label; no proof content is claimed for them.
matrixBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.matrix_apply_bound, MatrixBounds.matrix_mul_bound, MatrixBounds.h_matrix_bound, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound, MatrixBounds.c_word_bound, DyadicPrefixBounds.vector_prefix_bound, DyadicPrefixBounds.word_bound_of_step, DyadicPrefixBounds.h_step_norm, DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix
vectorBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.matrix_apply_bound, DyadicPrefixBounds.vector_prefix_bound, DyadicPrefixBounds.h_seed, DyadicPrefixBounds.c_seed, DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix
matrixBound_iff_norm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.matrix_apply_bound, MatrixBounds.matrix_mul_bound
vectorBound_iff_norm | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.matrix_apply_bound
matrix_apply_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.vector_prefix_bound
matrix_mul_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_word_bound, DyadicPrefixBounds.word_bound_of_step
pz | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.stateMatrix
stateMatrix | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.h_matrix_bound, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound, MatrixBounds.c_word_bound, DyadicStatesLastThree.state_step_4, DyadicStatesLastThree.state_step_5, DyadicStatesLastThree.state_step_6, DyadicStatesLastThree.stateZ_step_4, DyadicStatesLastThree.stateZ_step_5, DyadicStatesLastThree.stateZ_step_6, DyadicPrefixBounds.h_step_norm, DyadicPrefixBounds.h_state_step, DyadicPrefixBounds.h_prefix, DyadicPrefixBounds.c_prefix, DyadicStatesFirstThree.state_step_1, DyadicStatesFirstThree.state_step_2, DyadicStatesFirstThree.state_step_3, DyadicStatesFirstThree.stateZ_step_1, DyadicStatesFirstThree.stateZ_step_2, DyadicStatesFirstThree.stateZ_step_3
words | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.mem_words, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound
mem_words | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_five_bound, MatrixBounds.c_short_bound
wordMatrix | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.wordMatrix_append, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound, MatrixBounds.c_word_bound, DyadicPrefixBounds.state_word, DyadicPrefixBounds.vector_prefix_bound, DyadicPrefixBounds.word_bound_of_step, DyadicPrefixBounds.state_dyadic_bound, DyadicPrefixBounds.h_prefix
wordMatrix_append | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_word_bound
instDecidableMatrixBound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.h_matrix_bound, MatrixBounds.wordsCheck, MatrixBounds.c_five_bound, MatrixBounds.c_short_bound
h_matrix_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: DyadicPrefixBounds.h_step_norm
wordsCheck | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_five_checked, MatrixBounds.c_short_checked, MatrixBounds.c_short_bound
c_five_checked | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_five_bound
c_short_checked | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_short_bound
c_five_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_word_bound
c_short_bound | proof_shape: bind-only | frozen: none | escape_witness: none | consumers: MatrixBounds.c_word_bound
c_word_bound | proof_shape: content | frozen: none | escape_witness: c_word_bound | consumers: DyadicPrefixBounds.c_prefix
Utility checker: all certificates are kernel-checked and used by the named consumer.
-/

import D5.S1.Words.EvilOdious.SequenceCoefficients
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.List.Sections

namespace D5.S1.Words.EvilOdious.MatrixBounds
open D5.S1.Words.EvilOdious.SequenceCoefficients

set_option autoImplicit false
open Finset Matrix

def matrixBound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) : Prop :=
  ∀ i, ∑ j, (A i j).natAbs ≤ B

def vectorBound {d : ℕ} (v : Fin d → ℤ) (B : ℕ) : Prop :=
  ∀ i, (v i).natAbs ≤ B

open scoped Matrix.Norms.Operator

private theorem matrixBound_iff_norm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) :
    matrixBound A B ↔ ‖A‖₊ ≤ (B : NNReal) := by
  simp only [matrixBound, Matrix.linfty_opNNNorm_def, Finset.sup_le_iff,
    Finset.mem_univ, forall_true_left, ← NNReal.natCast_natAbs, ← Nat.cast_sum, Nat.cast_le]
private theorem vectorBound_iff_norm {d : ℕ} (v : Fin d → ℤ) (B : ℕ) :
    vectorBound v B ↔ ‖v‖₊ ≤ (B : NNReal) := by
  simp only [vectorBound, pi_nnnorm_le_iff, ← NNReal.natCast_natAbs, Nat.cast_le]
theorem matrix_apply_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (v : Fin d → ℤ) (B K : ℕ) (ha : matrixBound A B) (hv : vectorBound v K) :
    vectorBound (A.mulVec v) (B * K) := by
  apply (vectorBound_iff_norm _ _).mpr
  simpa only [Nat.cast_mul] using
    (Matrix.linfty_opNNNorm_mulVec A v).trans (mul_le_mul' ((matrixBound_iff_norm _ _).mp ha) ((vectorBound_iff_norm _ _).mp hv))
theorem matrix_mul_bound {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (a b : ℕ) (ha : matrixBound A a) (hb : matrixBound B b) :
    matrixBound (A * B) (a * b) := by
  apply (matrixBound_iff_norm _ _).mpr
  simpa only [Nat.cast_mul] using
    (Matrix.linfty_opNNNorm_mul A B).trans (mul_le_mul' ((matrixBound_iff_norm _ _).mp ha) ((matrixBound_iff_norm _ _).mp hb))

def pz (p : List ℤ) (k : ℤ) : ℤ := if 0 ≤ k then (List.getD p k.toNat 0) else 0

def stateMatrix (d : ℕ) (p : List ℤ) (b : Bool) : Matrix (Fin d) (Fin d) ℤ :=
  fun i a => pz p (2 * (a : ℤ) + (if b then 1 else 0) - i)

def words (n : ℕ) : List (List Bool) := (List.replicate n [false, true]).sections

private theorem mem_words (w : List Bool) : w ∈ words w.length := by
  apply List.mem_sections.mpr
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i h₁ h₂
  simp only [List.get_eq_getElem, List.getElem_replicate]
  cases w[i] <;> simp

def wordMatrix {d : ℕ} (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (w : List Bool) : Matrix (Fin d) (Fin d) ℤ := (w.map M).prod

private theorem wordMatrix_append {d : ℕ} (M : Bool → Matrix (Fin d) (Fin d) ℤ)
    (v w : List Bool) : wordMatrix M (v ++ w) = wordMatrix M v * wordMatrix M w := by
  simp [wordMatrix]





set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open Finset Matrix

private instance instDecidableMatrixBound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (B : ℕ) : Decidable (matrixBound A B) :=
  inferInstanceAs (Decidable (∀ i : Fin d, ∑ j, (A i j).natAbs ≤ B))


theorem h_matrix_bound :
    matrixBound (stateMatrix 5 (p 1) false) 6 ∧ matrixBound (stateMatrix 5 (p 1) true) 6 ∧
    matrixBound (stateMatrix 5 (p 2) false) 4 ∧ matrixBound (stateMatrix 5 (p 2) true) 4 ∧
    matrixBound (stateMatrix 5 (p 3) false) 4 ∧ matrixBound (stateMatrix 5 (p 3) true) 4 ∧
    matrixBound (stateMatrix 5 (p 4) false) 6 ∧ matrixBound (stateMatrix 5 (p 4) true) 6 ∧
    matrixBound (stateMatrix 5 (p 5) false) 16 ∧ matrixBound (stateMatrix 5 (p 5) true) 16 := by
  decide +kernel

def wordsCheck (len bound : ℕ) : Bool :=
  (words len).all (fun w => decide (matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) bound))

theorem c_five_checked : wordsCheck 5 1019200 = true := by decide +kernel

private theorem c_short_checked :
    (List.range 5).all (fun len => wordsCheck len (2 * 16 ^ len)) = true := by decide +kernel

private theorem c_five_bound (w : List Bool) (hw : w.length = 5) :
    matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (16 ^ 5) := by
  have h := List.all_eq_true.mp c_five_checked w (by rw [← hw]; exact mem_words w)
  have hb : matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) 1019200 := of_decide_eq_true h
  intro i
  exact (hb i).trans (by decide)

private theorem c_short_bound (w : List Bool) (hw : w.length < 5) :
    matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (2 * 16 ^ w.length) := by
  have h := List.all_eq_true.mp c_short_checked w.length (List.mem_range.mpr hw)
  exact of_decide_eq_true (List.all_eq_true.mp h w (mem_words w))

theorem c_word_bound (w : List Bool) : matrixBound (wordMatrix (stateMatrix 6 (p 6)) w) (2 * 16 ^ w.length) := by
  generalize hm : w.length = m
  induction m using Nat.strong_induction_on generalizing w with
  | h m ih =>
    by_cases hsmall : m < 5
    · subst m
      exact c_short_bound w hsmall
    · have hlarge : 5 ≤ m := by omega
      have htake : (w.take 5).length = 5 := by simp [List.length_take, hm, Nat.min_eq_left hlarge]
      have hdrop : (w.drop 5).length = m - 5 := by simp [hm]
      have hb1 := c_five_bound (w.take 5) htake
      have hb2 := ih (m - 5) (by omega) (w.drop 5) hdrop
      have hb := matrix_mul_bound _ _ _ _ hb1 hb2
      rw [← wordMatrix_append, List.take_append_drop] at hb
      have hexp : 16 ^ 5 * (2 * 16 ^ (m - 5)) = 2 * 16 ^ m := by
        rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le hlarge]
      simpa only [hexp, hm] using hb

end D5.S1.Words.EvilOdious.MatrixBounds

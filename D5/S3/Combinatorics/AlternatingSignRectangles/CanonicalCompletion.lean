/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/CanonicalCompletion
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: CanonicalCompletion for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
last_minus_of_zero_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
pad_zero_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_end_column
sum_pad_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
append_one_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
sum_append_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
extAvoids312_corner: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_safe, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.asmZeroFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.asmColumnFibreEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.squareCountEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefixSquare_avoids
no312_with_deficient_last: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_safe, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
no12_with_empty_deficient: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_safe, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_before_nonempty_of_deficit, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
emptyRowAt_empty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.fillRight_at_nonempty
emptyRowAt_surjective: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum
deficientColumnAt_deficient: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.fillBottom_at_complete, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.fillTail_complete_col, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
deficientColumnAt_injective: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.fillBottom_at_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.fillTail_deficient_col
deficientColumnAt_antitone: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.fillTail_decreasing
deficientColumnAt_surjective: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
completionRect_tl: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.canonicalCompletion_corner, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_old
completionRect_tr: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_one_new_col
completionRect_bl: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_one_new_row
completionRect_br: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_one_new_col, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_one_new_row
completion_dimensions: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
fillRight_at_empty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum
fillRight_at_nonempty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_sum
fillBottom_at_deficient: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum
fillBottom_at_complete: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum
completionRect_row_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
completionRect_row_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
completionRect_col_function_old: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum
completionRect_col_function_new: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_sum
completionRect_col_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
completionRect_col_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
completionRect_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
completionRect_old: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
completionRect_one_new_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
completionRect_one_new_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
extAvoids312_safe: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_iff_safe
completionRect_avoids_of_obstructions: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
square_cast_isASM: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.canonicalCompletion_isASM
square_cast_avoids: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_of_safe
canonicalCompletion_isASM: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
canonicalCompletion_corner: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_of_safe
extAvoids312_of_safe: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
extAvoids312_iff_safe: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_avoids_of_obstructions
concat_complete_opposite: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.concat_complete_opposite
minus_singleton_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_line
minus_plus_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_line
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
import Mathlib.Data.Finset.Sort

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma last_minus_of_zero_sum {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) (hzero : (∑ i, (a i : ℤ)) = 0)
    (x : Fin n) (hx : a x ≠ 0) (htail : ∀ y, x < y → a y = 0) : a x = -1 := by
  rcases alternating_line_state a ha hs with ⟨hz, _⟩ | ⟨y, hy, hytail, hsum⟩
  · exact (hx (hz x)).elim
  · have heq : x = y := by
      rcases lt_trichotomy x y with h | h | h
      · exact (hy (htail y h)).elim
      · exact h
      · exact (hx (hytail x h)).elim
    subst y
    cases he : a x <;> simp_all

lemma pad_zero_line {n t : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) (he : EndsOne a) :
    Alternates (Fin.append a (fun _ : Fin t => 0)) ∧
      StartsOne (Fin.append a (fun _ : Fin t => 0)) ∧
      EndsOne (Fin.append a (fun _ : Fin t => 0)) := by
  let b := Fin.append a (fun _ : Fin t => (0 : SignType))
  have hf : StrictMono (fun i : Fin n => i.castAdd t) := fun _ _ h => h
  have hval : ∀ i : Fin n, b (i.castAdd t) = a i := Fin.append_left _ _
  have hout (x : Fin (n+t)) (hx : ¬ ∃ i : Fin n, i.castAdd t = x) : b x = 0 := by
    revert hx
    refine Fin.addCases (fun i hi => ?_) (fun j _ => ?_) x
    · exact (hi ⟨i,rfl⟩).elim
    · exact Fin.append_right _ _ j
  exact ⟨(line_embed a b _ hf hval hout ha hs).1,
    (line_embed a b _ hf hval hout ha hs).2, ends_embed a b _ hf hval hout he⟩

lemma sum_pad_zero {n t : ℕ} (a : Fin n → SignType) :
    (∑ i, ((Fin.append a (fun _ : Fin t => 0) i : SignType) : ℤ)) = ∑ i, (a i : ℤ) := by
  let b := Fin.append a (fun _ : Fin t => (0 : SignType))
  have hf : StrictMono (fun i : Fin n => i.castAdd t) := fun _ _ h => h
  have hval : ∀ i : Fin n, b (i.castAdd t) = a i := Fin.append_left _ _
  have hout (x : Fin (n+t)) (hx : ¬ ∃ i : Fin n, i.castAdd t = x) : b x = 0 := by
    revert hx
    refine Fin.addCases (fun i hi => ?_) (fun j _ => ?_) x
    · exact (hi ⟨i,rfl⟩).elim
    · exact Fin.append_right _ _ j
  exact (sum_embed a b _ hf hval hout).symm

lemma append_one_line {n t : ℕ} (a : Fin n → SignType) (p : Fin t)
    (ha : Alternates a) (hs : StartsOne a) (hzero : (∑ i, (a i : ℤ)) = 0) :
    Alternates (Fin.append a (fun j => if p = j then 1 else 0)) ∧
      StartsOne (Fin.append a (fun j => if p = j then 1 else 0)) ∧
      EndsOne (Fin.append a (fun j => if p = j then 1 else 0)) := by
  let b := Fin.append a (fun j => if p = j then (1 : SignType) else 0)
  have hl (x : Fin n) : b (x.castAdd t) = a x := Fin.append_left _ _ _
  have hr (x : Fin t) : b (Fin.natAdd n x) = if p = x then 1 else 0 := Fin.append_right _ _ _
  have hone : b (Fin.natAdd n p) = 1 := by simp [hr]
  have hcross (x : Fin n) (y : Fin t) : x.castAdd t < Fin.natAdd n y := by
    change x.val < n + y.val
    have := x.isLt
    omega
  change Alternates b ∧ StartsOne b ∧ EndsOne b
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    refine Fin.addCases (fun x => ?_) (fun x => ?_) x
    · refine Fin.addCases (fun y => ?_) (fun y => ?_) y
      · intro hxy hx hy hz
        simp only [hl] at hx hy ⊢
        apply ha x y hxy hx hy
        intro z hxz hzy
        simpa only [hl] using hz (z.castAdd t) hxz hzy
      · intro _ hx hy hz
        have hyp : p = y := by simpa [hr] using hy
        have htail : ∀ z, x < z → a z = 0 := by
          intro z hxz
          simpa only [hl] using hz (z.castAdd t) hxz (hcross z y)
        have hminus := last_minus_of_zero_sum a ha hs hzero x (by simpa only [hl] using hx) htail
        simp [hl, hr, hyp, hminus]
    · refine Fin.addCases (fun y => ?_) (fun y => ?_) y
      · intro hxy _ _ _
        exact (not_lt_of_ge (le_of_lt (hcross y x)) hxy).elim
      · intro hxy hx hy _
        have hxp : p = x := by simpa [hr] using hx
        have hyp : p = y := by simpa [hr] using hy
        have heq : Fin.natAdd n x = Fin.natAdd n y := congrArg (Fin.natAdd n) (hxp.symm.trans hyp)
        exact (ne_of_lt hxy heq).elim
  · intro x
    refine Fin.addCases (fun x => ?_) (fun x => ?_) x
    · intro hx hz
      rw [hl] at hx ⊢
      apply hs x hx
      intro y hy
      simpa only [hl] using hz (y.castAdd t) hy
    · intro hx _
      have hxp : p = x := by simpa [hr] using hx
      simp [hr, hxp]
  · intro x
    refine Fin.addCases (fun x => ?_) (fun x => ?_) x
    · intro _ hz
      have hz' := hz (Fin.natAdd n p) (hcross x p)
      rw [hone] at hz'
      exact (by decide : (1 : SignType) ≠ 0) hz' |>.elim
    · intro hx _
      have hxp : p = x := by simpa [hr] using hx
      simp [hr, hxp]

lemma sum_append_one {n t : ℕ} (a : Fin n → SignType) (p : Fin t) :
    (∑ i, ((Fin.append a (fun j => if p = j then 1 else 0) i : SignType) : ℤ)) =
      (∑ i, (a i : ℤ)) + 1 := by
  have hc (j : Fin t) : ((if p = j then 1 else 0 : SignType) : ℤ) =
      if p = j then 1 else 0 := by
    by_cases h : p = j <;> simp [h]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hc]
  simp

end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

def RectContains312 {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Prop :=
  ∃ (i₁ i₂ i₃ : Fin r) (j₁ j₂ j₃ : Fin k),
    i₁ < i₂ ∧ i₂ < i₃ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
      R i₁ j₃ = 1 ∧ R i₂ j₁ = 1 ∧ R i₃ j₂ = 1

lemma extAvoids312_corner {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) : ¬ RectContains312 R := by
  rintro ⟨i₁, i₂, i₃, j₁, j₂, j₃, hi₁, hi₂, hj₁, hj₂, h₁, h₂, h₃⟩
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := he
  apply hav
  refine ⟨Fin.castLE hr i₁, Fin.castLE hr i₂, Fin.castLE hr i₃,
    Fin.castLE hk j₁, Fin.castLE hk j₂, Fin.castLE hk j₃,
    hi₁, hi₂, hj₁, hj₂, ?_, ?_, ?_⟩ <;> simpa only [hcorner]

lemma no312_with_deficient_last {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) (i₁ i₂ : Fin r) (j₁ j₂ j₃ : Fin k)
    (hi : i₁ < i₂) (hj₁ : j₁ < j₂) (hj₂ : j₂ < j₃)
    (h₁ : R i₁ j₃ = 1) (h₂ : R i₂ j₁ = 1) (hz : colSum R j₂ = 0) : False := by
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := he
  obtain ⟨i₃, hb, h₃⟩ := deficient_column_extension_one R hr hk M hM hcorner j₂ hz
  apply hav
  refine ⟨Fin.castLE hr i₁, Fin.castLE hr i₂, i₃,
    Fin.castLE hk j₁, Fin.castLE hk j₂, Fin.castLE hk j₃,
    hi, ?_, hj₁, hj₂, ?_, ?_, h₃⟩
  · change i₂.val < i₃.val
    have := i₂.isLt
    omega
  · simpa only [hcorner] using h₁
  · simpa only [hcorner] using h₂

lemma no12_with_empty_deficient {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) (i₀ i₁ : Fin r) (j₁ j₂ : Fin k)
    (hi : i₀ < i₁) (hj : j₁ < j₂) (hempty : ∀ j, R i₀ j = 0)
    (h₁ : R i₁ j₁ = 1) (hz : colSum R j₂ = 0) : False := by
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := he
  obtain ⟨j₃, hrb, h₃⟩ := empty_row_extension_one R hr hk M hM hcorner i₀ hempty
  obtain ⟨i₂, hbb, h₂⟩ := deficient_column_extension_one R hr hk M hM hcorner j₂ hz
  apply hav
  refine ⟨Fin.castLE hr i₀, Fin.castLE hr i₁, i₂,
    Fin.castLE hk j₁, Fin.castLE hk j₂, j₃,
    hi, ?_, hj, ?_, h₃, ?_, h₂⟩
  · change i₁.val < i₂.val
    have := i₁.isLt
    omega
  · change j₂.val < j₃.val
    have := j₂.isLt
    omega
  · simpa only [hcorner] using h₁

end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section



def deficientColumnAt {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) : Fin k :=
  (deficientColumns R).orderEmbOfFin rfl x.rev

private lemma emptyRowAt_empty {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (z : Fin (emptyRows R).card) (j : Fin k) : R (((emptyRows R).orderEmbOfFin rfl) z) j = 0 := by
  apply (mem_emptyRows R _).mp
  exact orderEmbOfFin_mem _ _ _

private lemma emptyRowAt_surjective {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (hi : ∀ j, R i j = 0) : ∃ z, ((emptyRows R).orderEmbOfFin rfl) z = i := by
  let x : emptyRows R := ⟨i, (mem_emptyRows R i).mpr hi⟩
  exact ⟨((emptyRows R).orderIsoOfFin rfl).symm x,
    congrArg Subtype.val (((emptyRows R).orderIsoOfFin rfl).apply_symm_apply x)⟩

lemma deficientColumnAt_deficient {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) : colSum R (deficientColumnAt R x) = 0 := by
  apply (mem_deficientColumns R _).mp
  exact orderEmbOfFin_mem _ _ _

lemma deficientColumnAt_injective {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    Function.Injective (deficientColumnAt R) :=
  ((deficientColumns R).orderEmbOfFin rfl).injective.comp Fin.rev_injective

lemma deficientColumnAt_antitone {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x y : Fin (deficientColumns R).card) (hxy : x < y) :
    deficientColumnAt R y < deficientColumnAt R x :=
  ((deficientColumns R).orderEmbOfFin rfl).strictMono (Fin.rev_lt_rev.mpr hxy)

lemma deficientColumnAt_surjective {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (j : Fin k) (hj : colSum R j = 0) : ∃ x, deficientColumnAt R x = j := by
  let y : deficientColumns R := ⟨j, (mem_deficientColumns R j).mpr hj⟩
  let z := ((deficientColumns R).orderIsoOfFin rfl).symm y
  refine ⟨z.rev, ?_⟩
  simp only [deficientColumnAt, Fin.rev_rev]
  exact congrArg Subtype.val (((deficientColumns R).orderIsoOfFin rfl).apply_symm_apply y)

private def fillRight {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (z : Fin (emptyRows R).card) : SignType :=
  if ((emptyRows R).orderEmbOfFin rfl) z = i then 1 else 0

private def fillBottom {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) (j : Fin k) : SignType :=
  if deficientColumnAt R x = j then 1 else 0

private def completionRect {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    Matrix (Fin (r + (deficientColumns R).card)) (Fin (k + (emptyRows R).card)) SignType :=
  Fin.append (fun i => Fin.append (R i) (fillRight R i))
    (fun x => Fin.append (fillBottom R x) (fun _ => 0))

@[simp] private lemma completionRect_tl {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (j : Fin k) :
    completionRect R (i.castAdd _) (j.castAdd _) = R i j := by
  simp [completionRect]

@[simp] private lemma completionRect_tr {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (z : Fin (emptyRows R).card) :
    completionRect R (i.castAdd _) (Fin.natAdd k z) = fillRight R i z := by
  simp [completionRect]

@[simp] private lemma completionRect_bl {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) (j : Fin k) :
    completionRect R (Fin.natAdd r x) (j.castAdd _) = fillBottom R x j := by
  simp [completionRect]

@[simp] private lemma completionRect_br {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) (z : Fin (emptyRows R).card) :
    completionRect R (Fin.natAdd r x) (Fin.natAdd k z) = 0 := by
  simp [completionRect]

private lemma completion_dimensions {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : r + (deficientColumns R).card = k + (emptyRows R).card := by
  have := emptyRows_balance R
  have := deficientColumns_balance R hR
  omega

end
end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private lemma fillRight_at_empty {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (z : Fin (emptyRows R).card) :
    fillRight R (((emptyRows R).orderEmbOfFin rfl) z) = fun y => if z = y then 1 else 0 := by
  funext y
  simp only [fillRight, (((emptyRows R).orderEmbOfFin rfl)).injective.eq_iff]
  simp only [eq_comm]

private lemma fillRight_at_nonempty {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin r) (hi : ∃ j, R i j ≠ 0) : fillRight R i = fun _ => 0 := by
  funext z
  have hn : ((emptyRows R).orderEmbOfFin rfl) z ≠ i := by
    rintro h
    obtain ⟨j, hj⟩ := hi
    exact hj (h ▸ emptyRowAt_empty R z j)
  simp [fillRight, hn]

private lemma fillBottom_at_deficient {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (x : Fin (deficientColumns R).card) :
    (fun y => fillBottom R y (deficientColumnAt R x)) = fun y => if x = y then 1 else 0 := by
  funext y
  simp only [fillBottom, (deficientColumnAt_injective R).eq_iff]
  simp only [eq_comm]

private lemma fillBottom_at_complete {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (j : Fin k) (hj : colSum R j = 1) : (fun x => fillBottom R x j) = fun _ => 0 := by
  funext x
  have hn : deficientColumnAt R x ≠ j := by
    intro h
    have := deficientColumnAt_deficient R x
    rw [h, hj] at this
    omega
  simp [fillBottom, hn]

private lemma completionRect_row_line {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (i : Fin (r + (deficientColumns R).card)) :
    Alternates (completionRect R i) ∧ StartsOne (completionRect R i) ∧
      EndsOne (completionRect R i) := by
  classical
  refine Fin.addCases (fun i => ?_) (fun x => ?_) i
  · simp only [completionRect, Fin.append_left, Fin.append_right]
    change Alternates (Fin.append (R i) (fillRight R i)) ∧
      StartsOne (Fin.append (R i) (fillRight R i)) ∧ EndsOne (Fin.append (R i) (fillRight R i))
    by_cases hi : ∃ j, R i j ≠ 0
    · rw [fillRight_at_nonempty R i hi]
      exact pad_zero_line (R i) (hR.1 i).1 (hR.1 i).2.1 (hR.1 i).2.2
    · have hz : ∀ j, R i j = 0 := by simpa only [not_exists, not_not] using hi
      obtain ⟨z, heq⟩ := emptyRowAt_surjective R i hz
      rw [← heq, fillRight_at_empty]
      apply append_one_line _ z (hR.1 _).1 (hR.1 _).2.1
      simp [emptyRowAt_empty]
  · simp only [completionRect, Fin.append_left, Fin.append_right]
    change Alternates (Fin.append (fillBottom R x) (fun _ => 0)) ∧
      StartsOne (Fin.append (fillBottom R x) (fun _ => 0)) ∧
      EndsOne (Fin.append (fillBottom R x) (fun _ => 0))
    exact pad_zero_line _ (singleton_line (deficientColumnAt R x)).1
      (singleton_line (deficientColumnAt R x)).2.1 (singleton_line (deficientColumnAt R x)).2.2

private lemma completionRect_row_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (i : Fin (r + (deficientColumns R).card)) :
    (∑ j, (completionRect R i j : ℤ)) = 1 := by
  classical
  refine Fin.addCases (fun i => ?_) (fun x => ?_) i
  · simp only [completionRect, Fin.append_left, Fin.append_right]
    change (∑ j, ((Fin.append (R i) (fillRight R i) j : SignType) : ℤ)) = 1
    by_cases hi : ∃ j, R i j ≠ 0
    · rw [fillRight_at_nonempty R i hi, sum_pad_zero, asr_row_sum R hR i]
      simp only [hi, if_true]
    · have hz : ∀ j, R i j = 0 := by simpa only [not_exists, not_not] using hi
      obtain ⟨z, heq⟩ := emptyRowAt_surjective R i hz
      rw [← heq, fillRight_at_empty, sum_append_one]
      simp [emptyRowAt_empty]
  · simp only [completionRect, Fin.append_left, Fin.append_right]
    change (∑ j, ((Fin.append (fillBottom R x) (fun _ => 0) j : SignType) : ℤ)) = 1
    rw [sum_pad_zero]
    have hc (j : Fin k) : (fillBottom R x j : ℤ) = if deficientColumnAt R x = j then 1 else 0 := by
      unfold fillBottom
      split_ifs <;> simp
    simp only [hc]
    simp

private lemma completionRect_col_function_old {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (j : Fin k) :
    (fun i => completionRect R i (j.castAdd _)) =
      Fin.append (fun i => R i j) (fun x => fillBottom R x j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun x => ?_) i <;> simp [completionRect]

private lemma completionRect_col_function_new {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (z : Fin (emptyRows R).card) :
    (fun i => completionRect R i (Fin.natAdd k z)) =
      Fin.append (fun i => if ((emptyRows R).orderEmbOfFin rfl) z = i then 1 else 0) (fun _ => 0) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun x => ?_) i <;> simp [completionRect, fillRight]

private lemma completionRect_col_line {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (j : Fin (k + (emptyRows R).card)) :
    Alternates (fun i => completionRect R i j) ∧ StartsOne (fun i => completionRect R i j) := by
  refine Fin.addCases (fun j => ?_) (fun z => ?_) j
  · rw [completionRect_col_function_old]
    rcases asr_col_sum R hR j with hz | hone
    · obtain ⟨x, heq⟩ := deficientColumnAt_surjective R j hz
      rw [← heq, fillBottom_at_deficient]
      exact (append_one_line _ x (hR.2 _).1 (hR.2 _).2
        (deficientColumnAt_deficient R x)).imp_right And.left
    · rw [fillBottom_at_complete R j hone]
      exact (pad_zero_line _ (hR.2 _).1 (hR.2 _).2
        (line_sum_one_ends_one _ (hR.2 _).1 (hR.2 _).2 hone)).imp_right And.left
  · rw [completionRect_col_function_new]
    exact (pad_zero_line _ (singleton_line (((emptyRows R).orderEmbOfFin rfl) z)).1
      (singleton_line (((emptyRows R).orderEmbOfFin rfl) z)).2.1 (singleton_line (((emptyRows R).orderEmbOfFin rfl) z)).2.2).imp_right And.left

private lemma completionRect_col_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (j : Fin (k + (emptyRows R).card)) :
    (∑ i, (completionRect R i j : ℤ)) = 1 := by
  refine Fin.addCases (fun j => ?_) (fun z => ?_) j
  · change (∑ i, ((fun i => completionRect R i (j.castAdd _)) i : ℤ)) = 1
    rw [completionRect_col_function_old]
    rcases asr_col_sum R hR j with hz | hone
    · obtain ⟨x, heq⟩ := deficientColumnAt_surjective R j hz
      rw [← heq, fillBottom_at_deficient, sum_append_one]
      change colSum R (deficientColumnAt R x) + 1 = 1
      rw [deficientColumnAt_deficient]
      rfl
    · rw [fillBottom_at_complete R j hone, sum_pad_zero]
      exact hone
  · change (∑ i, ((fun i => completionRect R i (Fin.natAdd k z)) i : ℤ)) = 1
    rw [completionRect_col_function_new, sum_pad_zero]
    have hc (i : Fin r) : ((if ((emptyRows R).orderEmbOfFin rfl) z = i then 1 else 0 : SignType) : ℤ) =
        if ((emptyRows R).orderEmbOfFin rfl) z = i then 1 else 0 := by
      split_ifs <;> simp
    simp only [hc]
    simp

private lemma completionRect_isASR {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : IsASR (completionRect R) :=
  ⟨completionRect_row_line R hR, completionRect_col_line R hR⟩

end
end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private lemma completionRect_old {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin (r + (deficientColumns R).card)) (j : Fin (k + (emptyRows R).card))
    (hi : i.val < r) (hj : j.val < k) :
    completionRect R i j = R ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
  have hi' : (⟨i.val, hi⟩ : Fin r).castAdd (deficientColumns R).card = i := by apply Fin.ext; rfl
  have hj' : (⟨j.val, hj⟩ : Fin k).castAdd (emptyRows R).card = j := by apply Fin.ext; rfl
  simpa only [hi', hj'] using completionRect_tl R ⟨i.val, hi⟩ ⟨j.val, hj⟩

private lemma completionRect_one_new_row {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin (r + (deficientColumns R).card)) (j : Fin (k + (emptyRows R).card))
    (hi : r ≤ i.val) (hone : completionRect R i j = 1) :
    ∃ x : Fin (deficientColumns R).card,
      i = Fin.natAdd r x ∧ j = (deficientColumnAt R x).castAdd (emptyRows R).card := by
  have hx : i.val - r < (deficientColumns R).card := by have := i.isLt; omega
  let x : Fin (deficientColumns R).card := ⟨i.val - r, hx⟩
  have hi' : i = Fin.natAdd r x := by apply Fin.ext; simp [x]; omega
  refine ⟨x, hi', ?_⟩
  rw [hi'] at hone
  revert hone
  refine Fin.addCases (fun j => ?_) (fun z => ?_) j
  · intro hone
    have heq : deficientColumnAt R x = j := by simpa [fillBottom] using hone
    simpa [heq]
  · intro hone
    simp at hone

private lemma completionRect_one_new_col {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (i : Fin (r + (deficientColumns R).card)) (j : Fin (k + (emptyRows R).card))
    (hj : k ≤ j.val) (hone : completionRect R i j = 1) :
    ∃ z : Fin (emptyRows R).card,
      i = (((emptyRows R).orderEmbOfFin rfl) z).castAdd (deficientColumns R).card ∧ j = Fin.natAdd k z := by
  have hz : j.val - k < (emptyRows R).card := by have := j.isLt; omega
  let z : Fin (emptyRows R).card := ⟨j.val - k, hz⟩
  have hj' : j = Fin.natAdd k z := by apply Fin.ext; simp [z]; omega
  refine ⟨z, ?_, hj'⟩
  rw [hj'] at hone
  revert hone
  refine Fin.addCases (fun i => ?_) (fun x => ?_) i
  · intro hone
    have heq : ((emptyRows R).orderEmbOfFin rfl) z = i := by simpa [fillRight] using hone
    simpa [heq]
  · intro hone
    simp at hone

structure CompletionSafe {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Prop where
  corner : ¬ RectContains312 R
  deficient : ∀ (i₁ i₂ : Fin r) (j₁ j₂ j₃ : Fin k), i₁ < i₂ → j₁ < j₂ → j₂ < j₃ →
    R i₁ j₃ = 1 → R i₂ j₁ = 1 → colSum R j₂ = 0 → False
  empty : ∀ (i₀ i₁ i₂ : Fin r) (j₁ j₂ : Fin k), i₀ < i₁ → i₁ < i₂ → j₁ < j₂ →
    (∀ j, R i₀ j = 0) → ¬ (R i₁ j₁ = 1 ∧ R i₂ j₂ = 1)
  empty_deficient : ∀ (i₀ i₁ : Fin r) (j₁ j₂ : Fin k), i₀ < i₁ → j₁ < j₂ →
    (∀ j, R i₀ j = 0) → R i₁ j₁ = 1 → colSum R j₂ = 0 → False

private lemma extAvoids312_safe {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) : CompletionSafe R :=
  ⟨extAvoids312_corner R he, no312_with_deficient_last R he,
    no12_below_empty R he, no12_with_empty_deficient R he⟩

private lemma completionRect_avoids_of_obstructions {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hsafe : CompletionSafe R) : ¬ RectContains312 (completionRect R) := by
  rintro ⟨i₁, i₂, i₃, j₁, j₂, j₃, hi₁₂, hi₂₃, hj₁₂, hj₂₃, h₁, h₂, h₃⟩
  by_cases hi₂ : r ≤ i₂.val
  · have hi₃ : r ≤ i₃.val := by change i₂.val < i₃.val at hi₂₃; omega
    obtain ⟨x, rfl, rfl⟩ := completionRect_one_new_row R i₂ j₁ hi₂ h₂
    obtain ⟨y, hiy, hjy⟩ := completionRect_one_new_row R i₃ j₂ hi₃ h₃
    rw [hiy] at hi₂₃
    have hxy : x < y := by change r + x.val < r + y.val at hi₂₃; change x.val < y.val; omega
    have hrev := deficientColumnAt_antitone R x y hxy
    rw [hjy] at hj₁₂
    exact (not_lt_of_ge (le_of_lt hrev)) hj₁₂
  have hi₂' : i₂.val < r := Nat.lt_of_not_ge hi₂
  have hi₁' : i₁.val < r := by change i₁.val < i₂.val at hi₁₂; omega
  by_cases hj₂ : k ≤ j₂.val
  · have hj₃ : k ≤ j₃.val := by change j₂.val < j₃.val at hj₂₃; omega
    obtain ⟨z₁, hiz₁, hjz₁⟩ := completionRect_one_new_col R i₁ j₃ hj₃ h₁
    obtain ⟨z₃, hiz₃, hjz₃⟩ := completionRect_one_new_col R i₃ j₂ hj₂ h₃
    have hir : ((emptyRows R).orderEmbOfFin rfl) z₁ < ((emptyRows R).orderEmbOfFin rfl) z₃ := by
      have h := lt_trans hi₁₂ hi₂₃
      rw [hiz₁, hiz₃] at h
      exact h
    have hz : z₁ < z₃ := (((emptyRows R).orderEmbOfFin rfl)).lt_iff_lt.mp hir
    rw [hjz₁, hjz₃] at hj₂₃
    change k + z₃.val < k + z₁.val at hj₂₃
    change z₁.val < z₃.val at hz
    omega
  have hj₂' : j₂.val < k := Nat.lt_of_not_ge hj₂
  have hj₁' : j₁.val < k := by change j₁.val < j₂.val at hj₁₂; omega
  have h₂' : R ⟨i₂.val, hi₂'⟩ ⟨j₁.val, hj₁'⟩ = 1 := by
    simpa only [completionRect_old R i₂ j₁ hi₂' hj₁'] using h₂
  by_cases hi₃ : r ≤ i₃.val
  · obtain ⟨x, hix, hjx⟩ := completionRect_one_new_row R i₃ j₂ hi₃ h₃
    have hdef : colSum R ⟨j₂.val, hj₂'⟩ = 0 := by
      have heq : (⟨j₂.val, hj₂'⟩ : Fin k) = deficientColumnAt R x := by
        apply Fin.ext
        simpa only [Fin.val_castAdd] using congrArg Fin.val hjx
      rw [heq]
      exact deficientColumnAt_deficient R x
    by_cases hj₃ : k ≤ j₃.val
    · obtain ⟨z, hiz, _⟩ := completionRect_one_new_col R i₁ j₃ hj₃ h₁
      have hempty : ∀ j, R ⟨i₁.val, hi₁'⟩ j = 0 := by
        have heq : (⟨i₁.val, hi₁'⟩ : Fin r) = ((emptyRows R).orderEmbOfFin rfl) z := by
          apply Fin.ext
          simpa only [Fin.val_castAdd] using congrArg Fin.val hiz
        rw [heq]
        exact emptyRowAt_empty R z
      exact hsafe.empty_deficient ⟨i₁.val, hi₁'⟩ ⟨i₂.val, hi₂'⟩
        ⟨j₁.val, hj₁'⟩ ⟨j₂.val, hj₂'⟩ hi₁₂ hj₁₂ hempty h₂' hdef
    · have hj₃' : j₃.val < k := Nat.lt_of_not_ge hj₃
      have h₁' : R ⟨i₁.val, hi₁'⟩ ⟨j₃.val, hj₃'⟩ = 1 := by
        simpa only [completionRect_old R i₁ j₃ hi₁' hj₃'] using h₁
      exact hsafe.deficient ⟨i₁.val, hi₁'⟩ ⟨i₂.val, hi₂'⟩
        ⟨j₁.val, hj₁'⟩ ⟨j₂.val, hj₂'⟩ ⟨j₃.val, hj₃'⟩ hi₁₂ hj₁₂ hj₂₃ h₁' h₂' hdef
  · have hi₃' : i₃.val < r := Nat.lt_of_not_ge hi₃
    have h₃' : R ⟨i₃.val, hi₃'⟩ ⟨j₂.val, hj₂'⟩ = 1 := by
      simpa only [completionRect_old R i₃ j₂ hi₃' hj₂'] using h₃
    by_cases hj₃ : k ≤ j₃.val
    · obtain ⟨z, hiz, _⟩ := completionRect_one_new_col R i₁ j₃ hj₃ h₁
      have hempty : ∀ j, R ⟨i₁.val, hi₁'⟩ j = 0 := by
        have heq : (⟨i₁.val, hi₁'⟩ : Fin r) = ((emptyRows R).orderEmbOfFin rfl) z := by
          apply Fin.ext
          simpa only [Fin.val_castAdd] using congrArg Fin.val hiz
        rw [heq]
        exact emptyRowAt_empty R z
      exact hsafe.empty ⟨i₁.val, hi₁'⟩ ⟨i₂.val, hi₂'⟩ ⟨i₃.val, hi₃'⟩
        ⟨j₁.val, hj₁'⟩ ⟨j₂.val, hj₂'⟩ hi₁₂ hi₂₃ hj₁₂ hempty ⟨h₂', h₃'⟩
    · have hj₃' : j₃.val < k := Nat.lt_of_not_ge hj₃
      have h₁' : R ⟨i₁.val, hi₁'⟩ ⟨j₃.val, hj₃'⟩ = 1 := by
        simpa only [completionRect_old R i₁ j₃ hi₁' hj₃'] using h₁
      exact hsafe.corner ⟨⟨i₁.val, hi₁'⟩, ⟨i₂.val, hi₂'⟩, ⟨i₃.val, hi₃'⟩,
        ⟨j₁.val, hj₁'⟩, ⟨j₂.val, hj₂'⟩, ⟨j₃.val, hj₃'⟩,
        hi₁₂, hi₂₃, hj₁₂, hj₂₃, h₁', h₂', h₃'⟩


end
end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private lemma square_cast_isASM {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (h : r = k)
    (hR : IsASR R) (hrows : ∀ i, (∑ j, (R i j : ℤ)) = 1)
    (hcols : ∀ j, (∑ i, (R i j : ℤ)) = 1) :
    IsASM (fun i j : Fin r => R i (Fin.cast h j)) := by
  subst k
  simpa only [Fin.cast_refl, id_eq] using (show IsASM R from ⟨hR, hrows, hcols⟩)

private lemma square_cast_avoids {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (h : r = k)
    (hav : ¬ RectContains312 R) :
    ¬ Contains312 (fun i j : Fin r => R i (Fin.cast h j)) := by
  subst k
  simpa only [Fin.cast_refl, id_eq, Contains312, RectContains312] using hav

private def canonicalCompletion {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (hR : IsASR R) :
    Matrix (Fin (r + (deficientColumns R).card)) (Fin (r + (deficientColumns R).card)) SignType :=
  fun i j => completionRect R i (Fin.cast (completion_dimensions R hR) j)

private lemma canonicalCompletion_isASM {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : IsASM (canonicalCompletion R hR) :=
  square_cast_isASM (completionRect R) (completion_dimensions R hR) (completionRect_isASR R hR)
    (completionRect_row_sum R hR) (completionRect_col_sum R hR)

private lemma canonicalCompletion_corner {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hr : r ≤ r + (deficientColumns R).card)
    (hk : k ≤ r + (deficientColumns R).card) (i : Fin r) (j : Fin k) :
    canonicalCompletion R hR (Fin.castLE hr i) (Fin.castLE hk j) = R i j := by
  have hir : Fin.castLE hr i = i.castAdd (deficientColumns R).card := by apply Fin.ext; rfl
  have hjr : Fin.cast (completion_dimensions R hR) (Fin.castLE hk j) =
      j.castAdd (emptyRows R).card := by apply Fin.ext; rfl
  simp only [canonicalCompletion, hir, hjr, completionRect_tl]


end
end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
noncomputable section

private lemma extAvoids312_of_safe {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hsafe : CompletionSafe R) : ExtAvoids312 R := by
  have hdim := completion_dimensions R hR
  have hr : r ≤ r + (deficientColumns R).card := by omega
  have hk : k ≤ r + (deficientColumns R).card := by omega
  have hav : ¬ Contains312 (canonicalCompletion R hR) :=
    square_cast_avoids (completionRect R) (completion_dimensions R hR)
      (completionRect_avoids_of_obstructions R hsafe)
  exact ⟨r + (deficientColumns R).card,hr,hk,canonicalCompletion R hR,
    canonicalCompletion_isASM R hR,hav,canonicalCompletion_corner R hR hr hk⟩

lemma extAvoids312_iff_safe {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : ExtAvoids312 R ↔ CompletionSafe R :=
  ⟨extAvoids312_safe R,extAvoids312_of_safe R hR⟩

end
end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

def StartsMinus {n : ℕ} (a : Fin n → SignType) : Prop :=
  ∀ x, a x ≠ 0 → (∀ y, y < x → a y = 0) → a x = -1

lemma concat_complete_opposite {n t : ℕ} (a : Fin n → SignType) (b : Fin t → SignType)
    (ha : Alternates a) (hs : StartsOne a) (he : EndsOne a)
    (ht : (∑ i, (a i : ℤ)) = 1) (hb : Alternates b) (hbs : StartsMinus b) :
    Alternates (Fin.append a b) ∧ StartsOne (Fin.append a b) := by
  let c := Fin.append a b
  have hl (x : Fin n) : c (x.castAdd t) = a x := Fin.append_left _ _ _
  have hr (x : Fin t) : c (Fin.natAdd n x) = b x := Fin.append_right _ _ _
  have hcross (x : Fin n) (y : Fin t) : x.castAdd t < Fin.natAdd n y := by
    change x.val < n+y.val
    have := x.isLt
    omega
  have hone : ∃ x, a x = 1 := by
    exact one_after_zero_prefix (show 0 ≤ n by omega) a ht (by simp) |>.imp (fun x h => h.2)
  change Alternates c ∧ StartsOne c
  refine ⟨?_,?_⟩
  · intro x y
    refine Fin.addCases (fun x => ?_) (fun x => ?_) x
    · refine Fin.addCases (fun y => ?_) (fun y => ?_) y
      · intro hxy hx hy hgap
        simp only [hl] at hx hy ⊢
        apply ha x y hxy hx hy
        intro z hxz hzy
        simpa only [hl] using hgap (z.castAdd t) hxz hzy
      · intro hxy hx hy hgap
        have hxlast : a x=1 := by
          apply he x (by simpa only [hl] using hx)
          intro z hxz
          simpa only [hl] using hgap (z.castAdd t) hxz (hcross z y)
        have hyfirst : b y = -1 := by
          apply hbs y (by simpa only [hr] using hy)
          intro z hzy
          simpa only [hr] using hgap (Fin.natAdd n z) (hcross x z) (by simpa using hzy)
        simp [hl,hr,hxlast,hyfirst]
    · refine Fin.addCases (fun y => ?_) (fun y => ?_) y
      · intro hxy _ _ _
        exact (not_lt_of_ge (le_of_lt (hcross y x)) hxy).elim
      · intro hxy hx hy hgap
        simp only [hr] at hx hy ⊢
        apply hb x y (by simpa using hxy) hx hy
        intro z hxz hzy
        simpa only [hr] using hgap (Fin.natAdd n z) (by simpa using hxz) (by simpa using hzy)
  · intro x
    refine Fin.addCases (fun x => ?_) (fun x => ?_) x
    · intro hx hgap
      rw [hl] at hx ⊢
      apply hs x hx
      intro y hyx
      simpa only [hl] using hgap (y.castAdd t) hyx
    · intro _ hgap
      obtain ⟨u,hu⟩ := hone
      have hz := hgap (u.castAdd t) (hcross u x)
      rw [hl,hu] at hz
      exact (by decide : (1 : SignType) ≠ 0) hz |>.elim

lemma minus_singleton_line {n : ℕ} (p : Fin n) :
    Alternates (fun x => if x=p then (-1 : SignType) else 0) ∧
    StartsMinus (fun x => if x=p then (-1 : SignType) else 0) := by
  refine ⟨?_,?_⟩
  · intro x y hxy hx hy _
    have hx' : x=p := by simpa using hx
    have hy' : y=p := by simpa using hy
    subst x
    subst y
    exact (lt_irrefl _ hxy).elim
  · intro x hx _
    have hx' : x=p := by simpa using hx
    simp [hx']

lemma minus_plus_line {n : ℕ} (x y : Fin n) (hxy : x < y) :
    let a := fun z => if z=x then (-1 : SignType) else if z=y then 1 else 0
    Alternates a ∧ StartsMinus a := by
  dsimp
  let a := fun z => if z=x then (-1 : SignType) else if z=y then 1 else 0
  change Alternates a ∧ StartsMinus a
  have hx : a x = -1 := by simp [a]
  have hy : a y = 1 := by simp [a,ne_of_gt hxy]
  have hsupport (z : Fin n) (hz : a z ≠ 0) : z=x ∨ z=y := by
    by_contra hn
    push_neg at hn
    simp [a,hn] at hz
  refine ⟨?_,?_⟩
  · intro u v huv hu hv _
    rcases hsupport u hu with rfl | rfl <;> rcases hsupport v hv with rfl | rfl
    · exact (lt_irrefl _ huv).elim
    · simp [hx,hy]
    · exact (not_lt_of_ge (le_of_lt hxy) huv).elim
    · exact (lt_irrefl _ huv).elim
  · intro u hu hgap
    rcases hsupport u hu with rfl | rfl
    · exact hx
    · have hz := hgap x hxy
      rw [hx] at hz
      exact (by decide : (-1 : SignType) ≠ 0) hz |>.elim

end D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

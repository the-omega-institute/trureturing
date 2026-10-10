/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/SignLines
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/SignLines
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: SignLines for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
line_embed: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.pad_zero_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.cons_zero_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_interior_column, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_right_column, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
ends_embed: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.pad_zero_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.cons_zero_ends, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_lower_row, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_top_row
sum_embed: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.sum_pad_zero, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_colSum, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.middle_line_sum
singleton_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completionRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.permMatrix_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row
permMatrix_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.permMatrix_isASM
permMatrix_cast: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.permMatrix_isASM
permMatrix_isASM: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.zero_extAvoids312
antiDiag_avoids: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.zero_extAvoids312
zero_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.S_zero
zero_extAvoids312: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.S_zero
nonemptyRows_eq_zero_iff: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.S_zero
S_zero: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.ExtendedAvoidanceClosedForm.literal_recurrenceSpec, D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmptyCounted_card
row_has_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.empty_row_extension_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_before, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_empty_source
empty_row_extension_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.no12_with_empty_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.no12_below_empty
no12_below_empty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.extAvoids312_safe, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_no_minus, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_strict_decreasing, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.zeroColumn_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_extAvoids_inv, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.residualRect_extAvoids, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_extAvoids
prefix_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.topRows_isASR, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.line_tail_zero_after_complete, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefixSquare_isASM
topRows_isASR: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.extractFibre, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_one_iff_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_sum_le_one, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.first_empty_tail_card, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.asr_prefix_column_complete_before_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_zero, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_column_complete_at_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_shift_column_sum, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_width
topRows_extAvoids312: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.extractFibre
alternating_line_state: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
alternating_line_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
complete_line_sum_eq_indicator: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asr_row_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asr_row_sum_one_iff: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
one_before_minus: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.one_before_minus
one_after_minus_of_ends: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.one_after_minus_of_ends
line_sum_one_ends_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asm_column_ends_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asm_row_minus_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asm_row_minus_unique
asm_column_minus_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asm_column_minus_unique
asr_row_minus_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asm_row_minus_unique
asr_column_minus_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asm_column_minus_unique
minus_between_ones: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
asr_first_col_not_minus: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.InteriorRecurrence.firstEmpty_first_col_zero, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.nonzeroFirst_iff, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asr_first_col_one_unique, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_line, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_sum, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.correctedColumn_zero, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.first_column_zero_except_pivot, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.pivot_minus_only_at_end, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_first_column_zero
asr_first_col_one_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
line_no_minus_singleton: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
asr_first_row_not_minus: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.asr_first_row_singleton, D5.S3.Combinatorics.AlternatingSignRectangles.SquareASMDecomposition.topLeft_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.mergeRectAt_residual
asr_first_row_singleton: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.minus_between_ones
three_sign_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.mergeRect_pivot_row
mem_emptyRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.emptyRowAt_empty, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.emptyRowAt_surjective, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.first_empty_row_exists, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.rowComplete_nonempty, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.all_rows_nonempty_iff
mem_deficientColumns: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.deficientColumnAt_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.deficientColumnAt_surjective, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balancedTailEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailColumn_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_before_nonempty_of_deficit, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.balanced_column_sum, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_width
asr_col_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
asr_total_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
emptyRows_balance: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.completion_dimensions, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.first_empty_row_exists, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.rowComplete_nonempty, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.nonemptyRows_le_rows, D5.S3.Combinatorics.AlternatingSignRectangles.SquareMergeConstruction.all_rows_nonempty_iff
deficientColumns_balance: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
nonemptyRows_le_rows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.counted_outside_isEmpty
nonemptyRows_le_columns: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
balanced_column_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
prefix_sum_as_filter: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.topRows_col_sum_filter, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.one_after_zero_prefix
one_after_zero_prefix: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.concat_complete_opposite, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_one_iff_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.deficient_column_extension_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquareFirstColumnDecomposition.asm_first_column_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.asm_prefix_zero_forbids_right_one, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.below_prefix_interior_not_minus, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_complete_column_range
deficient_column_extension_one: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.no12_with_empty_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion.no312_with_deficient_last
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Set.Card
import Mathlib.Data.Sign.Basic

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
set_option maxSynthPendingDepth 64

open Finset

def Alternates {n : ℕ} (a : Fin n → SignType) : Prop :=
  ∀ x y, x < y → a x ≠ 0 → a y ≠ 0 →
    (∀ z, x < z → z < y → a z = 0) → a x ≠ a y

def StartsOne {n : ℕ} (a : Fin n → SignType) : Prop :=
  ∀ x, a x ≠ 0 → (∀ y, y < x → a y = 0) → a x = 1

def EndsOne {n : ℕ} (a : Fin n → SignType) : Prop :=
  ∀ x, a x ≠ 0 → (∀ y, x < y → a y = 0) → a x = 1

def IsASR {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Prop :=
  (∀ i : Fin r, Alternates (R i) ∧ StartsOne (R i) ∧ EndsOne (R i)) ∧
  (∀ j : Fin k, Alternates (fun i : Fin r => R i j) ∧ StartsOne (fun i => R i j))

def IsASM {m : ℕ} (M : Matrix (Fin m) (Fin m) SignType) : Prop :=
  IsASR M ∧ (∀ i, ∑ j, (M i j : ℤ) = 1) ∧ (∀ j, ∑ i, (M i j : ℤ) = 1)

def Contains312 {m : ℕ} (M : Matrix (Fin m) (Fin m) SignType) : Prop :=
  ∃ (i₁ i₂ i₃ j₁ j₂ j₃ : Fin m),
    i₁ < i₂ ∧ i₂ < i₃ ∧ j₁ < j₂ ∧ j₂ < j₃ ∧
      M i₁ j₃ = 1 ∧ M i₂ j₁ = 1 ∧ M i₃ j₂ = 1

def ExtAvoids312 {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Prop :=
  ∃ (m : ℕ) (hr : r ≤ m) (hk : k ≤ m)
    (M : Matrix (Fin m) (Fin m) SignType),
    IsASM M ∧ ¬ Contains312 M ∧
      ∀ i j, M (Fin.castLE hr i) (Fin.castLE hk j) = R i j

def nonemptyRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : ℕ :=
  letI : DecidablePred (fun i : Fin r => ∃ j : Fin k, R i j ≠ 0) :=
    fun i => inferInstance
  (univ.filter (fun i : Fin r => ∃ j : Fin k, R i j ≠ 0)).card

private instance decidableEndsOne {n : ℕ} (a : Fin n → SignType) : Decidable (EndsOne a) := by
  unfold EndsOne
  infer_instance

noncomputable def S (r k d : ℕ) : ℕ :=
  Nat.card {R : Matrix (Fin r) (Fin k) SignType //
    IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R = d}

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma line_embed {n m : ℕ} (a : Fin n → SignType) (b : Fin m → SignType)
    (f : Fin n → Fin m) (hf : StrictMono f) (hval : ∀ u, b (f u) = a u)
    (hout : ∀ x, (¬ ∃ u, f u = x) → b x = 0)
    (ha : Alternates a) (hs : StartsOne a) : Alternates b ∧ StartsOne b := by
  classical
  have hpre (x : Fin m) (hx : b x ≠ 0) : ∃ u, f u = x := by
    by_contra hn
    exact hx (hout x hn)
  refine ⟨?_,?_⟩
  · intro x y hxy hx hy hgap
    obtain ⟨u,rfl⟩ := hpre x hx
    obtain ⟨v,rfl⟩ := hpre y hy
    simp only [hval] at hx hy ⊢
    apply ha u v (hf.lt_iff_lt.mp hxy) hx hy
    intro w huw hwv
    simpa only [hval] using hgap (f w) (hf huw) (hf hwv)
  · intro x hx hgap
    obtain ⟨u,rfl⟩ := hpre x hx
    rw [hval] at hx ⊢
    apply hs u hx
    intro v hvu
    simpa only [hval] using hgap (f v) (hf hvu)

lemma ends_embed {n m : ℕ} (a : Fin n → SignType) (b : Fin m → SignType)
    (f : Fin n → Fin m) (hf : StrictMono f) (hval : ∀ u, b (f u) = a u)
    (hout : ∀ x, (¬ ∃ u, f u = x) → b x = 0) (he : EndsOne a) : EndsOne b := by
  classical
  intro x hx hgap
  have hpre : ∃ u, f u = x := by
    by_contra hn
    exact hx (hout x hn)
  obtain ⟨u,rfl⟩ := hpre
  rw [hval] at hx ⊢
  apply he u hx
  intro v huv
  simpa only [hval] using hgap (f v) (hf huv)

lemma sum_embed {n m : ℕ} (a : Fin n → SignType) (b : Fin m → SignType)
    (f : Fin n → Fin m) (hf : StrictMono f) (hval : ∀ u, b (f u) = a u)
    (hout : ∀ x, (¬ ∃ u, f u = x) → b x = 0) :
    (∑ u, (a u : ℤ)) = ∑ x, (b x : ℤ) := by
  classical
  apply sum_bij_ne_zero (fun u _ _ => f u)
  · intro u _ _
    exact mem_univ _
  · intro u _ _ v _ _ heq
    exact hf.injective heq
  · intro x _ hx
    have hpre : ∃ u, f u = x := by
      by_contra hn
      rw [hout x hn] at hx
      simp at hx
    obtain ⟨u,rfl⟩ := hpre
    refine ⟨u,mem_univ _,?_,rfl⟩
    simpa only [hval] using hx
  · intro u _ _
    rw [hval]

lemma singleton_line {n : ℕ} (p : Fin n) :
    Alternates (fun j => if p = j then 1 else 0) ∧
      StartsOne (fun j => if p = j then 1 else 0) ∧
      EndsOne (fun j => if p = j then 1 else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hx hy _
    have hp : p = x := by simpa using hx
    have hq : p = y := by simpa using hy
    subst x
    subst y
    exact (lt_irrefl _ hxy).elim
  · intro x hx _
    have hp : p = x := by simpa using hx
    simp [hp]
  · intro x hx _
    have hp : p = x := by simpa using hx
    simp [hp]

private lemma permMatrix_isASR {m : ℕ} (σ : Equiv.Perm (Fin m)) : IsASR (σ.permMatrix SignType) := by
  constructor
  · intro i
    have hrow : σ.permMatrix SignType i = (fun j => if σ i = j then 1 else 0) := by
      funext j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.of_apply,
        Equiv.toPEquiv_apply, Option.mem_def, eq_comm]
    rw [hrow]
    exact singleton_line (σ i)
  · intro j
    have hcol : (fun i => σ.permMatrix SignType i j) =
        (fun i => if σ.symm j = i then 1 else 0) := by
      funext i
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.of_apply,
        Equiv.toPEquiv_apply, Option.mem_def, Equiv.eq_symm_apply, eq_comm]
    rw [hcol]
    exact ⟨(singleton_line (σ.symm j)).1, (singleton_line (σ.symm j)).2.1⟩

private lemma permMatrix_cast {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    (σ.permMatrix SignType i j : ℤ) = if σ i = j then 1 else 0 := by
  by_cases h : σ i = j
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.of_apply,
      Equiv.toPEquiv_apply, Option.mem_def, h]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Matrix.of_apply,
      Equiv.toPEquiv_apply, Option.mem_def, h, Ne.symm h]

private lemma permMatrix_isASM {m : ℕ} (σ : Equiv.Perm (Fin m)) : IsASM (σ.permMatrix SignType) := by
  refine ⟨permMatrix_isASR σ, ?_, ?_⟩
  · intro i
    simp_rw [permMatrix_cast]
    simp
  · intro j
    have e (i : Fin m) : σ i = j ↔ i = σ.symm j := by
      exact σ.apply_eq_iff_eq_symm_apply
    simp_rw [permMatrix_cast, e]
    simp

private lemma antiDiag_avoids {m : ℕ} : ¬ Contains312 (((Fin.revPerm : Equiv.Perm (Fin m)).permMatrix SignType)) := by
  rintro ⟨i₁, i₂, i₃, j₁, j₂, j₃, h₁₂, h₂₃, hj₁₂, hj₂₃, ha, hb, hc⟩
  have eb : i₂.rev = j₁ := by simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, Option.mem_def, eq_comm] using hb
  have ec : i₃.rev = j₂ := by simpa [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, Option.mem_def, eq_comm] using hc
  have hrev := Fin.rev_lt_rev.mpr h₂₃
  rw [eb, ec] at hrev
  exact (lt_asymm hrev hj₁₂)

private lemma zero_isASR (r k : ℕ) : IsASR (0 : Matrix (Fin r) (Fin k) SignType) := by
  constructor
  · intro i
    refine ⟨?_, ?_, ?_⟩ <;> simp [Alternates, StartsOne, EndsOne]
  · intro j
    refine ⟨?_, ?_⟩ <;> simp [Alternates, StartsOne]

private lemma zero_extAvoids312 (r k : ℕ) :
    ExtAvoids312 (0 : Matrix (Fin r) (Fin k) SignType) := by
  refine ⟨r + k, by omega, by omega, (Fin.revPerm.permMatrix SignType),
    permMatrix_isASM _, antiDiag_avoids, ?_⟩
  intro i j
  have hne : (Fin.castLE (show r ≤ r + k by omega) i).rev ≠
      Fin.castLE (show k ≤ r + k by omega) j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at hv
    have hi := i.isLt
    have hj := j.isLt
    omega
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix, Equiv.toPEquiv_apply, Option.mem_def, eq_comm, hne]

private lemma nonemptyRows_eq_zero_iff {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows R = 0 ↔ R = 0 := by
  classical
  constructor
  · intro h
    simp only [nonemptyRows, card_eq_zero, filter_eq_empty_iff, mem_univ,
      forall_const, not_exists, not_not] at h
    ext i j
    exact h j
  · rintro rfl
    simp [nonemptyRows]

lemma S_zero (r k : ℕ) : S r k 0 = 1 := by
  classical
  let zero : {R : Matrix (Fin r) (Fin k) SignType //
      IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R = 0} :=
    ⟨0, zero_isASR r k, zero_extAvoids312 r k, (nonemptyRows_eq_zero_iff 0).mpr rfl⟩
  let e : {R : Matrix (Fin r) (Fin k) SignType //
      IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R = 0} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => zero
      left_inv := by
        intro x
        apply Subtype.ext
        exact (nonemptyRows_eq_zero_iff x.val).mp x.property.2.2 |>.symm
      right_inv := by intro x; cases x; rfl }
  exact (Nat.card_congr e).trans (by simp)

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma row_has_one {m : ℕ} {M : Matrix (Fin m) (Fin m) SignType}
    (hM : IsASM M) (i : Fin m) : ∃ j, M i j = 1 := by
  by_contra h
  push Not at h
  have heach (j : Fin m) : (M i j : ℤ) ≤ 0 := by
    have hx := h j
    cases he : M i j <;> simp_all [SignType.cast]
  have hs : (∑ j, (M i j : ℤ)) ≤ 0 := sum_nonpos fun j _ => heach j
  rw [hM.2.1 i] at hs
  omega

lemma empty_row_extension_one {r k m : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hr : r ≤ m) (hk : k ≤ m) (M : Matrix (Fin m) (Fin m) SignType)
    (hM : IsASM M) (hext : ∀ i j, M (Fin.castLE hr i) (Fin.castLE hk j) = R i j)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) :
    ∃ j : Fin m, k ≤ j.val ∧ M (Fin.castLE hr i₀) j = 1 := by
  obtain ⟨j, hj⟩ := row_has_one hM (Fin.castLE hr i₀)
  refine ⟨j, ?_, hj⟩
  by_contra h
  have hsmall : j.val < k := by omega
  let jj : Fin k := ⟨j.val, hsmall⟩
  have he : Fin.castLE hk jj = j := by apply Fin.ext; rfl
  have hz := hext i₀ jj
  rw [he, hempty jj, hj] at hz
  exact (by decide : (1 : SignType) ≠ 0) hz

lemma no12_below_empty {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hext : ExtAvoids312 R) (i₀ i₁ i₂ : Fin r) (j₁ j₂ : Fin k)
    (h₀₁ : i₀ < i₁) (h₁₂ : i₁ < i₂) (hj : j₁ < j₂)
    (hempty : ∀ j, R i₀ j = 0) : ¬ (R i₁ j₁ = 1 ∧ R i₂ j₂ = 1) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := hext
  obtain ⟨j₃, hright, h₃⟩ := empty_row_extension_one R hr hk M hM hcorner i₀ hempty
  apply hav
  refine ⟨Fin.castLE hr i₀, Fin.castLE hr i₁, Fin.castLE hr i₂,
    Fin.castLE hk j₁, Fin.castLE hk j₂, j₃, ?_, ?_, ?_, ?_, h₃, ?_, ?_⟩
  · exact h₀₁
  · exact h₁₂
  · exact hj
  · change j₂.val < j₃.val
    have hb := j₂.isLt
    omega
  · rw [hcorner, h₁]
  · rw [hcorner, h₂]

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma prefix_line {n p : ℕ} (hp : p ≤ n) (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) :
    Alternates (fun i : Fin p => a (Fin.castLE hp i)) ∧
      StartsOne (fun i : Fin p => a (Fin.castLE hp i)) := by
  constructor
  · intro x y hxy hx hy hz
    apply ha (Fin.castLE hp x) (Fin.castLE hp y) hxy hx hy
    intro z hxz hzy
    have hzsmall : z.val < p := by
      change z.val < y.val at hzy
      have hyb := y.isLt
      omega
    let zp : Fin p := ⟨z.val, hzsmall⟩
    have he : Fin.castLE hp zp = z := by apply Fin.ext; rfl
    rw [← he]
    apply hz zp
    · exact hxz
    · exact hzy
  · intro x hx hz
    apply hs (Fin.castLE hp x) hx
    intro y hy
    have hysmall : y.val < p := by
      change y.val < x.val at hy
      have hxb := x.isLt
      omega
    let yp : Fin p := ⟨y.val, hysmall⟩
    have he : Fin.castLE hp yp = y := by apply Fin.ext; rfl
    rw [← he]
    exact hz yp hy

def topRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    {p : ℕ} (hp : p ≤ r) : Matrix (Fin p) (Fin k) SignType :=
  fun i j => R (Fin.castLE hp i) j

lemma topRows_isASR {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hp : p ≤ r) (hR : IsASR R) : IsASR (topRows R hp) := by
  constructor
  · intro i
    exact hR.1 (Fin.castLE hp i)
  · intro j
    exact prefix_line hp (fun i => R i j) (hR.2 j).1 (hR.2 j).2

lemma topRows_extAvoids312 {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hp : p ≤ r) (hR : ExtAvoids312 R) : ExtAvoids312 (topRows R hp) := by
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := hR
  refine ⟨m, hp.trans hr, hk, M, hM, hav, ?_⟩
  intro i j
  have he : Fin.castLE hr (Fin.castLE hp i) = Fin.castLE (hp.trans hr) i := by
    apply Fin.ext
    rfl
  rw [← he, hcorner]
  rfl

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

def LineState {n : ℕ} (a : Fin n → SignType) : Prop :=
  ((∀ i, a i = 0) ∧ (∑ i, (a i : ℤ)) = 0) ∨
    ∃ x, a x ≠ 0 ∧ (∀ y, x < y → a y = 0) ∧
      (∑ i, (a i : ℤ)) = if a x = 1 then 1 else 0

lemma alternating_line_state {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) : LineState a := by
  induction n with
  | zero =>
      left
      exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ n ih =>
      let b : Fin n → SignType := fun i => a i.castSucc
      have hb : Alternates b ∧ StartsOne b :=
        prefix_line (Nat.le_succ n) a ha hs
      have hstate := ih b hb.1 hb.2
      have hsum : (∑ i, (a i : ℤ)) = (∑ i, (b i : ℤ)) + (a (Fin.last n) : ℤ) :=
        Fin.sum_univ_castSucc _
      by_cases hz : a (Fin.last n) = 0
      · rcases hstate with ⟨hzero, htotal⟩ | ⟨x, hx, htail, htotal⟩
        · left
          refine ⟨?_, by simp [hsum, htotal, hz]⟩
          intro i
          refine Fin.lastCases hz (fun j => hzero j) i
        · right
          refine ⟨x.castSucc, hx, ?_, ?_⟩
          · intro y hy
            revert hy
            refine Fin.lastCases (fun _ => hz) (fun j hy => htail j hy) y
          · simpa [hsum, hz] using htotal
      · have hprev (x : Fin n) : x.castSucc < Fin.last n := Fin.castSucc_lt_last x
        have hlast : ∀ y : Fin (n + 1), Fin.last n < y → a y = 0 := by
          intro y hy
          exact (not_lt_of_ge (Fin.le_last y) hy).elim
        rcases hstate with ⟨hzero, htotal⟩ | ⟨x, hx, htail, htotal⟩
        · have hfirst : a (Fin.last n) = 1 := by
            apply hs (Fin.last n) hz
            intro y hy
            revert hy
            refine Fin.lastCases (fun hy => (lt_irrefl _ hy).elim)
              (fun j _ => hzero j) y
          right
          refine ⟨Fin.last n, hz, hlast, ?_⟩
          simp [hsum, htotal, hfirst]
        · have hdiff : b x ≠ a (Fin.last n) := by
            apply ha x.castSucc (Fin.last n) (hprev x) hx hz
            intro z hxz hzl
            revert hxz hzl
            refine Fin.lastCases (fun _ hzl => (lt_irrefl _ hzl).elim)
              (fun j hxz _ => htail j hxz) z
          right
          refine ⟨Fin.last n, hz, hlast, ?_⟩
          rw [hsum, htotal]
          cases he : b x <;> cases hf : a (Fin.last n) <;>
            simp_all [SignType.cast]

private lemma alternating_line_sum {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) :
    (∑ i, (a i : ℤ)) = 0 ∨ (∑ i, (a i : ℤ)) = 1 := by
  rcases alternating_line_state a ha hs with ⟨_, h⟩ | ⟨x, _, _, h⟩
  · exact Or.inl h
  · by_cases hx : a x = 1 <;> simp [hx] at h
    · exact Or.inr h
    · exact Or.inl h

private lemma complete_line_sum_eq_indicator {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) (he : EndsOne a) :
    (∑ i, (a i : ℤ)) = if ∃ i, a i ≠ 0 then 1 else 0 := by
  classical
  rcases alternating_line_state a ha hs with ⟨hz, hsum⟩ | ⟨x, hx, htail, hsum⟩
  · have hempty : ¬ ∃ i, a i ≠ 0 := by rintro ⟨i, hi⟩; exact hi (hz i)
    simp [hempty, hsum]
  · have hone := he x hx htail
    have hex : ∃ i, a i ≠ 0 := ⟨x, hx⟩
    simpa [hex, hone] using hsum

lemma asr_row_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (i : Fin r) :
    (∑ j, (R i j : ℤ)) = if ∃ j, R i j ≠ 0 then 1 else 0 :=
  complete_line_sum_eq_indicator _ (hR.1 i).1 (hR.1 i).2.1 (hR.1 i).2.2

lemma asr_row_sum_one_iff {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (i : Fin r) :
    (∑ j, (R i j : ℤ)) = 1 ↔ ∃ j, R i j ≠ 0 := by
  classical
  rw [asr_row_sum R hR i]
  split_ifs <;> simp_all

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma one_before_minus {n : ℕ} (a : Fin n → SignType) (hs : StartsOne a)
    (x : Fin n) (hx : a x = -1) : ∃ y, y < x ∧ a y = 1 := by
  classical
  let s := univ.filter (fun y => a y ≠ 0)
  have hxm : x ∈ s := by simp [s, hx]
  have hne : s.Nonempty := ⟨x, hxm⟩
  let y := s.min' hne
  have hym : y ∈ s := s.min'_mem hne
  have hyn : a y ≠ 0 := (mem_filter.mp hym).2
  have hyx : y ≤ x := s.min'_le x hxm
  have hfirst : ∀ z, z < y → a z = 0 := by
    intro z hzy
    by_contra hz
    have hzm : z ∈ s := mem_filter.mpr ⟨mem_univ _, hz⟩
    exact (not_lt_of_ge (s.min'_le z hzm)) hzy
  have hone := hs y hyn hfirst
  refine ⟨y, lt_of_le_of_ne hyx ?_, hone⟩
  intro heq
  rw [heq, hx] at hone
  exact (by decide : (-1 : SignType) ≠ 1) hone

lemma one_after_minus_of_ends {n : ℕ} (a : Fin n → SignType) (he : EndsOne a)
    (x : Fin n) (hx : a x = -1) : ∃ y, x < y ∧ a y = 1 := by
  classical
  let s := univ.filter (fun y => a y ≠ 0)
  have hxm : x ∈ s := by simp [s, hx]
  have hne : s.Nonempty := ⟨x, hxm⟩
  let y := s.max' hne
  have hym : y ∈ s := s.max'_mem hne
  have hyn : a y ≠ 0 := (mem_filter.mp hym).2
  have hxy : x ≤ y := s.le_max' x hxm
  have hlast : ∀ z, y < z → a z = 0 := by
    intro z hyz
    by_contra hz
    have hzm : z ∈ s := mem_filter.mpr ⟨mem_univ _, hz⟩
    exact (not_lt_of_ge (s.le_max' z hzm)) hyz
  have hone := he y hyn hlast
  refine ⟨y, lt_of_le_of_ne hxy ?_, hone⟩
  intro heq
  rw [← heq, hx] at hone
  exact (by decide : (-1 : SignType) ≠ 1) hone

lemma line_sum_one_ends_one {n : ℕ} (a : Fin n → SignType)
    (ha : Alternates a) (hs : StartsOne a) (ht : (∑ i, (a i : ℤ)) = 1) :
    EndsOne a := by
  rcases alternating_line_state a ha hs with ⟨hz, hsum⟩ | ⟨x, hx, htail, hsum⟩
  · omega
  · have hone : a x = 1 := by
      by_contra hn
      simp only [hn, if_false] at hsum
      omega
    intro y hy hylast
    have heq : y = x := by
      rcases lt_trichotomy y x with h | h | h
      · exact (hx (hylast x h)).elim
      · exact h
      · exact (hy (htail y h)).elim
    simpa [heq] using hone

lemma asm_column_ends_one {m : ℕ} {M : Matrix (Fin m) (Fin m) SignType}
    (hM : IsASM M) (j : Fin m) : EndsOne (fun i => M i j) :=
  line_sum_one_ends_one _ (hM.1.2 j).1 (hM.1.2 j).2 (hM.2.2 j)

private lemma asm_row_minus_unique {m : ℕ} {M : Matrix (Fin m) (Fin m) SignType}
    (hM : IsASM M) (hav : ¬ Contains312 M) (i : Fin m) (j₁ j₂ : Fin m)
    (h₁ : M i j₁ = -1) (h₂ : M i j₂ = -1) : j₁ = j₂ := by
  suffices h : ∀ a b : Fin m, a < b → M i a = -1 → M i b = -1 → False by
    rcases lt_trichotomy j₁ j₂ with hlt | heq | hlt
    · exact (h j₁ j₂ hlt h₁ h₂).elim
    · exact heq
    · exact (h j₂ j₁ hlt h₂ h₁).elim
  intro a b hab ha hb
  obtain ⟨l, hla, hl⟩ := one_before_minus (M i) (hM.1.1 i).2.1 a ha
  obtain ⟨u, hui, hu⟩ := one_before_minus (fun x => M x b) (hM.1.2 b).2 i hb
  obtain ⟨v, hiv, hv⟩ := one_after_minus_of_ends (fun x => M x a)
    (asm_column_ends_one hM a) i ha
  exact hav ⟨u, i, v, l, a, b, hui, hiv, hla, hab, hu, hl, hv⟩

private lemma asm_column_minus_unique {m : ℕ} {M : Matrix (Fin m) (Fin m) SignType}
    (hM : IsASM M) (hav : ¬ Contains312 M) (j : Fin m) (i₁ i₂ : Fin m)
    (h₁ : M i₁ j = -1) (h₂ : M i₂ j = -1) : i₁ = i₂ := by
  suffices h : ∀ a b : Fin m, a < b → M a j = -1 → M b j = -1 → False by
    rcases lt_trichotomy i₁ i₂ with hlt | heq | hlt
    · exact (h i₁ i₂ hlt h₁ h₂).elim
    · exact heq
    · exact (h i₂ i₁ hlt h₂ h₁).elim
  intro a b hab ha hb
  obtain ⟨u, hju, hu⟩ := one_after_minus_of_ends (M a) (hM.1.1 a).2.2 j ha
  obtain ⟨l, hlj, hl⟩ := one_before_minus (M b) (hM.1.1 b).2.1 j hb
  obtain ⟨v, hbv, hv⟩ := one_after_minus_of_ends (fun x => M x j)
    (asm_column_ends_one hM j) b hb
  exact hav ⟨a, b, v, l, j, u, hab, hbv, hlj, hju, hu, hl, hv⟩

lemma asr_row_minus_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) (i : Fin r) (j₁ j₂ : Fin k)
    (h₁ : R i j₁ = -1) (h₂ : R i j₂ = -1) : j₁ = j₂ := by
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := he
  have h := asm_row_minus_unique hM hav (Fin.castLE hr i)
    (Fin.castLE hk j₁) (Fin.castLE hk j₂)
    (by rw [hcorner]; exact h₁) (by rw [hcorner]; exact h₂)
  exact Fin.castLE_injective hk h

lemma asr_column_minus_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (he : ExtAvoids312 R) (j : Fin k) (i₁ i₂ : Fin r)
    (h₁ : R i₁ j = -1) (h₂ : R i₂ j = -1) : i₁ = i₂ := by
  obtain ⟨m, hr, hk, M, hM, hav, hcorner⟩ := he
  have h := asm_column_minus_unique hM hav (Fin.castLE hk j)
    (Fin.castLE hr i₁) (Fin.castLE hr i₂)
    (by rw [hcorner]; exact h₁) (by rw [hcorner]; exact h₂)
  exact Fin.castLE_injective hr h

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma minus_between_ones {n : ℕ} (a : Fin n → SignType) (ha : Alternates a)
    (x y : Fin n) (hxy : x < y) (hx : a x = 1) (hy : a y = 1) :
    ∃ z, x < z ∧ z < y ∧ a z = -1 := by
  classical
  let s := univ.filter (fun z => x < z ∧ a z ≠ 0)
  have hym : y ∈ s := by simp [s,hxy,hy]
  have hne : s.Nonempty := ⟨y,hym⟩
  let z := s.min' hne
  have hzm : z ∈ s := s.min'_mem hne
  have hzn : a z ≠ 0 := (mem_filter.mp hzm).2.2
  have hxz : x < z := (mem_filter.mp hzm).2.1
  have hzy : z ≤ y := s.min'_le y hym
  have hgap : ∀ w, x < w → w < z → a w = 0 := by
    intro w hxw hwz
    by_contra hw
    have hwm : w ∈ s := mem_filter.mpr ⟨mem_univ _,hxw,hw⟩
    exact not_lt_of_ge (s.min'_le w hwm) hwz
  have hdiff := ha x z hxz (by simp [hx]) hzn hgap
  have hminus : a z = -1 := by cases he : a z <;> simp_all
  have hnezy : z ≠ y := by
    intro h
    rw [h,hy] at hminus
    exact (by decide : (1 : SignType) ≠ -1) hminus
  exact ⟨z,hxz,lt_of_le_of_ne hzy hnezy,hminus⟩

lemma asr_first_col_not_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hk : 0 < k) (i : Fin r) : R i ⟨0,hk⟩ ≠ -1 := by
  intro hminus
  have hfirst : R i ⟨0,hk⟩ = 1 := by
    apply (hR.1 i).2.1 ⟨0,hk⟩
    · simp [hminus]
    · intro y hy
      exact (Nat.not_lt_zero y.val hy).elim
  rw [hminus] at hfirst
  exact (by decide : (-1 : SignType) ≠ 1) hfirst

lemma asr_first_col_one_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hk : 0 < k) (a b : Fin r)
    (ha : R a ⟨0,hk⟩ = 1) (hb : R b ⟨0,hk⟩ = 1) : a = b := by
  suffices h : ∀ a b : Fin r, a < b → R a ⟨0,hk⟩ = 1 → R b ⟨0,hk⟩ = 1 → False by
    rcases lt_trichotomy a b with hlt | hEq | hlt
    · exact (h a b hlt ha hb).elim
    · exact hEq
    · exact (h b a hlt hb ha).elim
  intro a b hab ha hb
  obtain ⟨z,_,_,hz⟩ := minus_between_ones (fun i => R i ⟨0,hk⟩) (hR.2 _).1 a b hab ha hb
  exact asr_first_col_not_minus R hR hk z hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma line_no_minus_singleton {n : ℕ} (a : Fin n → SignType) (ha : Alternates a)
    (hn : ∀ x, a x ≠ -1) (p : Fin n) (hp : a p = 1) :
    ∀ x, a x = if x = p then 1 else 0 := by
  intro x
  by_cases hx : x = p
  · simp [hx,hp]
  · rw [if_neg hx]
    by_contra hx0
    have hx1 : a x = 1 := by have := hn x; cases he : a x <;> simp_all
    rcases lt_or_gt_of_ne hx with hxp | hpx
    · obtain ⟨z,_,_,hz⟩ := minus_between_ones a ha x p hxp hx1 hp
      exact hn z hz
    · obtain ⟨z,_,_,hz⟩ := minus_between_ones a ha p x hpx hp hx1
      exact hn z hz

lemma asr_first_row_not_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hr : 0 < r) (c : Fin k) : R ⟨0,hr⟩ c ≠ -1 := by
  intro hm
  have hs : R ⟨0,hr⟩ c = 1 := by
    apply (hR.2 c).2 ⟨0,hr⟩ (by simp [hm])
    intro u hu
    exact (Nat.not_lt_zero u.val hu).elim
  rw [hm] at hs
  exact (by decide : (-1 : SignType) ≠ 1) hs

lemma asr_first_row_singleton {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hr : 0 < r) (hne : ∃ c, R ⟨0,hr⟩ c ≠ 0) :
    ∃ p, ∀ c, R ⟨0,hr⟩ c = if c = p then 1 else 0 := by
  obtain ⟨p,hp⟩ := hne
  have hp1 : R ⟨0,hr⟩ p = 1 := by
    have hn := asr_first_row_not_minus R hR hr p
    cases hs : R ⟨0,hr⟩ p <;> simp_all
  exact ⟨p,line_no_minus_singleton _ (hR.1 _).1 (asr_first_row_not_minus R hR hr) p hp1⟩

lemma three_sign_line {n : ℕ} (x z y : Fin n) (hxz : x < z) (hzy : z < y) :
    let a := fun w => if w = x then (1 : SignType) else if w = z then -1 else if w = y then 1 else 0
    Alternates a ∧ StartsOne a ∧ EndsOne a := by
  dsimp
  let a := fun w => if w = x then (1 : SignType) else if w = z then -1 else if w = y then 1 else 0
  change Alternates a ∧ StartsOne a ∧ EndsOne a
  have hx : a x = 1 := by simp [a]
  have hz : a z = -1 := by simp [a,ne_of_gt hxz]
  have hy : a y = 1 := by simp [a,ne_of_gt hzy,ne_of_gt (lt_trans hxz hzy)]
  have hsupport (w : Fin n) (hw : a w ≠ 0) : w = x ∨ w = z ∨ w = y := by
    by_contra hn
    push_neg at hn
    simp [a,hn] at hw
  refine ⟨?_,?_,?_⟩
  · intro u v huv hu hv hgap
    rcases hsupport u hu with rfl | rfl | rfl <;>
      rcases hsupport v hv with rfl | rfl | rfl
    all_goals try exact (lt_irrefl _ huv).elim
    all_goals try exact (not_lt_of_ge (le_of_lt hxz) huv).elim
    all_goals try exact (not_lt_of_ge (le_of_lt hzy) huv).elim
    all_goals try exact (not_lt_of_ge (le_of_lt (lt_trans hxz hzy)) huv).elim
    · simp [hx,hz]
    · have hf := hgap z hxz hzy
      rw [hz] at hf
      exact (by decide : (-1 : SignType) ≠ 0) hf |>.elim
    · simp [hz,hy]
  · intro u hu hgap
    rcases hsupport u hu with rfl | rfl | rfl
    · exact hx
    · have hf := hgap x hxz
      rw [hx] at hf
      exact (by decide : (1 : SignType) ≠ 0) hf |>.elim
    · have hf := hgap x (lt_trans hxz hzy)
      rw [hx] at hf
      exact (by decide : (1 : SignType) ≠ 0) hf |>.elim
  · intro u hu hgap
    rcases hsupport u hu with rfl | rfl | rfl
    · have hf := hgap y (lt_trans hxz hzy)
      rw [hy] at hf
      exact (by decide : (1 : SignType) ≠ 0) hf |>.elim
    · have hf := hgap y hzy
      rw [hy] at hf
      exact (by decide : (1 : SignType) ≠ 0) hf |>.elim
    · exact hy

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

noncomputable def emptyRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Finset (Fin r) := by
  classical
  exact univ.filter (fun i => ∀ j, R i j = 0)

def colSum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (j : Fin k) : ℤ :=
  ∑ i, (R i j : ℤ)

noncomputable def deficientColumns {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) : Finset (Fin k) := by
  classical
  exact univ.filter (fun j => colSum R j = 0)

lemma mem_emptyRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (i : Fin r) :
    i ∈ emptyRows R ↔ ∀ j, R i j = 0 := by
  classical
  simp [emptyRows]

lemma mem_deficientColumns {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (j : Fin k) :
    j ∈ deficientColumns R ↔ colSum R j = 0 := by
  classical
  simp [deficientColumns]

lemma asr_col_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (j : Fin k) : colSum R j = 0 ∨ colSum R j = 1 :=
  alternating_line_sum _ (hR.2 j).1 (hR.2 j).2

lemma asr_total_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : (∑ i, ∑ j, (R i j : ℤ)) = nonemptyRows R := by
  letI : DecidablePred (fun i : Fin r => ∃ j : Fin k, R i j ≠ 0) := fun i => inferInstance
  simp_rw [asr_row_sum R hR]
  unfold nonemptyRows
  exact sum_boole _ _

lemma emptyRows_balance {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    (emptyRows R).card + nonemptyRows R = r := by
  classical
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin r)))
    (p := fun i => ∀ j, R i j = 0)
  simpa [emptyRows, nonemptyRows, not_forall] using h

lemma deficientColumns_balance {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : (deficientColumns R).card + nonemptyRows R = k := by
  classical
  have hcol (j : Fin k) : colSum R j = 1 - (if colSum R j = 0 then 1 else 0) := by
    rcases asr_col_sum R hR j with h | h <;> simp [h]
  have hsum : (∑ j, colSum R j) = (k : ℤ) - (deficientColumns R).card := by
    calc
      (∑ j, colSum R j) = ∑ j, (1 - (if colSum R j = 0 then (1 : ℤ) else 0)) :=
        sum_congr rfl (fun j _ => hcol j)
      _ = _ := by
        rw [sum_sub_distrib]
        simp [deficientColumns, ← sum_filter]
  have ht := asr_total_sum R hR
  rw [sum_comm] at ht
  change (∑ j, colSum R j) = _ at ht
  omega

lemma nonemptyRows_le_rows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows R ≤ r := by
  have := emptyRows_balance R
  omega

lemma nonemptyRows_le_columns {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) : nonemptyRows R ≤ k := by
  have := deficientColumns_balance R hR
  omega

lemma balanced_column_sum {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hd : nonemptyRows R = k) (j : Fin k) : colSum R j = 1 := by
  have hb := deficientColumns_balance R hR
  have hzero : (deficientColumns R).card = 0 := by omega
  have hne : j ∉ deficientColumns R := by rw [card_eq_zero.mp hzero]; simp
  exact (asr_col_sum R hR j).resolve_left (fun h => hne ((mem_deficientColumns R j).mpr h))

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

namespace D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma prefix_sum_as_filter {n p : ℕ} (hp : p ≤ n) (a : Fin n → SignType) :
    (∑ i : Fin p, (a (Fin.castLE hp i) : ℤ)) =
      ∑ i ∈ univ.filter (fun i : Fin n => i.val < p), (a i : ℤ) := by
  apply sum_bij (fun i _ => Fin.castLE hp i)
  · intro i _
    simp [i.isLt]
  · intro i _ j _ hij
    exact Fin.castLE_injective hp hij
  · intro j hj
    have hsmall : j.val < p := (mem_filter.mp hj).2
    exact ⟨⟨j.val, hsmall⟩, mem_univ _, by apply Fin.ext; rfl⟩
  · intro i _
    rfl

lemma one_after_zero_prefix {n p : ℕ} (hp : p ≤ n) (a : Fin n → SignType)
    (ht : (∑ i, (a i : ℤ)) = 1)
    (hz : (∑ i : Fin p, (a (Fin.castLE hp i) : ℤ)) = 0) :
    ∃ i, p ≤ i.val ∧ a i = 1 := by
  classical
  rw [prefix_sum_as_filter hp a] at hz
  by_contra h
  push_neg at h
  have hneg : ∑ i ∈ univ.filter (fun i : Fin n => ¬ i.val < p), (a i : ℤ) ≤ 0 := by
    apply sum_nonpos
    intro i hi
    have hp' : p ≤ i.val := Nat.le_of_not_gt (mem_filter.mp hi).2
    have hn := h i hp'
    cases he : a i <;> simp_all [SignType.cast]
  have hsum := sum_filter_add_sum_filter_not (s := univ) (f := fun i : Fin n => (a i : ℤ))
    (p := fun i => i.val < p)
  rw [ht, hz] at hsum
  omega

lemma deficient_column_extension_one {r k m : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hr : r ≤ m) (hk : k ≤ m) (M : Matrix (Fin m) (Fin m) SignType)
    (hM : IsASM M) (hcorner : ∀ i j, M (Fin.castLE hr i) (Fin.castLE hk j) = R i j)
    (j : Fin k) (hz : (∑ i, (R i j : ℤ)) = 0) :
    ∃ i : Fin m, r ≤ i.val ∧ M i (Fin.castLE hk j) = 1 := by
  apply one_after_zero_prefix hr (fun i => M i (Fin.castLE hk j)) (hM.2.2 _)
  simpa only [hcorner] using hz

end D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

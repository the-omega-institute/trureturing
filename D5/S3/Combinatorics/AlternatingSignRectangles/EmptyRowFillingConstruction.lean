/- GID: D5/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/AlternatingSignRectangles/EmptyRowFillingConstruction
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: EmptyRowFillingConstruction for extendably 312-avoiding rectangles. -/

/-
admission_basis: escape-witness
counted_outside_isEmpty: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
S_outside_nat: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
S_outside: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
nonemptyRows_eq_card_subtype: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.first_empty_row_exists, D5.S3.Combinatorics.AlternatingSignRectangles.RowCompleteRecurrence.pivot_nonempty_bound
first_empty_row_exists: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.firstEmptyPart
topRows_nonemptyRows_of_before: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.extractFibre, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.first_empty_tail_card, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_one_column_bound, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_shift_column_sum, D5.S3.Combinatorics.AlternatingSignRectangles.SquarePrefixGeometry.prefix_width
balanced_below_empty_no_minus: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
balanced_below_empty_nonneg: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
balanced_below_empty_one_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
balanced_below_empty_singleton: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
topRows_col_sum_filter: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.topRows_col_sum_add_tail
topRows_col_sum_add_tail: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_one_iff_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_sum_le_one
balanced_tail_sum_le_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
balanced_tail_one_iff_deficient: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
balanced_tail_column_one_unique: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_column_one_unique
balanced_tail_strict_decreasing: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_tail_column_one_unique
mem_tailRows: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balancedTailEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balancedTailEquiv_strictAnti, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailChoiceEquiv, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailColumn, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailColumn_deficient, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailColumn_entries
tailColumn_entries: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
tailColumn_one: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
tailColumn_deficient: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
balancedTail_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
balancedTailEquiv_strictAnti: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
first_empty_tail_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
strictAnti_equiv_sorted: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct
mem_tailChoice: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tailChoice, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.tailChoiceEquiv
first_empty_choice_card: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.balanced_below_empty_one_unique
fillTail_selected_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tailChoice, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
fillTail_deficient_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
selectedRowAt_mem: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.fillTail_unselected_row
selectedRowAt_surjective: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tailChoice, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
fillTail_unselected_row: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.fillTail_reconstruct, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tailChoice, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
fillTail_complete_col: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
filledRect_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_top, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_function, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_old, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
filledRect_empty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_empty, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_function, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_one_tail, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
filledRect_tail: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_tail, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_function, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_one_tail, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_row_line
fillTail_decreasing: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
zero_before_singleton: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
filledRect_row_line: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_isASR
filledRect_col_function: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_line, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_col_sum
filledRect_col_line: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRect_isASR: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRect_col_sum: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
filledRect_nonemptyRows: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.SignLines.alternating_line_state
rowComplete_nonempty: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFilling.filledRectAt_before, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_empty_not_top
filledRect_old: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_empty_not_top, D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
filledRect_one_tail: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
filledRect_empty_not_top: proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
filledRect_safe: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
filledRect_extAvoids312: proof_shape: content; escape_witness: D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction.filledRect_safe
Direct frozen dependencies: none; the ASR prerequisites are same-delivery content.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14871
-/

import D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.SignLines

abbrev Counted (r k d : ℕ) :=
  {R : Matrix (Fin r) (Fin k) SignType // IsASR R ∧ ExtAvoids312 R ∧ nonemptyRows R = d}

private lemma counted_outside_isEmpty (r k d : ℕ) (h : r < d ∨ k < d) : IsEmpty (Counted r k d) := by
  constructor
  intro R
  have hr := nonemptyRows_le_rows R.val
  have hk := nonemptyRows_le_columns R.val R.property.1
  have hd := R.property.2.2
  rcases h with h | h <;> omega

private lemma S_outside_nat (r k d : ℕ) (h : r < d ∨ k < d) : S r k d = 0 := by
  letI := counted_outside_isEmpty r k d h
  let e : Counted r k d ≃ Empty := Equiv.equivOfIsEmpty _ _
  exact (Nat.card_congr e).trans (by simp)

lemma S_outside (r k d : ℕ) (h : r < d ∨ k < d) : (S r k d : ℤ) = 0 := by
  rw [S_outside_nat r k d h]
  rfl

end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma nonemptyRows_eq_card_subtype {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) :
    nonemptyRows R = Nat.card {i : Fin r // ∃ j : Fin k, R i j ≠ 0} := by
  letI : DecidablePred (fun i : Fin r => ∃ j : Fin k, R i j ≠ 0) := fun i => inferInstance
  rw [Nat.card_eq_fintype_card]
  simp [nonemptyRows, Fintype.card_subtype]

lemma first_empty_row_exists {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hd : nonemptyRows R = k) (hkr : k < r) :
    ∃ (j : Fin (k + 1)) (hj : j.val < r),
      (∀ c, R ⟨j.val, hj⟩ c = 0) ∧
        ∀ i : Fin r, i.val < j.val → ∃ c, R i c ≠ 0 := by
  classical
  have hb := emptyRows_balance R
  have hpos : 0 < (emptyRows R).card := by omega
  let s := emptyRows R
  have hne : s.Nonempty := card_pos.mp hpos
  let j := s.min' hne
  have hje : ∀ c, R j c = 0 := (mem_emptyRows R j).mp (s.min'_mem hne)
  have hbefore : ∀ i : Fin r, i < j → ∃ c, R i c ≠ 0 := by
    intro i hij
    by_contra h
    have hz : ∀ c, R i c = 0 := by simpa only [not_exists, not_not] using h
    have him : i ∈ s := (mem_emptyRows R i).mpr hz
    exact not_lt_of_ge (s.min'_le i him) hij
  let f : Fin j.val ↪ {i : Fin r // ∃ c, R i c ≠ 0} :=
    { toFun := fun i => ⟨⟨i.val, i.isLt.trans j.isLt⟩, hbefore _ i.isLt⟩
      inj' := by intro i₁ i₂ h; apply Fin.ext; exact congrArg (fun x => x.val.val) h }
  have hle : j.val ≤ nonemptyRows R := by
    rw [nonemptyRows_eq_card_subtype]
    have := Nat.card_le_card_of_injective f f.injective
    simpa using this
  have hbound : j.val < k + 1 := by omega
  refine ⟨⟨j.val,hbound⟩, j.isLt, ?_, ?_⟩
  · exact hje
  · exact hbefore

lemma topRows_nonemptyRows_of_before {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hp : p ≤ r) (hbefore : ∀ i : Fin r, i.val < p → ∃ c, R i c ≠ 0) :
    nonemptyRows (topRows R hp) = p := by
  unfold nonemptyRows
  have hn (i : Fin p) : ∃ c, topRows R hp i c ≠ 0 := hbefore _ i.isLt
  simp only [hn, filter_true, card_univ, Fintype.card_fin]

end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

private lemma balanced_below_empty_no_minus {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ i : Fin r) (hi : i₀ < i) (hempty : ∀ j, R i₀ j = 0) (j : Fin k) : R i j ≠ -1 := by
  intro hminus
  obtain ⟨l, hlj, hl⟩ := one_before_minus (R i) (hR.1 i).2.1 j hminus
  have hcol := balanced_column_sum R hR hd j
  have hecol := line_sum_one_ends_one (fun x => R x j) (hR.2 j).1 (hR.2 j).2 hcol
  obtain ⟨v, hiv, hv⟩ := one_after_minus_of_ends (fun x => R x j) hecol i hminus
  exact no12_below_empty R he i₀ i v l j hi hiv hlj hempty ⟨hl, hv⟩

private lemma balanced_below_empty_nonneg {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ i : Fin r) (hi : i₀ < i) (hempty : ∀ j, R i₀ j = 0) (j : Fin k) :
    0 ≤ (R i j : ℤ) := by
  have hn := balanced_below_empty_no_minus R hR he hd i₀ i hi hempty j
  cases hx : R i j <;> simp_all [SignType.cast]

private lemma balanced_below_empty_one_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ i : Fin r) (hi : i₀ < i) (hempty : ∀ j, R i₀ j = 0)
    (a b : Fin k) (ha : R i a = 1) (hb : R i b = 1) : a = b := by
  classical
  by_contra hne
  have hp : ∃ j, R i j ≠ 0 := ⟨a, by simp [ha]⟩
  have hsum : (∑ j, (R i j : ℤ)) = 1 := (asr_row_sum_one_iff R hR i).mpr hp
  have hle : (∑ j ∈ ({a,b} : Finset (Fin k)), (R i j : ℤ)) ≤ ∑ j, (R i j : ℤ) := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro j _ _
    exact balanced_below_empty_nonneg R hR he hd i₀ i hi hempty j
  rw [sum_pair hne, ha, hb, hsum] at hle
  norm_num at hle

private lemma balanced_below_empty_singleton {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ i : Fin r) (hi : i₀ < i) (hempty : ∀ j, R i₀ j = 0)
    (hp : ∃ j, R i j ≠ 0) :
    ∃ a : Fin k, ∀ j, R i j = if a = j then 1 else 0 := by
  classical
  have hsum : (∑ j, (R i j : ℤ)) = 1 := (asr_row_sum_one_iff R hR i).mpr hp
  have hex : ∃ a, R i a = 1 := by
    by_contra h
    push Not at h
    have hle : (∑ j, (R i j : ℤ)) ≤ 0 := by
      apply sum_nonpos
      intro j _
      have hn := h j
      cases hj : R i j <;> simp_all [SignType.cast]
    omega
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  intro j
  by_cases hj : a = j
  · simp [← hj, ha]
  · have hnotone : R i j ≠ 1 := by
      intro hone
      exact hj (balanced_below_empty_one_unique R hR he hd i₀ i hi hempty a j ha hone)
    have hnotminus := balanced_below_empty_no_minus R hR he hd i₀ i hi hempty j
    cases hv : R i j <;> simp_all

end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

private lemma topRows_col_sum_filter {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hp : p ≤ r) (j : Fin k) :
    colSum (topRows R hp) j = ∑ i ∈ univ.filter (fun i : Fin r => i.val < p), (R i j : ℤ) :=
  prefix_sum_as_filter hp (fun i => R i j)

private lemma topRows_col_sum_add_tail {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hp : p ≤ r) (j : Fin k) :
    colSum (topRows R hp) j +
      (∑ i ∈ univ.filter (fun i : Fin r => ¬ i.val < p), (R i j : ℤ)) = colSum R j := by
  rw [topRows_col_sum_filter]
  exact sum_filter_add_sum_filter_not (s := univ) (f := fun i : Fin r => (R i j : ℤ))
    (p := fun i => i.val < p)

private lemma balanced_tail_sum_le_one {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (hd : nonemptyRows R = k) (p : ℕ) (hp : p ≤ r) (j : Fin k) :
    (∑ i ∈ univ.filter (fun i : Fin r => ¬ i.val < p), (R i j : ℤ)) ≤ 1 := by
  have hsum := topRows_col_sum_add_tail R hp j
  have htop := asr_col_sum (topRows R hp) (topRows_isASR R hp hR) j
  rw [balanced_column_sum R hR hd j] at hsum
  rcases htop with h | h <;> omega

private lemma balanced_tail_one_iff_deficient {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) (j : Fin k) :
    (∃ i, i₀ < i ∧ R i j = 1) ↔
      colSum (topRows R (Nat.le_of_lt i₀.isLt)) j = 0 := by
  classical
  let hp : i₀.val ≤ r := Nat.le_of_lt i₀.isLt
  let t := univ.filter (fun i : Fin r => ¬ i.val < i₀.val)
  have hnonneg (i : Fin r) (hi : i ∈ t) : 0 ≤ (R i j : ℤ) := by
    have hge : i₀.val ≤ i.val := Nat.le_of_not_gt (mem_filter.mp hi).2
    by_cases hEq : i = i₀
    · simp [hEq, hempty]
    · have hlt : i₀ < i := lt_of_le_of_ne hge (fun h => hEq h.symm)
      exact balanced_below_empty_nonneg R hR he hd i₀ i hlt hempty j
  constructor
  · rintro ⟨i, hi, hone⟩
    have hit : i ∈ t := by
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      exact not_lt_of_ge (le_of_lt hi)
    have hle := single_le_sum (s := t) hnonneg hit
    rw [hone] at hle
    have hs := topRows_col_sum_add_tail R hp j
    rw [balanced_column_sum R hR hd j] at hs
    rcases asr_col_sum (topRows R hp) (topRows_isASR R hp hR) j with h | h
    · exact h
    · change (1 : ℤ) ≤ ∑ i ∈ t, (R i j : ℤ) at hle
      change colSum (topRows R hp) j + (∑ i ∈ t, (R i j : ℤ)) = 1 at hs
      omega
  · intro hz
    obtain ⟨i, hi, hone⟩ := one_after_zero_prefix hp (fun i => R i j)
      (balanced_column_sum R hR hd j) hz
    have hne : i₀ ≠ i := by
      intro h
      rw [← h, hempty] at hone
      exact (by decide : (0 : SignType) ≠ 1) hone
    exact ⟨i, lt_of_le_of_ne hi hne, hone⟩

private lemma balanced_tail_column_one_unique {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ a b : Fin r) (ha : i₀ < a) (hb : i₀ < b) (hempty : ∀ j, R i₀ j = 0)
    (j : Fin k) (haj : R a j = 1) (hbj : R b j = 1) : a = b := by
  classical
  by_contra hne
  let t := univ.filter (fun i : Fin r => ¬ i.val < i₀.val)
  have hat : a ∈ t := mem_filter.mpr ⟨mem_univ _, not_lt_of_ge (le_of_lt ha)⟩
  have hbt : b ∈ t := mem_filter.mpr ⟨mem_univ _, not_lt_of_ge (le_of_lt hb)⟩
  have hsub : ({a,b} : Finset (Fin r)) ⊆ t := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hnonneg (i : Fin r) (hi : i ∈ t) : 0 ≤ (R i j : ℤ) := by
    have hge : i₀.val ≤ i.val := Nat.le_of_not_gt (mem_filter.mp hi).2
    by_cases hEq : i = i₀
    · simp [hEq, hempty]
    · have hlt : i₀ < i := lt_of_le_of_ne hge (fun h => hEq h.symm)
      exact balanced_below_empty_nonneg R hR he hd i₀ i hlt hempty j
  have hle : (∑ i ∈ ({a,b} : Finset (Fin r)), (R i j : ℤ)) ≤ ∑ i ∈ t, (R i j : ℤ) := by
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro i hi _
    exact hnonneg i hi
  rw [sum_pair hne, haj, hbj] at hle
  have hbound := balanced_tail_sum_le_one R hR hd i₀.val (Nat.le_of_lt i₀.isLt) j
  change (∑ i ∈ t, (R i j : ℤ)) ≤ 1 at hbound
  norm_num at hle
  omega

private lemma balanced_tail_strict_decreasing {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ a b : Fin r) (ha : i₀ < a) (hab : a < b) (hempty : ∀ j, R i₀ j = 0)
    (j₁ j₂ : Fin k) (h₁ : R a j₁ = 1) (h₂ : R b j₂ = 1) : j₂ < j₁ := by
  rcases lt_trichotomy j₂ j₁ with h | h | h
  · exact h
  · have heq := balanced_tail_column_one_unique R hR he hd i₀ a b ha
      (lt_trans ha hab) hempty j₁ h₁ (by simpa only [h] using h₂)
    exact (ne_of_lt hab heq).elim
  · exact (no12_below_empty R he i₀ a b j₁ j₂ ha hab h hempty ⟨h₁,h₂⟩).elim

end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

def tailRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (i₀ : Fin r) : Finset (Fin r) := by
  classical
  exact univ.filter (fun i => i₀ < i ∧ ∃ j, R i j ≠ 0)

private lemma mem_tailRows {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (i₀ i : Fin r) :
    i ∈ tailRows R i₀ ↔ i₀ < i ∧ ∃ j, R i j ≠ 0 := by
  classical
  simp [tailRows]

def tailColumn {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) (i : tailRows R i₀) : Fin k :=
  Classical.choose (balanced_below_empty_singleton R hR he hd i₀ i.val
    ((mem_tailRows R i₀ i.val).mp i.property).1 hempty
    ((mem_tailRows R i₀ i.val).mp i.property).2)

lemma tailColumn_entries {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) (i : tailRows R i₀) (j : Fin k) :
    R i.val j = if tailColumn R hR he hd i₀ hempty i = j then 1 else 0 :=
  Classical.choose_spec (balanced_below_empty_singleton R hR he hd i₀ i.val
    ((mem_tailRows R i₀ i.val).mp i.property).1 hempty
    ((mem_tailRows R i₀ i.val).mp i.property).2) j

private lemma tailColumn_one {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) (i : tailRows R i₀) :
    R i.val (tailColumn R hR he hd i₀ hempty i) = 1 := by
  rw [tailColumn_entries R hR he hd i₀ hempty i]
  simp

private lemma tailColumn_deficient {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) (i : tailRows R i₀) :
    tailColumn R hR he hd i₀ hempty i ∈
      deficientColumns (topRows R (Nat.le_of_lt i₀.isLt)) := by
  apply (mem_deficientColumns _ _).mpr
  apply (balanced_tail_one_iff_deficient R hR he hd i₀ hempty _).mp
  exact ⟨i.val, ((mem_tailRows R i₀ i.val).mp i.property).1,
    tailColumn_one R hR he hd i₀ hempty i⟩

def balancedTailEquiv {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) :
    tailRows R i₀ ≃ deficientColumns (topRows R (Nat.le_of_lt i₀.isLt)) := by
  let f : tailRows R i₀ → deficientColumns (topRows R (Nat.le_of_lt i₀.isLt)) :=
    fun i => ⟨tailColumn R hR he hd i₀ hempty i, tailColumn_deficient R hR he hd i₀ hempty i⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply balanced_tail_column_one_unique R hR he hd i₀ a.val b.val
      ((mem_tailRows R i₀ a.val).mp a.property).1
      ((mem_tailRows R i₀ b.val).mp b.property).1 hempty (f a).val
    · exact tailColumn_one R hR he hd i₀ hempty a
    · have hb := tailColumn_one R hR he hd i₀ hempty b
      simpa only [show (f a).val = (f b).val from congrArg Subtype.val hab] using hb
  · intro j
    have hz := (mem_deficientColumns _ j.val).mp j.property
    obtain ⟨i, hi, hone⟩ := (balanced_tail_one_iff_deficient R hR he hd i₀ hempty j.val).mpr hz
    let a : tailRows R i₀ := ⟨i, (mem_tailRows R i₀ i).mpr ⟨hi, ⟨j.val, by simp [hone]⟩⟩⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply balanced_below_empty_one_unique R hR he hd i₀ i hi hempty
      (tailColumn R hR he hd i₀ hempty a) j.val
    · exact tailColumn_one R hR he hd i₀ hempty a
    · exact hone

private lemma balancedTail_card {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) :
    (tailRows R i₀).card = (deficientColumns (topRows R (Nat.le_of_lt i₀.isLt))).card := by
  have h := Nat.card_congr (balancedTailEquiv R hR he hd i₀ hempty)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h

lemma balancedTailEquiv_strictAnti {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0) :
    StrictAnti (fun i => (balancedTailEquiv R hR he hd i₀ hempty i).val) := by
  intro a b hab
  apply balanced_tail_strict_decreasing R hR he hd i₀ a.val b.val
    ((mem_tailRows R i₀ a.val).mp a.property).1 hab hempty
  · exact tailColumn_one R hR he hd i₀ hempty a
  · exact tailColumn_one R hR he hd i₀ hempty b

private lemma first_empty_tail_card {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ j, R i₀ j = 0)
    (hbefore : ∀ i : Fin r, i.val < i₀.val → ∃ c, R i c ≠ 0) :
    (tailRows R i₀).card = k - i₀.val := by
  rw [balancedTail_card R hR he hd i₀ hempty]
  have hn := topRows_nonemptyRows_of_before R (Nat.le_of_lt i₀.isLt) hbefore
  have hb := deficientColumns_balance (topRows R (Nat.le_of_lt i₀.isLt))
    (topRows_isASR R (Nat.le_of_lt i₀.isLt) hR)
  omega

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset

lemma strictAnti_equiv_sorted {α β : Type*} [LinearOrder α] [LinearOrder β]
    (s : Finset α) (t : Finset β) (e : s ≃ t)
    (he : StrictAnti (fun x : s => (e x).val))
    {n : ℕ} (hs : s.card = n) (ht : t.card = n) (x : Fin n) :
    e (s.orderIsoOfFin hs x) = t.orderIsoOfFin ht x.rev := by
  let f : Fin n → Fin n := fun y =>
    (t.orderIsoOfFin ht).symm (e (s.orderIsoOfFin hs y.rev))
  have hf : StrictMono f := by
    intro a b hab
    apply (t.orderIsoOfFin ht).symm.strictMono
    apply he
    apply (s.orderIsoOfFin hs).strictMono
    exact Fin.rev_lt_rev.mpr hab
  have h := hf.apply_eq (x := x.rev)
  change (t.orderIsoOfFin ht).symm (e (s.orderIsoOfFin hs x.rev.rev)) = x.rev at h
  rw [Fin.rev_rev] at h
  exact (t.orderIsoOfFin ht).symm_apply_eq.mp h

end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

def tailIndex {r p : ℕ} (hp : p < r) (a : Fin (r-p-1)) : Fin r :=
  Fin.cast (by omega : p+1+(r-p-1)=r) (Fin.natAdd (p+1) a)

def tailChoice {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (hp : p < r) : Finset (Fin (r-p-1)) := by
  classical
  exact univ.filter (fun a => ∃ c, R (tailIndex hp a) c ≠ 0)

lemma mem_tailChoice {r k p : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (hp : p < r)
    (a : Fin (r-p-1)) : a ∈ tailChoice R hp ↔ ∃ c, R (tailIndex hp a) c ≠ 0 := by
  classical
  simp [tailChoice]

def tailChoiceEquiv {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType) (i₀ : Fin r) :
    tailRows R i₀ ≃ tailChoice R i₀.isLt where
  toFun i :=
    ⟨⟨i.val.val-i₀.val-1,by
        have hi := ((mem_tailRows R i₀ i.val).mp i.property).1
        have hb := i.val.isLt
        change i₀.val < i.val.val at hi
        omega⟩,by
      apply (mem_tailChoice R i₀.isLt _).mpr
      have heq : tailIndex i₀.isLt ⟨i.val.val-i₀.val-1,by
          have hi := ((mem_tailRows R i₀ i.val).mp i.property).1
          have hb := i.val.isLt
          change i₀.val < i.val.val at hi
          omega⟩ = i.val := by
        apply Fin.ext
        dsimp [tailIndex]
        have hi := ((mem_tailRows R i₀ i.val).mp i.property).1
        change i₀.val < i.val.val at hi
        omega
      rw [heq]
      exact ((mem_tailRows R i₀ i.val).mp i.property).2⟩
  invFun a := ⟨tailIndex i₀.isLt a.val,by
    apply (mem_tailRows R i₀ _).mpr
    refine ⟨?_,(mem_tailChoice R i₀.isLt a.val).mp a.property⟩
    change i₀.val < i₀.val+1+a.val.val
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [tailIndex]
    have hi := ((mem_tailRows R i₀ i.val).mp i.property).1
    change i₀.val < i.val.val at hi
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [tailIndex]
    omega

lemma first_empty_choice_card {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hR : IsASR R) (he : ExtAvoids312 R) (hd : nonemptyRows R = k)
    (i₀ : Fin r) (hempty : ∀ c, R i₀ c = 0)
    (hbefore : ∀ i : Fin r, i.val < i₀.val → ∃ c, R i c ≠ 0) :
    (tailChoice R i₀.isLt).card = k-i₀.val := by
  have hc := Nat.card_congr (tailChoiceEquiv R i₀)
  have heq : (tailRows R i₀).card = (tailChoice R i₀.isLt).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc
  rw [← heq]
  exact first_empty_tail_card R hR he hd i₀ hempty hbefore

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section



def fillTail {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i : Fin t) (c : Fin k) : SignType :=
  if ∃ x, (A.orderEmbOfFin hA) x = i ∧ deficientColumnAt T x = c then 1 else 0

lemma fillTail_selected_row {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (x : Fin (deficientColumns T).card) :
    fillTail T A hA ((A.orderEmbOfFin hA) x) = fun c => if deficientColumnAt T x = c then 1 else 0 := by
  classical
  funext c
  have heq : (∃ y, (A.orderEmbOfFin hA) y = (A.orderEmbOfFin hA) x ∧ deficientColumnAt T y = c) ↔
      deficientColumnAt T x = c := by
    constructor
    · rintro ⟨y, hy, hc⟩
      have h := ((A.orderEmbOfFin hA)).injective hy
      simpa only [h] using hc
    · intro hc
      exact ⟨x, rfl, hc⟩
  simp only [fillTail, heq]

private lemma fillTail_deficient_col {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (x : Fin (deficientColumns T).card) :
    (fun i => fillTail T A hA i (deficientColumnAt T x)) =
      fun i => if (A.orderEmbOfFin hA) x = i then 1 else 0 := by
  classical
  funext i
  have heq : (∃ y, (A.orderEmbOfFin hA) y = i ∧ deficientColumnAt T y = deficientColumnAt T x) ↔
      (A.orderEmbOfFin hA) x = i := by
    constructor
    · rintro ⟨y, hy, hc⟩
      have h := deficientColumnAt_injective T hc
      simpa only [h] using hy
    · intro hi
      exact ⟨x, hi, rfl⟩
  simp only [fillTail, heq]

private lemma selectedRowAt_mem {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (x : Fin (deficientColumns T).card) :
    (A.orderEmbOfFin hA) x ∈ A := orderEmbOfFin_mem A hA x

lemma selectedRowAt_surjective {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i : Fin t) (hi : i ∈ A) :
    ∃ x, (A.orderEmbOfFin hA) x = i := by
  have h := congrArg (fun t : Set (Fin t) => i ∈ t) (Finset.range_orderEmbOfFin A hA)
  exact h.mpr hi

lemma fillTail_unselected_row {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i : Fin t) (hi : i ∉ A) :
    fillTail T A hA i = fun _ => 0 := by
  classical
  funext c
  have hno : ¬ ∃ x, (A.orderEmbOfFin hA) x = i ∧ deficientColumnAt T x = c := by
    rintro ⟨x, hx, _⟩
    exact hi (hx ▸ selectedRowAt_mem T A hA x)
  simp [fillTail, hno]

private lemma fillTail_complete_col {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (c : Fin k) (hc : colSum T c = 1) :
    (fun i => fillTail T A hA i c) = fun _ => 0 := by
  classical
  funext i
  have hno : ¬ ∃ x, (A.orderEmbOfFin hA) x = i ∧ deficientColumnAt T x = c := by
    rintro ⟨x, _, hx⟩
    have hz := deficientColumnAt_deficient T x
    rw [hx, hc] at hz
    omega
  simp [fillTail, hno]

def filledRect {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) : Matrix (Fin (j + (1 + t))) (Fin k) SignType :=
  Fin.append T (Fin.append (fun _ => 0) (fillTail T A hA))

@[simp] lemma filledRect_top {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i : Fin j) (c : Fin k) :
    filledRect T A hA (i.castAdd (1+t)) c = T i c := by
  exact congrFun (Fin.append_left T (Fin.append (fun _ : Fin 1 => 0) (fillTail T A hA)) i) c

@[simp] lemma filledRect_empty {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (c : Fin k) :
    filledRect T A hA (Fin.natAdd j (0 : Fin (1+t))) c = 0 := by
  have h0 : (0 : Fin (1+t)) = (0 : Fin 1).castAdd t := by apply Fin.ext; rfl
  unfold filledRect
  rw [Fin.append_right T (Fin.append (fun _ : Fin 1 => 0) (fillTail T A hA)), h0]
  exact congrFun (Fin.append_left (fun _ : Fin 1 => (0 : Fin k → SignType)) (fillTail T A hA) 0) c

@[simp] lemma filledRect_tail {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i : Fin t) (c : Fin k) :
    filledRect T A hA (Fin.natAdd j (Fin.natAdd 1 i)) c = fillTail T A hA i c := by
  exact congrFun ((Fin.append_right T (Fin.append (fun _ : Fin 1 => 0) (fillTail T A hA)) (Fin.natAdd 1 i)).trans
    (Fin.append_right (fun _ : Fin 1 => (0 : Fin k → SignType)) (fillTail T A hA) i)) c

private lemma fillTail_decreasing {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType) (A : Finset (Fin t))
    (hA : A.card = (deficientColumns T).card) (i₁ i₂ : Fin t) (c₁ c₂ : Fin k)
    (hi : i₁ < i₂) (h₁ : fillTail T A hA i₁ c₁ = 1) (h₂ : fillTail T A hA i₂ c₂ = 1) : c₂ < c₁ := by
  classical
  have hp₁ : ∃ x, (A.orderEmbOfFin hA) x = i₁ ∧ deficientColumnAt T x = c₁ := by
    simpa [fillTail] using h₁
  have hp₂ : ∃ x, (A.orderEmbOfFin hA) x = i₂ ∧ deficientColumnAt T x = c₂ := by
    simpa [fillTail] using h₂
  obtain ⟨x, hxi, rfl⟩ := hp₁
  obtain ⟨y, hyi, rfl⟩ := hp₂
  have hxy : x < y := ((A.orderEmbOfFin hA)).lt_iff_lt.mp (by simpa only [hxi,hyi] using hi)
  exact deficientColumnAt_antitone T x y hxy

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

private lemma zero_before_singleton {t : ℕ} (p : Fin t) :
    Fin.append (fun _ : Fin 1 => (0 : SignType)) (fun i => if p = i then 1 else 0) =
      fun y : Fin (1+t) => if Fin.natAdd 1 p = y then 1 else 0 := by
  funext y
  refine Fin.addCases (fun x => ?_) (fun x => ?_) y
  · have hn : Fin.natAdd 1 p ≠ x.castAdd t := by
      intro h
      have hv := congrArg Fin.val h
      have := x.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp [hn]
  · simp only [Fin.append_right,Fin.natAdd_inj]

private lemma filledRect_row_line {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card)
    (i : Fin (j+(1+t))) :
    Alternates (filledRect T A hA i) ∧ StartsOne (filledRect T A hA i) ∧
      EndsOne (filledRect T A hA i) := by
  classical
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have heq : filledRect T A hA (i.castAdd _) = T i := funext (filledRect_top T A hA i)
    rw [heq]
    exact hT.1 i
  · refine Fin.addCases (fun z => ?_) (fun i => ?_) i
    · have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
      subst z
      have heq : filledRect T A hA (Fin.natAdd j ((0 : Fin 1).castAdd t)) = fun _ => 0 := by
        funext c
        have h0 : (0 : Fin 1).castAdd t = (0 : Fin (1+t)) := by apply Fin.ext; rfl
        rw [h0]
        exact filledRect_empty T A hA c
      rw [heq]
      simp [Alternates,StartsOne,EndsOne]
    · have heq : filledRect T A hA (Fin.natAdd j (Fin.natAdd 1 i)) = fillTail T A hA i :=
        funext (filledRect_tail T A hA i)
      rw [heq]
      by_cases hi : i ∈ A
      · obtain ⟨x, rfl⟩ := selectedRowAt_surjective T A hA i hi
        rw [fillTail_selected_row]
        exact singleton_line _
      · rw [fillTail_unselected_row T A hA i hi]
        simp [Alternates,StartsOne,EndsOne]

private lemma filledRect_col_function {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) (c : Fin k) :
    (fun i => filledRect T A hA i c) =
      Fin.append (fun i => T i c) (Fin.append (fun _ : Fin 1 => 0) (fun i => fillTail T A hA i c)) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [filledRect_top,Fin.append_left]
  · refine Fin.addCases (fun z => ?_) (fun i => ?_) i
    · have hz : z = (0 : Fin 1) := Subsingleton.elim _ _
      subst z
      have h0 : (0 : Fin 1).castAdd t = (0 : Fin (1+t)) := by apply Fin.ext; rfl
      calc
        filledRect T A hA (Fin.natAdd j ((0 : Fin 1).castAdd t)) c = 0 := by
          rw [h0]
          exact filledRect_empty T A hA c
        _ = _ := by rw [Fin.append_right,Fin.append_left]
    · simp only [filledRect_tail,Fin.append_right]

private lemma filledRect_col_line {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) (c : Fin k) :
    Alternates (fun i => filledRect T A hA i c) ∧ StartsOne (fun i => filledRect T A hA i c) := by
  rw [filledRect_col_function]
  rcases asr_col_sum T hT c with hz | hone
  · obtain ⟨x, heq⟩ := deficientColumnAt_surjective T c hz
    rw [← heq,fillTail_deficient_col,zero_before_singleton]
    exact (append_one_line _ _ (hT.2 _).1 (hT.2 _).2
      (deficientColumnAt_deficient T x)).imp_right And.left
  · rw [fillTail_complete_col T A hA c hone]
    have heq : Fin.append (fun _ : Fin 1 => (0 : SignType)) (fun _ : Fin t => 0) = fun _ => 0 := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [heq]
    exact (pad_zero_line _ (hT.2 _).1 (hT.2 _).2
      (line_sum_one_ends_one _ (hT.2 _).1 (hT.2 _).2 hone)).imp_right And.left

lemma filledRect_isASR {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) :
    IsASR (filledRect T A hA) :=
  ⟨filledRect_row_line T hT A hA, filledRect_col_line T hT A hA⟩

private lemma filledRect_col_sum {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) (c : Fin k) :
    colSum (filledRect T A hA) c = 1 := by
  change (∑ i, ((fun i => filledRect T A hA i c) i : ℤ)) = 1
  rw [filledRect_col_function]
  rcases asr_col_sum T hT c with hz | hone
  · obtain ⟨x, heq⟩ := deficientColumnAt_surjective T c hz
    rw [← heq,fillTail_deficient_col,zero_before_singleton,sum_append_one]
    change colSum T (deficientColumnAt T x) + 1 = 1
    rw [deficientColumnAt_deficient]
    rfl
  · rw [fillTail_complete_col T A hA c hone]
    have heq : Fin.append (fun _ : Fin 1 => (0 : SignType)) (fun _ : Fin t => 0) = fun _ => 0 := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    rw [heq,sum_pad_zero]
    exact hone

lemma filledRect_nonemptyRows {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) :
    nonemptyRows (filledRect T A hA) = k := by
  have ht := asr_total_sum (filledRect T A hA) (filledRect_isASR T hT A hA)
  rw [sum_comm] at ht
  have hc : (∑ c, colSum (filledRect T A hA) c) = (k : ℤ) := by
    simp only [filledRect_col_sum T hT A hA,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  change (∑ c, colSum (filledRect T A hA) c) = _ at ht
  omega

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

namespace D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction
set_option autoImplicit false
open D5.S3.Combinatorics.AlternatingSignRectangles.CanonicalCompletion D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction D5.S3.Combinatorics.AlternatingSignRectangles.SignLines
open Finset
noncomputable section

lemma rowComplete_nonempty {r k : ℕ} (R : Matrix (Fin r) (Fin k) SignType)
    (hd : nonemptyRows R = r) (i : Fin r) : ∃ j, R i j ≠ 0 := by
  classical
  have hb := emptyRows_balance R
  have hz : (emptyRows R).card = 0 := by omega
  have hn : i ∉ emptyRows R := by rw [card_eq_zero.mp hz]; simp
  by_contra h
  apply hn
  apply (mem_emptyRows R i).mpr
  simpa only [not_exists,not_not] using h

private lemma filledRect_old {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card)
    (i : Fin (j+(1+t))) (hi : i.val < j) (c : Fin k) :
    filledRect T A hA i c = T ⟨i.val,hi⟩ c := by
  have hir : (⟨i.val,hi⟩ : Fin j).castAdd (1+t) = i := by apply Fin.ext; rfl
  simpa only [hir] using filledRect_top T A hA ⟨i.val,hi⟩ c

private lemma filledRect_one_tail {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card)
    (i : Fin (j+(1+t))) (hi : j ≤ i.val) (c : Fin k) (hone : filledRect T A hA i c = 1) :
    ∃ a : Fin t, i = Fin.natAdd j (Fin.natAdd 1 a) ∧ fillTail T A hA a c = 1 := by
  have hne : i.val ≠ j := by
    intro h
    have hir : i = Fin.natAdd j (0 : Fin (1+t)) := by apply Fin.ext; simpa using h
    rw [hir,filledRect_empty] at hone
    exact (by decide : (0 : SignType) ≠ 1) hone
  have hb : i.val-j-1 < t := by have := i.isLt; omega
  let a : Fin t := ⟨i.val-j-1,hb⟩
  have hir : i = Fin.natAdd j (Fin.natAdd 1 a) := by apply Fin.ext; simp [a]; omega
  refine ⟨a,hir,?_⟩
  simpa only [hir,filledRect_tail] using hone

private lemma filledRect_empty_not_top {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hTrows : nonemptyRows T = j) (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card)
    (i : Fin (j+(1+t))) (hempty : ∀ c, filledRect T A hA i c = 0) : j ≤ i.val := by
  by_contra h
  have hi : i.val < j := Nat.lt_of_not_ge h
  obtain ⟨c,hc⟩ := rowComplete_nonempty T hTrows ⟨i.val,hi⟩
  exact hc (by simpa only [filledRect_old T A hA i hi] using hempty c)

private lemma filledRect_safe {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (he : ExtAvoids312 T) (hTrows : nonemptyRows T = j)
    (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) :
    CompletionSafe (filledRect T A hA) := by
  classical
  constructor
  · rintro ⟨i₁,i₂,i₃,c₁,c₂,c₃,hi₁₂,hi₂₃,hc₁₂,hc₂₃,h₁,h₂,h₃⟩
    by_cases hi₂ : j ≤ i₂.val
    · have hi₃ : j ≤ i₃.val := by change i₂.val < i₃.val at hi₂₃; omega
      obtain ⟨a,hia,ha⟩ := filledRect_one_tail T A hA i₂ hi₂ c₁ h₂
      obtain ⟨b,hib,hb⟩ := filledRect_one_tail T A hA i₃ hi₃ c₂ h₃
      have hab : a < b := by
        rw [hia,hib] at hi₂₃
        change j+(1+a.val) < j+(1+b.val) at hi₂₃
        change a.val < b.val
        omega
      exact not_lt_of_ge (le_of_lt (fillTail_decreasing T A hA a b c₁ c₂ hab ha hb)) hc₁₂
    · have hi₂' : i₂.val < j := Nat.lt_of_not_ge hi₂
      have hi₁' : i₁.val < j := by change i₁.val < i₂.val at hi₁₂; omega
      have ht₁ : T ⟨i₁.val,hi₁'⟩ c₃ = 1 := by simpa only [filledRect_old T A hA i₁ hi₁'] using h₁
      have ht₂ : T ⟨i₂.val,hi₂'⟩ c₁ = 1 := by simpa only [filledRect_old T A hA i₂ hi₂'] using h₂
      by_cases hi₃ : j ≤ i₃.val
      · obtain ⟨a,_,ha⟩ := filledRect_one_tail T A hA i₃ hi₃ c₂ h₃
        have hex : ∃ x, (A.orderEmbOfFin hA) x = a ∧ deficientColumnAt T x = c₂ := by
          simpa [fillTail] using ha
        obtain ⟨x,_,hxc⟩ := hex
        have hz : colSum T c₂ = 0 := by rw [← hxc]; exact deficientColumnAt_deficient T x
        exact no312_with_deficient_last T he ⟨i₁.val,hi₁'⟩ ⟨i₂.val,hi₂'⟩ c₁ c₂ c₃
          hi₁₂ hc₁₂ hc₂₃ ht₁ ht₂ hz
      · have hi₃' : i₃.val < j := Nat.lt_of_not_ge hi₃
        have ht₃ : T ⟨i₃.val,hi₃'⟩ c₂ = 1 := by simpa only [filledRect_old T A hA i₃ hi₃'] using h₃
        exact extAvoids312_corner T he ⟨⟨i₁.val,hi₁'⟩,⟨i₂.val,hi₂'⟩,⟨i₃.val,hi₃'⟩,
          c₁,c₂,c₃,hi₁₂,hi₂₃,hc₁₂,hc₂₃,ht₁,ht₂,ht₃⟩
  · intro _ _ _ c₂ _ _ _ _ _ _ hz
    rw [filledRect_col_sum T hT A hA c₂] at hz
    omega
  · intro i₀ i₁ i₂ c₁ c₂ hi₀₁ hi₁₂ hc hempty hones
    have hi₀ := filledRect_empty_not_top T hTrows A hA i₀ hempty
    have hi₁ : j ≤ i₁.val := by change i₀.val < i₁.val at hi₀₁; omega
    have hi₂ : j ≤ i₂.val := by change i₁.val < i₂.val at hi₁₂; omega
    obtain ⟨a,hia,ha⟩ := filledRect_one_tail T A hA i₁ hi₁ c₁ hones.1
    obtain ⟨b,hib,hb⟩ := filledRect_one_tail T A hA i₂ hi₂ c₂ hones.2
    have hab : a < b := by
      rw [hia,hib] at hi₁₂
      change j+(1+a.val) < j+(1+b.val) at hi₁₂
      change a.val < b.val
      omega
    exact not_lt_of_ge (le_of_lt (fillTail_decreasing T A hA a b c₁ c₂ hab ha hb)) hc
  · intro _ _ _ c₂ _ _ _ _ hz
    rw [filledRect_col_sum T hT A hA c₂] at hz
    omega

lemma filledRect_extAvoids312 {j k t : ℕ} (T : Matrix (Fin j) (Fin k) SignType)
    (hT : IsASR T) (he : ExtAvoids312 T) (hTrows : nonemptyRows T = j)
    (A : Finset (Fin t)) (hA : A.card = (deficientColumns T).card) :
    ExtAvoids312 (filledRect T A hA) :=
  (extAvoids312_iff_safe _ (filledRect_isASR T hT A hA)).mpr (filledRect_safe T hT he hTrows A hA)

end
end D5.S3.Combinatorics.AlternatingSignRectangles.EmptyRowFillingConstruction

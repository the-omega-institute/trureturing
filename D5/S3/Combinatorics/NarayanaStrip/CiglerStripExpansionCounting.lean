/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionCounting
   mirror-E: none(waiver:colored-insertion-counting)
   anchors: [mathlib/module/Mathlib.Data.List.SplitLengths]
   utility: none
   digest: Binomial counting and inverse color allocation for skeleton insertions. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCancellation
import D5.S3.Combinatorics.ArrowWilfTwelveSurject
import Mathlib.Data.List.SplitLengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCounting

open CiglerStripExpansionSkeleton CiglerStripExpansionCancellation

def doubleGapLengths : List ℕ → ℕ → List ℕ
  | [], _ => []
  | [last], remainder => [2 * last + remainder]
  | first :: second :: rest, remainder =>
    2 * first :: 0 :: doubleGapLengths (second :: rest) remainder

def halveGaps : List (List Bool) → List ℕ
  | [] => []
  | [last] => [last.length / 2]
  | evenGap :: _ :: rest => evenGap.length / 2 :: halveGaps rest

theorem fixed_gap_bijection (pairs : ℕ) (colors : List Bool) :
    ∃ correspondence :
      {gaps : List (List Bool) // gaps.length = 2 * pairs + 1 ∧
        gaps.flatten = colors ∧ FixedGaps gaps} ≃
        (Finset.Nat.antidiagonalTuple (pairs + 1) (colors.length / 2)),
      (∀ gaps, List.ofFn (correspondence gaps).val = halveGaps gaps.val) ∧
      (∀ data, (correspondence.symm data).val =
        List.splitLengths (doubleGapLengths (List.ofFn data.val) (colors.length % 2)) colors) ∧
      (∀ domain : Finset (List (List Bool)),
        (∀ gaps, gaps ∈ domain ↔ gaps.length = 2 * pairs + 1 ∧ gaps.flatten = colors) →
          (∑ gaps ∈ domain, (-1 : ℤ) ^ gapCharge true gaps) =
            (((colors.length / 2 + pairs).choose pairs : ℕ) : ℤ)) := by
  classical
  have gap_composition_count (bars colors : ℕ) :
      (Finset.Nat.antidiagonalTuple (bars + 1) colors).card =
        (colors + bars).choose bars := by
    have transport : (Finset.Nat.antidiagonalTuple (bars + 1) colors).card =
        ((Finset.univ : Finset (Fin (bars + 1))).finsuppAntidiag colors).card := by
      apply Finset.card_bij (fun data _ => Finsupp.equivFunOnFinite.symm data)
      · intro data inside
        simp only [Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
        exact Finset.Nat.mem_antidiagonalTuple.mp inside
      · intro first _ second _ equal
        exact Finsupp.equivFunOnFinite.symm.injective equal
      · intro data inside
        refine ⟨Finsupp.equivFunOnFinite data, ?_, ?_⟩
        · exact Finset.Nat.mem_antidiagonalTuple.mpr
            (Finset.mem_finsuppAntidiag.mp inside).1
        · exact Finsupp.equivFunOnFinite.symm_apply_apply data
    rw [transport, Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    have top : bars + 1 + colors - 1 = colors + bars := by omega
    rw [top]
    exact Nat.choose_symm_add
  have doubled (sizes : List ℕ) (remainder : ℕ) (nonempty : sizes ≠ [])
      (small : remainder < 2) :
      (doubleGapLengths sizes remainder).length = 2 * sizes.length - 1 ∧
        (doubleGapLengths sizes remainder).sum = 2 * sizes.sum + remainder ∧
        (∀ gaps : List (List Bool),
          gaps.map List.length = doubleGapLengths sizes remainder →
            FixedGaps gaps ∧ halveGaps gaps = sizes) := by
    induction sizes generalizing remainder with
    | nil => exact False.elim (nonempty rfl)
    | cons first rest induction_hyp =>
      cases rest with
      | nil =>
        simp only [doubleGapLengths, List.length_singleton, List.sum_singleton]
        refine ⟨trivial, trivial, ?_⟩
        intro gaps lengths
        cases gaps with
        | nil => simp at lengths
        | cons gap gaps =>
          cases gaps with
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at lengths
            simp only [FixedGaps, halveGaps, List.cons.injEq, and_true, true_and]
            omega
          | cons gapNext gaps => simp at lengths
      | cons second rest =>
        have recurse := induction_hyp remainder (by simp) small
        simp only [doubleGapLengths, List.length_cons, List.sum_cons]
        refine ⟨by simp only [List.length_cons] at recurse; omega,
          by rw [recurse.2.1]; simp only [List.sum_cons]; omega, ?_⟩
        intro gaps lengths
        cases gaps with
        | nil => simp at lengths
        | cons gap gaps =>
          cases gaps with
          | nil => simp at lengths
          | cons gapOdd gaps =>
            simp only [List.map_cons, List.cons.injEq] at lengths
            have odd_empty : gapOdd = [] := by simpa using lengths.2.1
            subst gapOdd
            have rest_props := recurse.2.2 gaps lengths.2.2
            simp only [FixedGaps, halveGaps, rest_props.1, rest_props.2,
              lengths.1, Nat.mul_mod_right, List.cons.injEq]
            simp
  have halved (pairs : ℕ) (gaps : List (List Bool))
      (length : gaps.length = 2 * pairs + 1) (fixed : FixedGaps gaps) :
      (halveGaps gaps).length = pairs + 1 ∧
        (halveGaps gaps).sum = gaps.flatten.length / 2 ∧
        doubleGapLengths (halveGaps gaps) (gaps.flatten.length % 2) =
          gaps.map List.length := by
    induction pairs generalizing gaps with
    | zero =>
      cases gaps with
      | nil => simp at length
      | cons gap gaps =>
        cases gaps with
        | cons next rest => simp at length
        | nil =>
          simp only [halveGaps, doubleGapLengths, List.length_singleton,
            List.sum_singleton, List.flatten_cons, List.flatten_nil,
            List.append_nil, List.map_cons, List.map_nil]
          refine ⟨trivial, trivial, ?_⟩
          congr 1
          omega
    | succ pairs induction_hyp =>
      cases gaps with
      | nil => simp at length
      | cons gap gaps =>
        cases gaps with
        | nil => simp at length
        | cons gapOdd gaps =>
          have rest_length : gaps.length = 2 * pairs + 1 := by
            simp only [List.length_cons] at length
            omega
          rcases fixed with ⟨even, empty, fixed⟩
          subst gapOdd
          have recurse := induction_hyp gaps rest_length fixed
          have nonempty : halveGaps gaps ≠ [] := by
            intro empty
            rw [empty] at recurse
            simp at recurse
          have parity : (gap.length + gaps.flatten.length) % 2 =
              gaps.flatten.length % 2 := by omega
          refine ⟨?_, ?_, ?_⟩
          · simp only [halveGaps, List.length_cons, recurse.1]
          · simp only [halveGaps, List.sum_cons, recurse.2.1,
              List.flatten_cons, List.nil_append, List.length_append]
            omega
          · cases halve_eq : halveGaps gaps with
            | nil => exact False.elim (nonempty halve_eq)
            | cons next rest =>
              simp only [halveGaps, halve_eq, doubleGapLengths, List.flatten_cons,
                List.nil_append, List.length_append, parity]
              rw [← halve_eq, recurse.2.2]
              simp only [List.map_cons, List.length_nil]
              congr 2
              omega
  have of_list (word : List ℕ) (length : ℕ) (agrees : word.length = length) :
      List.ofFn (fun index : Fin length => word.get (Fin.cast agrees.symm index)) =
        word := by
    rw [← List.ofFn_congr agrees word.get, List.ofFn_get]
  let encode (gaps : {gaps : List (List Bool) // gaps.length = 2 * pairs + 1 ∧
      gaps.flatten = colors ∧ FixedGaps gaps}) :
      Finset.Nat.antidiagonalTuple (pairs + 1) (colors.length / 2) :=
    ⟨fun index => (halveGaps gaps.val).get
      (Fin.cast (halved pairs gaps.val gaps.property.1 gaps.property.2.2).1.symm index), by
      rw [Finset.Nat.mem_antidiagonalTuple, ← List.sum_ofFn,
        of_list _ _ (halved pairs gaps.val gaps.property.1 gaps.property.2.2).1]
      rw [(halved pairs gaps.val gaps.property.1 gaps.property.2.2).2.1,
        gaps.property.2.1]⟩
  have encoded (gaps : {gaps : List (List Bool) // gaps.length = 2 * pairs + 1 ∧
      gaps.flatten = colors ∧ FixedGaps gaps}) :
      List.ofFn (encode gaps).val = halveGaps gaps.val := by
    exact of_list _ _ (halved pairs gaps.val gaps.property.1 gaps.property.2.2).1
  let decode (data :
      Finset.Nat.antidiagonalTuple (pairs + 1) (colors.length / 2)) :
      {gaps : List (List Bool) // gaps.length = 2 * pairs + 1 ∧
        gaps.flatten = colors ∧ FixedGaps gaps} :=
    ⟨List.splitLengths (doubleGapLengths (List.ofFn data.val) (colors.length % 2)) colors, by
      have shape := doubled (List.ofFn data.val) (colors.length % 2)
        (by intro empty; have length := congrArg List.length empty; simp at length)
        (Nat.mod_lt _ (by omega))
      have total : (doubleGapLengths (List.ofFn data.val) (colors.length % 2)).sum =
          colors.length := by
        rw [shape.2.1, List.sum_ofFn, Finset.Nat.mem_antidiagonalTuple.mp data.property]
        omega
      have allocated := And.intro (List.map_splitLengths_length _ _ total.le)
        (List.flatten_splitLengths _ _ total.ge)
      refine ⟨?_, allocated.2, (shape.2.2 _ allocated.1).1⟩
      have lengths := congrArg List.length allocated.1
      rw [List.length_map, shape.1, List.length_ofFn] at lengths
      omega⟩
  have decode_encode (gaps : {gaps : List (List Bool) // gaps.length = 2 * pairs + 1 ∧
      gaps.flatten = colors ∧ FixedGaps gaps}) : decode (encode gaps) = gaps := by
    apply Subtype.ext
    change List.splitLengths (doubleGapLengths (List.ofFn (encode gaps).val)
      (colors.length % 2)) colors = gaps.val
    have sizes_eq := (halved pairs gaps.val gaps.property.1 gaps.property.2.2).2.2
    simp only [gaps.property.2.1] at sizes_eq
    rw [encoded, sizes_eq]
    simpa only [gaps.property.2.1] using
      ArrowWilfTwelveSurject.splitLengths_map_length_flatten gaps.val
  have encode_decode (data :
      Finset.Nat.antidiagonalTuple (pairs + 1) (colors.length / 2)) :
      encode (decode data) = data := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [encoded]
    have shape := doubled (List.ofFn data.val) (colors.length % 2)
      (by intro empty; have length := congrArg List.length empty; simp at length)
      (Nat.mod_lt _ (by omega))
    have total : (doubleGapLengths (List.ofFn data.val) (colors.length % 2)).sum =
        colors.length := by
      rw [shape.2.1, List.sum_ofFn, Finset.Nat.mem_antidiagonalTuple.mp data.property]
      omega
    exact (shape.2.2 _ (List.map_splitLengths_length _ _ total.le)).2
  let correspondence := Equiv.mk encode decode decode_encode encode_decode
  refine ⟨correspondence, encoded, fun _ => rfl, ?_⟩
  intro domain complete
  have fixed_count : (domain.filter FixedGaps).card =
      (Finset.Nat.antidiagonalTuple (pairs + 1) (colors.length / 2)).card := by
    let to_tuple (gaps : List (List Bool)) (inside : gaps ∈ domain.filter FixedGaps) :=
      correspondence ⟨gaps, (complete gaps).mp (Finset.mem_filter.mp inside).1 |>.1,
        (complete gaps).mp (Finset.mem_filter.mp inside).1 |>.2,
        (Finset.mem_filter.mp inside).2⟩
    apply Finset.card_bij (fun gaps inside => (to_tuple gaps inside).val)
    · intro gaps inside
      exact (to_tuple gaps inside).property
    · intro first first_mem second second_mem same
      have eq_tuple : to_tuple first first_mem = to_tuple second second_mem :=
        Subtype.ext same
      have eq_gaps := correspondence.injective eq_tuple
      exact congrArg Subtype.val eq_gaps
    · intro tuple inside
      let gaps := correspondence.symm ⟨tuple, inside⟩
      have membership : gaps.val ∈ domain.filter FixedGaps := by
        rw [Finset.mem_filter, complete]
        exact ⟨⟨gaps.property.1, gaps.property.2.1⟩, gaps.property.2.2⟩
      refine ⟨gaps.val, membership, ?_⟩
      have recovered : to_tuple gaps.val membership = ⟨tuple, inside⟩ := by
        change correspondence _ = _
        convert correspondence.apply_symm_apply ⟨tuple, inside⟩
      exact congrArg Subtype.val recovered
  have gap_props := colored_gap_involution.1
  have fixed_sum : (∑ gaps ∈ domain.filter FixedGaps,
      (-1 : ℤ) ^ gapCharge true gaps) = ((domain.filter FixedGaps).card : ℤ) := by
    calc
      _ = ∑ _gaps ∈ domain.filter FixedGaps, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro gaps inside
        rw [(gap_props gaps).2.2.2.2.1 (Finset.mem_filter.mp inside).2]
        rfl
      _ = _ := by simp
  have nonfixed_sum : (∑ gaps ∈ domain.filter (fun gaps => ¬FixedGaps gaps),
      (-1 : ℤ) ^ gapCharge true gaps) = 0 := by
    apply Finset.sum_involution (fun gaps _ => gapInvolution gaps)
    · intro gaps inside
      have not_fixed : gapInvolution gaps ≠ gaps := by
        exact fun same => (Finset.mem_filter.mp inside).2
          ((gap_props gaps).2.2.2.1.mp same)
      rw [(gap_props gaps).2.2.2.2.2 not_fixed]
      exact add_neg_cancel _
    · intro gaps inside _
      exact fun same => (Finset.mem_filter.mp inside).2
        ((gap_props gaps).2.2.2.1.mp same)
    · intro gaps inside
      rw [Finset.mem_filter, complete]
      have shape := (complete gaps).mp (Finset.mem_filter.mp inside).1
      refine ⟨?_, ?_⟩
      · rw [(gap_props gaps).1, (gap_props gaps).2.1]
        exact shape
      · intro fixed
        have image_fixed := (gap_props (gapInvolution gaps)).2.2.2.1.mpr fixed
        rw [(gap_props gaps).2.2.1] at image_fixed
        exact (Finset.mem_filter.mp inside).2
          ((gap_props gaps).2.2.2.1.mp image_fixed.symm)
    · intro gaps inside
      exact (gap_props gaps).2.2.1
  have partition := Finset.sum_filter_add_sum_filter_not domain FixedGaps
    (fun gaps => (-1 : ℤ) ^ gapCharge true gaps)
  rw [fixed_sum, nonfixed_sum, add_zero, fixed_count, gap_composition_count] at partition
  exact partition.symm

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionCounting

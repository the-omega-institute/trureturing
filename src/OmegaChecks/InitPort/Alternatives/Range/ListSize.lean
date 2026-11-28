module
public import OmegaChecks.InitPort.Alternatives.Range.LoopEndpoints
public import Init.Data.Range.Polymorphic.Lemmas
import all Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Loop
import all Init.Data.Array.Lemmas
import all Init.Data.Array.Basic
import all Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.NatLemmas
public import Init.Data.Range.Polymorphic.IntLemmas

/-! Range list lengths, indexing and emptiness. -/

open Std Std.PRange

namespace OmegaChecks.InitPort.Alternatives

public theorem Std.Rco.getElem?_toList_eq : type_of% @_root_.Std.Rco.getElem?_toList_eq := by
  intro α _ _ _ _ _ _ r i
  induction i generalizing r with
  | zero =>
    rw [_root_.Std.Rco.toList_eq_ite_roo, UpwardEnumerable.succMany?_zero]
    by_cases h : r.lower < r.upper
    · rw [ite_eq_left h]
      rw [Option.filter_some, ite_eq_left (decide_eq_true h)]
      rfl
    · rw [ite_eq_right h]
      rw [Option.filter_some, ite_eq_right (fun ht => h (of_decide_eq_true ht))]
      rfl
  | succ i ih =>
    rw [_root_.Std.Rco.toList_eq_ite_roo]
    by_cases h : r.lower < r.upper
    · rw [ite_eq_left h, List.getElem?_cons_succ, _root_.Std.Roo.toList_eq_match_rco,
        UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
      cases hn : UpwardEnumerable.succ? r.lower with
      | none => rfl
      | some next => exact ih (r := ⟨next, r.upper⟩)
    · rw [ite_eq_right h]
      cases hs : UpwardEnumerable.succMany? (i + 1) r.lower with
      | none => rfl
      | some next =>
        have cannot : ¬ next < r.upper := fun hh => h (UpwardEnumerable.lt_iff.mpr
          (UpwardEnumerable.lt_trans ⟨i, hs⟩ (UpwardEnumerable.lt_iff.mp hh)))
        rw [Option.filter_some, ite_eq_right (fun ht => cannot (of_decide_eq_true ht))]
        rfl

public theorem Std.Rco.length_toList : type_of% @_root_.Std.Rco.length_toList := by
  intro α r _ _ _ _ _ _ _ _
  obtain ⟨lo, hi⟩ := r
  generalize hn : Rxo.HasSize.size lo hi = n
  induction n generalizing lo with
  | zero =>
    have hout := _root_.Std.Rxo.size_eq_zero_iff_not_le.mp hn
    rw [_root_.Std.Rco.toList_eq_ite_roo, ite_eq_right hout]
    exact hn.symm
  | succ n ih =>
    have hin : lo < hi := Decidable.byContradiction fun hc =>
      Nat.noConfusion ((_root_.Std.Rxo.size_eq_zero_iff_not_le.mpr hc).symm.trans hn)
    rw [_root_.Std.Rco.toList_eq_ite_roo, ite_eq_left hin, List.length_cons, _root_.Std.Roo.toList_eq_match_rco]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact (Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none lo hi hin hs).symm
    | some next =>
      have eq := Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo hi next hin hs
      exact (congrArg Nat.succ (ih next (Nat.succ.inj (eq.symm.trans hn)))).trans eq.symm

public theorem Std.Rcc.getElem?_toList_eq : type_of% @_root_.Std.Rcc.getElem?_toList_eq := by
  intro α _ _ _ _ _ _ r i
  induction i generalizing r with
  | zero =>
    rw [_root_.Std.Rcc.toList_eq_ite_roc, UpwardEnumerable.succMany?_zero]
    by_cases h : r.lower ≤ r.upper
    · rw [ite_eq_left h]
      rw [Option.filter_some, ite_eq_left (decide_eq_true h)]
      rfl
    · rw [ite_eq_right h]
      rw [Option.filter_some, ite_eq_right (fun ht => h (of_decide_eq_true ht))]
      rfl
  | succ i ih =>
    rw [_root_.Std.Rcc.toList_eq_ite_roc]
    by_cases h : r.lower ≤ r.upper
    · rw [ite_eq_left h, List.getElem?_cons_succ, _root_.Std.Roc.toList_eq_match_rcc,
        UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
      cases hn : UpwardEnumerable.succ? r.lower with
      | none => rfl
      | some next => exact ih (r := ⟨next, r.upper⟩)
    · rw [ite_eq_right h]
      cases hs : UpwardEnumerable.succMany? (i + 1) r.lower with
      | none => rfl
      | some next =>
        have cannot : ¬ next ≤ r.upper := fun hh => h (UpwardEnumerable.le_iff.mpr
          (UpwardEnumerable.le_trans ⟨i + 1, hs⟩ (UpwardEnumerable.le_iff.mp hh)))
        rw [Option.filter_some, ite_eq_right (fun ht => cannot (of_decide_eq_true ht))]
        rfl

public theorem Std.Rcc.length_toList : type_of% @_root_.Std.Rcc.length_toList := by
  intro α r _ _ _ _ _ _ _ _
  obtain ⟨lo, hi⟩ := r
  generalize hn : Rxc.HasSize.size lo hi = n
  induction n generalizing lo with
  | zero =>
    have hout := _root_.Std.Rxc.size_eq_zero_iff_not_le.mp hn
    rw [_root_.Std.Rcc.toList_eq_ite_roc, ite_eq_right hout]
    exact hn.symm
  | succ n ih =>
    have hin : lo ≤ hi := Decidable.byContradiction fun hc =>
      Nat.noConfusion ((_root_.Std.Rxc.size_eq_zero_iff_not_le.mpr hc).symm.trans hn)
    rw [_root_.Std.Rcc.toList_eq_ite_roc, ite_eq_left hin, List.length_cons, _root_.Std.Roc.toList_eq_match_rcc]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact (Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none lo hi hin hs).symm
    | some next =>
      have eq := Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some lo hi next hin hs
      exact (congrArg Nat.succ (ih next (Nat.succ.inj (eq.symm.trans hn)))).trans eq.symm

public theorem Std.Rcc.toList_eq_toList_rco : type_of% @_root_.Std.Rcc.toList_eq_toList_rco := by
  intro α r _ _ _ _ _ _ _ _ _ _ _ _
  apply List.ext_getElem?
  intro i
  rw [_root_.Std.Rcc.getElem?_toList_eq, _root_.Std.Rco.getElem?_toList_eq]
  cases hs : UpwardEnumerable.succMany? i r.lower with
  | none => rfl
  | some a =>
    have hrel : a < UpwardEnumerable.succ r.upper ↔ a ≤ r.upper :=
      UpwardEnumerable.lt_iff.trans (UpwardEnumerable.lt_succ_iff.trans UpwardEnumerable.le_iff.symm)
    rw [Option.filter_some, Option.filter_some]
    by_cases ha : a ≤ r.upper
    · rw [ite_eq_left (decide_eq_true ha), ite_eq_left (decide_eq_true (hrel.mpr ha))]
    · rw [ite_eq_right (fun h => ha (of_decide_eq_true h)),
        ite_eq_right (fun h => ha (hrel.mp (of_decide_eq_true h)))]

public theorem Std.Roc.toList_eq_toList_roo : type_of% @_root_.Std.Roc.toList_eq_toList_roo := by
  intro α r _ _ _ _ _ _ _ _ _ _ _ _
  rw [_root_.Std.Roc.toList_eq_match_rcc, _root_.Std.Roo.toList_eq_match_rco]
  cases hs : UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rcc.toList_eq_toList_rco (r := ⟨next, r.upper⟩)

public theorem Nat.toList_ric_eq_toList_rcc : type_of% @_root_.Nat.toList_ric_eq_toList_rcc := by
  intro n
  rw [_root_.Std.Ric.toList_eq_match_rcc]
  rfl

public theorem Nat.toList_ric_eq_toList_rio : type_of% @_root_.Nat.toList_ric_eq_toList_rio := by
  intro n
  rw [_root_.Nat.toList_ric_eq_toList_rcc, _root_.Nat.toList_rio_eq_toList_rco]
  exact _root_.Nat.toList_rcc_eq_toList_rco

public theorem Nat.toList_rco_succ_succ : type_of% @_root_.Nat.toList_rco_succ_succ := by
  intro m n
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Nat.getElem?_toList_rco, _root_.Nat.getElem?_toList_rco]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Nat.toList_rcc_eq_cons_iff : type_of% @_root_.Nat.toList_rcc_eq_cons_iff := by
  intros
  rw [_root_.Nat.toList_rcc_eq_toList_rco, _root_.Nat.toList_rcc_eq_toList_rco,
    _root_.Nat.toList_rco_eq_cons_iff]
  constructor
  · rintro ⟨ha, hlt, ht⟩
    exact ⟨ha, by omega, ht⟩
  · rintro ⟨ha, hle, ht⟩
    exact ⟨ha, by omega, ht⟩

public theorem Int.toList_rco_succ_succ : type_of% @_root_.Int.toList_rco_succ_succ := by
  intro m n
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Int.getElem?_toList_rco, _root_.Int.getElem?_toList_rco]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Int.toList_rcc_eq_cons_iff : type_of% @_root_.Int.toList_rcc_eq_cons_iff := by
  intros
  rw [_root_.Int.toList_rcc_eq_toList_rco, _root_.Int.toList_rcc_eq_toList_rco,
    _root_.Int.toList_rco_eq_cons_iff]
  constructor
  · rintro ⟨ha, hlt, ht⟩
    exact ⟨ha, by omega, ht⟩
  · rintro ⟨ha, hle, ht⟩
    exact ⟨ha, by omega, ht⟩

public theorem Std.Rco.toArray_eq_ite_roo : type_of% @_root_.Std.Rco.toArray_eq_ite_roo := by
  intro α r _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Rco.toList_toArray, _root_.Std.Rco.toList_eq_ite_roo]
  by_cases h : r.lower < r.upper
  · rw [ite_eq_left h, ite_eq_left h, Array.toList_append, _root_.Std.Roo.toList_toArray]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]

public theorem Std.Roo.toArray_eq_match_rco : type_of% @_root_.Std.Roo.toArray_eq_match_rco := by
  intro α r _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Roo.toList_toArray, _root_.Std.Roo.toList_eq_match_rco]
  cases h : UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rco.toList_toArray.symm

public theorem Std.Rio.toArray_eq_match_rco : type_of% @_root_.Std.Rio.toArray_eq_match_rco := by
  intro α r _ _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Rio.toList_toArray, _root_.Std.Rio.toList_eq_match_rco]
  cases h : Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rco.toList_toArray.symm

public theorem Std.Rcc.toArray_eq_ite_roc : type_of% @_root_.Std.Rcc.toArray_eq_ite_roc := by
  intro α r _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Rcc.toList_toArray, _root_.Std.Rcc.toList_eq_ite_roc]
  by_cases h : r.lower ≤ r.upper
  · rw [ite_eq_left h, ite_eq_left h, Array.toList_append, _root_.Std.Roc.toList_toArray]
    rfl
  · rw [ite_eq_right h, ite_eq_right h]

public theorem Std.Roc.toArray_eq_match_rcc : type_of% @_root_.Std.Roc.toArray_eq_match_rcc := by
  intro α r _ _ _ _ _ _
  apply Array.toList_inj.mp
  rw [_root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_eq_match_rcc]
  cases h : UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rcc.toList_toArray.symm

public theorem Int.getElem!_toList_rco_ne_zero_iff : type_of% @_root_.Int.getElem!_toList_rco_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toList_rco]
  split <;> omega

public theorem Int.getElem!_toArray_rco_ne_zero_iff : type_of% @_root_.Int.getElem!_toArray_rco_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toArray_rco]
  split <;> omega

public theorem Int.getElem!_toArray_rcc_ne_zero_iff : type_of% @_root_.Int.getElem!_toArray_rcc_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toArray_rcc]
  split <;> omega

public theorem Int.getElem!_toArray_roo_ne_zero_iff : type_of% @_root_.Int.getElem!_toArray_roo_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toArray_roo]
  split <;> omega

public theorem Int.getElem!_toList_rcc_ne_zero_iff : type_of% @_root_.Int.getElem!_toList_rcc_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toList_rcc]
  split <;> omega

public theorem Int.getElem!_toList_roc_ne_zero_iff : type_of% @_root_.Int.getElem!_toList_roc_ne_zero_iff := by
  intros
  rw [_root_.Int.getElem!_toList_roc]
  split <;> omega

private theorem conditionalNoneIff {p q : Prop} [Decidable p] {value : α}
    (excluded : p → q → False) (outside : ¬p → q) :
    (if p then some value else none) = none ↔ q := by
  split <;> rename_i h
  · exact ⟨(fun e => nomatch e), fun hq => False.elim (excluded h hq)⟩
  · exact ⟨fun _ => outside h, fun _ => rfl⟩

public theorem Int.getElem?_toArray_roc_eq_none_iff : type_of% @_root_.Int.getElem?_toArray_roc_eq_none_iff := by
  intros
  rw [_root_.Int.getElem?_toArray_roc]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Int.getElem?_toArray_roo_eq_none_iff : type_of% @_root_.Int.getElem?_toArray_roo_eq_none_iff := by
  intros
  rw [_root_.Int.getElem?_toArray_roo]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Int.getElem?_toList_roc_eq_none_iff : type_of% @_root_.Int.getElem?_toList_roc_eq_none_iff := by
  intros
  rw [_root_.Int.getElem?_toList_roc]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Int.getElem?_toList_roo_eq_none_iff : type_of% @_root_.Int.getElem?_toList_roo_eq_none_iff := by
  intros
  rw [_root_.Int.getElem?_toList_roo]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Int.toList_rcc_succ_succ : type_of% @_root_.Int.toList_rcc_succ_succ := by
  intros
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Int.getElem?_toList_rcc, _root_.Int.getElem?_toList_rcc]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Int.zero_lt_getElem!_toArray_roc_iff : type_of% @_root_.Int.zero_lt_getElem!_toArray_roc_iff := by
  intros
  rw [_root_.Int.getElem!_toArray_roc]
  split <;> omega

public theorem Int.zero_ne_getElem!_toList_roo_iff : type_of% @_root_.Int.zero_ne_getElem!_toList_roo_iff := by
  intros
  rw [_root_.Int.getElem!_toList_roo]
  split <;> omega

public theorem Nat.getElem?_toArray_ric_eq_none_iff : type_of% @_root_.Nat.getElem?_toArray_ric_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toArray_ric]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toArray_rio_eq_none_iff : type_of% @_root_.Nat.getElem?_toArray_rio_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toArray_rio]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toArray_roc_eq_none_iff : type_of% @_root_.Nat.getElem?_toArray_roc_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toArray_roc]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toArray_roo_eq_none_iff : type_of% @_root_.Nat.getElem?_toArray_roo_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toArray_roo]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toList_ric_eq_none_iff : type_of% @_root_.Nat.getElem?_toList_ric_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toList_ric]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toList_rio_eq_none_iff : type_of% @_root_.Nat.getElem?_toList_rio_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toList_rio]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toList_roc_eq_none_iff : type_of% @_root_.Nat.getElem?_toList_roc_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toList_roc]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.getElem?_toList_roo_eq_none_iff : type_of% @_root_.Nat.getElem?_toList_roo_eq_none_iff := by
  intros
  rw [_root_.Nat.getElem?_toList_roo]
  exact conditionalNoneIff (by omega) (by omega)

public theorem Nat.map_add_toList_rco : type_of% @_root_.Nat.map_add_toList_rco := by
  intros
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Nat.getElem?_toList_rco, _root_.Nat.getElem?_toList_rco]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Nat.map_add_toList_rco' : type_of% @_root_.Nat.map_add_toList_rco' := by
  intros
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Nat.getElem?_toList_rco, _root_.Nat.getElem?_toList_rco]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Nat.toList_rcc_succ_succ : type_of% @_root_.Nat.toList_rcc_succ_succ := by
  intros
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Nat.getElem?_toList_rcc, _root_.Nat.getElem?_toList_rcc]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Nat.toList_rco_add_right_eq_map : type_of% @_root_.Nat.toList_rco_add_right_eq_map := by
  intros
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map, _root_.Nat.getElem?_toList_rco, _root_.Nat.getElem?_toList_rco]
  split <;> split <;> first | rfl | (exfalso; omega) | (apply congrArg some; dsimp only; omega)

public theorem Nat.toArray_rco_succ_succ : type_of% @_root_.Nat.toArray_rco_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Rco.toList_toArray, _root_.Std.Rco.toList_toArray]
  exact _root_.Nat.toList_rco_succ_succ

public theorem Nat.toArray_rco_succ_right_eq_append_map : type_of% @_root_.Nat.toArray_rco_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Rco.toList_toArray, _root_.Std.Rco.toList_toArray]
  exact _root_.Nat.toList_rco_succ_right_eq_cons_map h

public theorem Nat.toArray_roo_succ_succ : type_of% @_root_.Nat.toArray_roo_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Roo.toList_toArray, _root_.Std.Roo.toList_toArray]
  exact _root_.Nat.toList_roo_succ_succ

public theorem Nat.toArray_roo_succ_right_eq_append_map : type_of% @_root_.Nat.toArray_roo_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Roo.toList_toArray, _root_.Std.Roo.toList_toArray]
  exact _root_.Nat.toList_roo_succ_right_eq_cons_map h

public theorem Nat.toArray_roc_succ_succ : type_of% @_root_.Nat.toArray_roc_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_toArray]
  exact _root_.Nat.toList_roc_succ_succ

public theorem Nat.toArray_roc_succ_right_eq_append_map : type_of% @_root_.Nat.toArray_roc_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_toArray]
  exact _root_.Nat.toList_roc_succ_right_eq_cons_map h

public theorem Nat.toList_roc_succ_succ : type_of% @_root_.Nat.toList_roc_succ_succ := by
  intro m n
  rw [_root_.Nat.toList_roc_eq_toList_rco, _root_.Nat.toList_roc_eq_toList_rco]
  exact _root_.Nat.toList_rco_succ_succ

public theorem Nat.toArray_rcc_eq_singleton_append_iff : type_of% @_root_.Nat.toArray_rcc_eq_singleton_append_iff := by
  intro xs m n a
  have convert := @_root_.Nat.toList_rcc_eq_cons_iff xs.toList m n a
  constructor
  · intro h
    have hh := congrArg Array.toList h
    rw [_root_.Std.Rcc.toList_toArray, Array.toList_append] at hh
    obtain ⟨ha, hb, ht⟩ := convert.mp hh
    refine ⟨ha, hb, Array.toList_inj.mp ?_⟩
    rw [_root_.Std.Rcc.toList_toArray]
    exact ht
  · rintro ⟨ha, hb, ht⟩
    apply Array.toList_inj.mp
    rw [_root_.Std.Rcc.toList_toArray, Array.toList_append]
    apply convert.mpr
    refine ⟨ha, hb, ?_⟩
    rw [← _root_.Std.Rcc.toList_toArray, ht]


public theorem Int.toArray_rco_succ_succ : type_of% @_root_.Int.toArray_rco_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Rco.toList_toArray, _root_.Std.Rco.toList_toArray]
  exact _root_.Int.toList_rco_succ_succ

public theorem Int.toArray_rco_succ_right_eq_append_map : type_of% @_root_.Int.toArray_rco_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Rco.toList_toArray, _root_.Std.Rco.toList_toArray]
  exact _root_.Int.toList_rco_succ_right_eq_cons_map h

public theorem Int.toArray_roo_succ_succ : type_of% @_root_.Int.toArray_roo_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Roo.toList_toArray, _root_.Std.Roo.toList_toArray]
  exact _root_.Int.toList_roo_succ_succ

public theorem Int.toArray_roo_succ_right_eq_append_map : type_of% @_root_.Int.toArray_roo_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Roo.toList_toArray, _root_.Std.Roo.toList_toArray]
  exact _root_.Int.toList_roo_succ_right_eq_cons_map h

public theorem Int.toArray_roc_succ_succ : type_of% @_root_.Int.toArray_roc_succ_succ := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_toArray]
  exact _root_.Int.toList_roc_succ_succ

public theorem Int.toArray_roc_succ_right_eq_append_map : type_of% @_root_.Int.toArray_roc_succ_right_eq_append_map := by
  intro m n h
  apply Array.toList_inj.mp
  rw [Array.toList_append, Array.toList_map, _root_.Std.Roc.toList_toArray, _root_.Std.Roc.toList_toArray]
  exact _root_.Int.toList_roc_succ_right_eq_cons_map h

public theorem Int.toList_roc_succ_succ : type_of% @_root_.Int.toList_roc_succ_succ := by
  intro m n
  rw [_root_.Int.toList_roc_eq_toList_rco, _root_.Int.toList_roc_eq_toList_rco]
  exact _root_.Int.toList_rco_succ_succ

public theorem Int.toArray_rcc_eq_singleton_append_iff : type_of% @_root_.Int.toArray_rcc_eq_singleton_append_iff := by
  intro xs m n a
  have convert := @_root_.Int.toList_rcc_eq_cons_iff xs.toList m n a
  constructor
  · intro h
    have hh := congrArg Array.toList h
    rw [_root_.Std.Rcc.toList_toArray, Array.toList_append] at hh
    obtain ⟨ha, hb, ht⟩ := convert.mp hh
    refine ⟨ha, hb, Array.toList_inj.mp ?_⟩
    rw [_root_.Std.Rcc.toList_toArray]
    exact ht
  · rintro ⟨ha, hb, ht⟩
    apply Array.toList_inj.mp
    rw [_root_.Std.Rcc.toList_toArray, Array.toList_append]
    apply convert.mpr
    refine ⟨ha, hb, ?_⟩
    rw [← _root_.Std.Rcc.toList_toArray, ht]


public theorem Nat.toList_ric_eq_singleton_iff : type_of% @_root_.Nat.toList_ric_eq_singleton_iff := by
  intros
  rw [_root_.Nat.toList_ric_eq_toList_rcc]
  exact _root_.Nat.toList_rcc_eq_singleton_iff

public theorem Int.toArray_roo_eq_singleton_iff : type_of% @_root_.Int.toArray_roo_eq_singleton_iff := by
  intros
  refine Array.toList_inj.symm.trans ?_
  rw [_root_.Std.Roo.toList_toArray]
  exact _root_.Int.toList_roo_eq_singleton_iff

public theorem List.range'_eq_toList_rco : type_of% @_root_.List.range'_eq_toList_rco := by
  intro m n
  apply List.ext_getElem?
  intro i
  rw [_root_.Nat.getElem?_toList_rco]
  split <;> rename_i h
  · exact (List.getElem?_range' (by omega)).trans (congrArg some (by rw [Nat.one_mul]))
  · apply getElem?_neg
    rw [List.length_range']
    omega

public theorem List.range_eq_toList_rco : type_of% @_root_.List.range_eq_toList_rco := by
  intro n
  apply List.ext_getElem?
  intro i
  rw [_root_.Nat.getElem?_toList_rco]
  split <;> rename_i h
  · exact (List.getElem?_range (by omega)).trans (congrArg some (Nat.zero_add _).symm)
  · apply getElem?_neg
    rw [List.length_range]
    omega

public theorem Array.getElem_ofFn_go : type_of% (private_decl% @_root_.Array.getElem_ofFn_go) := by
  intro n α f acc i k h w
  induction i generalizing acc k with
  | zero =>
    rw [dite_eq_left (show k < acc.size from w)]
    rfl
  | succ i ih =>
    unfold _root_.Array.ofFn.go
    rw [ih]
    case w => rw [Array.size_push]; omega
    let value := f ⟨n - i - 1, by omega⟩
    have size : (acc.push value).size = acc.size + 1 := Array.size_push ..
    by_cases prior : k < acc.size
    · rw [dite_eq_left prior, dite_eq_left (show k < (acc.push value).size by rw [size]; omega)]
      exact Array.getElem_push_lt prior
    · rw [dite_eq_right prior]
      by_cases current : k < (acc.push value).size
      · rw [dite_eq_left current, Array.getElem_push]
        rw [dite_eq_right prior]
        apply congrArg f
        apply Fin.ext
        dsimp only
        omega
      · rw [dite_eq_right current]
        apply congrArg f
        apply Fin.ext
        dsimp only
        rw [Array.size_push]
        omega

public theorem Array.getElem_ofFn : type_of% @_root_.Array.getElem_ofFn := by
  intro n α f i h
  have correct (count : Nat) (acc : Array α) (bound : count ≤ n)
      (size : acc.size + count = n)
      (initial : ∀ (j : Fin n) (inAcc : j.val < acc.size), acc[j.val] = f j) :
      ∀ (j : Fin n) (hj : j.val < (Array.ofFn.go f acc count bound).size),
        (Array.ofFn.go f acc count bound)[j.val] = f j := by
    induction count generalizing acc with
    | zero => exact initial
    | succ count ih =>
      apply ih <;> try (rw [Array.size_push]; omega)
      intro j inside
      rw [Array.getElem_push]
      split <;> rename_i hprev
      · exact initial j hprev
      · apply congrArg f
        apply Fin.ext
        rw [Array.size_push] at inside
        dsimp only
        omega
  exact correct n (Array.emptyWithCapacity n) (Nat.le_refl _) (Nat.zero_add _)
    (fun _ hj => False.elim (Nat.not_lt_zero _ hj)) ⟨i, (Array.size_ofFn (f := f)) ▸ h⟩ h

public theorem List.getElem_range : type_of% @_root_.List.getElem_range := by
  intro i n h
  apply Option.some.inj
  exact (List.getElem?_eq_getElem h).symm.trans (List.getElem?_range (by simpa only [List.length_range] using h))

public theorem List.getElem_range' : type_of% @_root_.List.getElem_range' := by
  intro s step i n h
  apply Option.some.inj
  exact (List.getElem?_eq_getElem h).symm.trans (List.getElem?_range' (by simpa only [List.length_range'] using h))

public theorem Array.range_eq_toArray_rco : type_of% @_root_.Array.range_eq_toArray_rco := by
  intro n
  apply Array.toList_inj.mp
  rw [Array.toList_range, _root_.Std.Rco.toList_toArray]
  exact _root_.List.range_eq_toList_rco

public theorem Array.range'_eq_toArray_rco : type_of% @_root_.Array.range'_eq_toArray_rco := by
  intro m n
  apply Array.toList_inj.mp
  rw [Array.toList_range', _root_.Std.Rco.toList_toArray]
  exact _root_.List.range'_eq_toList_rco

public theorem Std.Rcc.size_eq_ite_roc : type_of% @_root_.Std.Rcc.size_eq_ite_roc := by
  intro α r _ _ _ _ _ _ _ _
  by_cases h : r.lower ≤ r.upper
  · rw [ite_eq_left h, _root_.Std.Roc.size_eq_match_rcc]
    cases hs : UpwardEnumerable.succ? r.lower with
    | none => exact Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h hs
    | some next => exact Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h hs
  · rw [ite_eq_right h]
    exact Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ h

public theorem Std.Rco.size_eq_ite_roo : type_of% @_root_.Std.Rco.size_eq_ite_roo := by
  intro α r _ _ _ _ _ _ _ _
  by_cases h : r.lower < r.upper
  · rw [ite_eq_left h, _root_.Std.Roo.size_eq_match_rcc]
    cases hs : UpwardEnumerable.succ? r.lower with
    | none => exact Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h hs
    | some next => exact Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h hs
  · rw [ite_eq_right h]
    exact Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _ h

public theorem Std.Roc.size_eq_match_roc : type_of% @_root_.Std.Roc.size_eq_match_roc := by
  intro α r _ _ _ _ _ _ _ _
  rw [_root_.Std.Roc.size_eq_match_rcc]
  cases succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rcc.size_eq_ite_roc

public theorem Std.Ric.size_eq_match_roc : type_of% @_root_.Std.Ric.size_eq_match_roc := by
  intro α r _ _ _ _ _ _ _ _ _
  rw [_root_.Std.Ric.size_eq_match_rcc]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rcc.size_eq_ite_roc

public theorem Std.Roo.size_eq_match_roc : type_of% @_root_.Std.Roo.size_eq_match_roc := by
  intro α r _ _ _ _ _ _ _ _
  rw [_root_.Std.Roo.size_eq_match_rcc]
  cases succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rco.size_eq_ite_roo

public theorem Std.Rio.size_eq_match_roc : type_of% @_root_.Std.Rio.size_eq_match_roc := by
  intro α r _ _ _ _ _ _ _ _ _
  rw [_root_.Std.Rio.size_eq_match_rcc]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rco.size_eq_ite_roo

public theorem Std.Rci.size_eq_size_roi : type_of% @_root_.Std.Rci.size_eq_size_roi := by
  intro α r _ _ _ _ _
  rw [_root_.Std.Roi.size_eq_match_rci]
  cases hs : UpwardEnumerable.succ? r.lower with
  | none => exact Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ hs
  | some next => exact Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ hs

public theorem Std.Rci.size_eq_match_rci : type_of% @_root_.Std.Rci.size_eq_match_rci := by
  intro α r _ _ _ _ _
  cases hs : UpwardEnumerable.succ? r.lower with
  | none => exact Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ hs
  | some next => exact Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ hs

public theorem Std.Roi.size_eq_match_roi : type_of% @_root_.Std.Roi.size_eq_match_roi := by
  intro α r _ _ _ _ _
  rw [_root_.Std.Roi.size_eq_match_rci]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rci.size_eq_size_roi

public theorem Std.Rii.size_eq_match_roi : type_of% @_root_.Std.Rii.size_eq_match_roi := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rii.size_eq_match_rci]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rci.size_eq_size_roi

public theorem Std.Rcc.size_eq_ite_rcc : type_of% @_root_.Std.Rcc.size_eq_ite_rcc := by
  intro α r _ _ _ _ _ _ _ _
  by_cases h : r.lower ≤ r.upper
  · rw [ite_eq_left h]
    cases hs : UpwardEnumerable.succ? r.lower with
    | none => exact Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h hs
    | some next => exact Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h hs
  · rw [ite_eq_right h]
    exact Rxc.LawfulHasSize.size_eq_zero_of_not_le _ _ h

public theorem Std.Rco.size_eq_ite_rcc : type_of% @_root_.Std.Rco.size_eq_ite_rcc := by
  intro α r _ _ _ _ _ _ _ _
  by_cases h : r.lower < r.upper
  · rw [ite_eq_left h]
    cases hs : UpwardEnumerable.succ? r.lower with
    | none => exact Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h hs
    | some next => exact Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h hs
  · rw [ite_eq_right h]
    exact Rxo.LawfulHasSize.size_eq_zero_of_not_le _ _ h

end OmegaChecks.InitPort.Alternatives

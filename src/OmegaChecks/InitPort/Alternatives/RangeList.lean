module
public import Init.Data.Range.Polymorphic.Lemmas
import all Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Loop
import all Init.Data.Array.Basic
import all Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.NatLemmas
public import Init.Data.Range.Polymorphic.IntLemmas

/-! Size and lookup laws for finite ranges. -/

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

private theorem consRangeEmpty (p : Prop) [Decidable p] (a : α) (tail : List α) :
    (if p then a :: tail else []) = [] ↔ ¬p := by
  constructor
  · intro empty hp
    rw [ite_eq_left hp] at empty
    contradiction
  · intro no
    exact ite_eq_right no

private theorem arrayNilOfList (xs : List α) : xs.toArray = #[] ↔ xs = [] :=
  ⟨fun eq => congrArg Array.toList eq, fun eq => congrArg List.toArray eq⟩

public theorem Std.Rcc.toList_eq_nil_iff : type_of% @_root_.Std.Rcc.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rcc.toList_eq_ite_roc]
  exact consRangeEmpty _ _ _

public theorem Std.Rco.toList_eq_nil_iff : type_of% @_root_.Std.Rco.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rco.toList_eq_ite_roo]
  exact consRangeEmpty _ _ _

public theorem Std.Roo.toList_eq_nil_iff : type_of% @_root_.Std.Roo.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _
  rw [_root_.Std.Roo.toList_eq_match_rco]
  cases h : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro _ _ eq
      cases eq
    · intro _
      rfl
  | some next =>
    constructor
    · intro empty a eq
      cases eq
      exact _root_.Std.Rco.toList_eq_nil_iff.mp empty
    · intro noneBelow
      exact _root_.Std.Rco.toList_eq_nil_iff.mpr (noneBelow next rfl)

public theorem Std.Rcc.toArray_eq_empty_iff : type_of% @_root_.Std.Rcc.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _
  rw [← _root_.Std.Rcc.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rcc.toList_eq_nil_iff

public theorem Std.Rco.toArray_eq_empty_iff : type_of% @_root_.Std.Rco.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _
  rw [← _root_.Std.Rco.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rco.toList_eq_nil_iff

public theorem Std.Roo.toArray_eq_empty_iff : type_of% @_root_.Std.Roo.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _
  rw [← _root_.Std.Roo.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Roo.toList_eq_nil_iff

public theorem Std.Rci.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Rci.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty
    change false = true at empty
    cases empty
  · intro absent
    exact (absent r.lower (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _))).elim

public theorem Std.Ric.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Ric.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty
    change false = true at empty
    cases empty
  · intro absent
    exact (absent r.upper (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl _))).elim

public theorem Std.Rii.isEmpty_iff_forall_not_mem : type_of% @_root_.Std.Rii.isEmpty_iff_forall_not_mem := by
  intro α r _ _ _ _ _ _ _
  constructor
  · intro empty a _
    exact (_root_.Std.Rii.isEmpty_iff.mp empty) ⟨a⟩
  · intro absent
    exact _root_.Std.Rii.isEmpty_iff.mpr fun ⟨a⟩ => absent a True.intro

public theorem Std.Roc.toList_eq_nil_iff : type_of% @_root_.Std.Roc.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  cases s : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro _ lt
      obtain ⟨n, h⟩ := UpwardEnumerable.lt_iff.mp lt
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, s] at h
      cases h
    · intro _
      rfl
  | some next =>
    constructor
    · intro empty lt
      obtain ⟨n, h⟩ := UpwardEnumerable.lt_iff.mp lt
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, s] at h
      exact (_root_.Std.Rcc.toList_eq_nil_iff.mp empty) (UpwardEnumerable.le_iff.mpr ⟨n, h⟩)
    · intro before
      exact _root_.Std.Rcc.toList_eq_nil_iff.mpr fun le =>
        before (UpwardEnumerable.lt_iff.mpr (UpwardEnumerable.lt_of_lt_of_le
          (UpwardEnumerable.lt_succ? s) (UpwardEnumerable.le_iff.mp le)))

public theorem Std.Roc.toArray_eq_empty_iff : type_of% @_root_.Std.Roc.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [← _root_.Std.Roc.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Roc.toList_eq_nil_iff

public theorem Std.Rxi.Iterator.toList_eq_match : type_of% @_root_.Std.Rxi.Iterator.toList_eq_match := by
  intro α _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxi.Iterator.step_eq_step]
  unfold _root_.Std.Rxi.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a => rfl

public theorem Std.Rxc.Iterator.toList_eq_match : type_of% @_root_.Std.Rxc.Iterator.toList_eq_match := by
  intro α _ _ _ _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxc.Iterator.step_eq_step]
  unfold _root_.Std.Rxc.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a =>
    dsimp only
    by_cases bound : a ≤ it.internalState.upperBound
    · rw [ite_eq_left bound, ite_eq_left bound]
    · rw [ite_eq_right bound, ite_eq_right bound]

public theorem Std.Rxo.Iterator.toList_eq_match : type_of% @_root_.Std.Rxo.Iterator.toList_eq_match := by
  intro α _ _ _ _ _ _ it
  rw [_root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Rxo.Iterator.step_eq_step]
  unfold _root_.Std.Rxo.Iterator.step
  dsimp only [Subtype.val]
  cases h : it.internalState.next with
  | none => rfl
  | some a =>
    dsimp only
    by_cases bound : a < it.internalState.upperBound
    · rw [ite_eq_left bound, ite_eq_left bound]
    · rw [ite_eq_right bound, ite_eq_right bound]

public theorem Std.Roi.toList_eq_match_rci : type_of% @_root_.Std.Roi.toList_eq_match_rci := by
  intro α r _ _ _
  unfold _root_.Std.Roi.toList _root_.Std.Roi.Internal.iter
  cases start : UpwardEnumerable.succ? r.lower with
  | none => rw [_root_.Std.Rxi.Iterator.toList_eq_match]
  | some a => rfl

public theorem Std.Rii.toList_eq_match_rci : type_of% @_root_.Std.Rii.toList_eq_match_rci := by
  intro α r _ _ _ _
  unfold _root_.Std.Rii.toList _root_.Std.Rii.Internal.iter
  cases start : Least?.least? (α := α) with
  | none => rw [_root_.Std.Rxi.Iterator.toList_eq_match]
  | some a => rfl

public theorem Std.Roc.toList_eq_match : type_of% @_root_.Std.Roc.toList_eq_match := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rcc.toList_eq_ite_roc

public theorem Std.Roo.toList_eq_match : type_of% @_root_.Std.Roo.toList_eq_match := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Roo.toList_eq_match_rco]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rco.toList_eq_ite_roo

public theorem Std.Rci.length_toList : type_of% @_root_.Std.Rci.length_toList := by
  intro α r _ _ _ _ _
  obtain ⟨lo⟩ := r
  generalize hn : Rxi.HasSize.size lo = n
  induction n generalizing lo with
  | zero => exact False.elim (Nat.not_lt_zero _ (hn ▸ _root_.Std.Rxi.size_pos (lo := lo)))
  | succ n ih =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, List.length_cons, _root_.Std.Roi.toList_eq_match_rci]
    cases hs : UpwardEnumerable.succ? lo with
    | none => exact (Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none _ hs).symm
    | some next =>
      have eq := Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ hs
      exact (congrArg Nat.succ (ih next (Nat.succ.inj (eq.symm.trans hn)))).trans eq.symm

public theorem Std.Roi.length_toList : type_of% @_root_.Std.Roi.length_toList := by
  intro α r _ _ _ _ _
  rw [_root_.Std.Roi.toList_eq_match_rci, _root_.Std.Roi.size_eq_match_rci]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some next => exact _root_.Std.Rci.length_toList

public theorem Std.Rii.length_toList : type_of% @_root_.Std.Rii.length_toList := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rii.toList_eq_match_rci, _root_.Std.Rii.size_eq_match_rci]
  cases Least?.least? (α := α) with
  | none => rfl
  | some next => exact _root_.Std.Rci.length_toList

public theorem Std.Rci.getElem?_toList_eq : type_of% @_root_.Std.Rci.getElem?_toList_eq := by
  intro α _ _ _ r i
  induction i generalizing r with
  | zero =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, UpwardEnumerable.succMany?_zero]
    rfl
  | succ i ih =>
    rw [_root_.Std.Rci.toList_eq_toList_roi, List.getElem?_cons_succ,
      _root_.Std.Roi.toList_eq_match_rci, UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
    cases UpwardEnumerable.succ? r.lower with
    | none => rfl
    | some next => exact ih (r := ⟨next⟩)

public theorem Std.toList_roc_eq_toList_rcc_of_isSome_succ? :
    type_of% @_root_.Std.toList_roc_eq_toList_rcc_of_isSome_succ? := by
  intro α _ _ _ _ _ _ lo hi h
  rw [_root_.Std.Roc.toList_eq_match_rcc]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.toList_roo_eq_toList_rco_of_isSome_succ? :
    type_of% @_root_.Std.toList_roo_eq_toList_rco_of_isSome_succ? := by
  intro α _ _ _ _ _ _ lo hi h
  rw [_root_.Std.Roo.toList_eq_match_rco]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.toList_roi_eq_toList_rci_of_isSome_succ? :
    type_of% @_root_.Std.toList_roi_eq_toList_rci_of_isSome_succ? := by
  intro α _ _ _ lo h
  rw [_root_.Std.Roi.toList_eq_match_rci]
  dsimp only
  generalize hs : UpwardEnumerable.succ? lo = start at h ⊢
  cases start with
  | none => cases h
  | some next => rfl

public theorem Std.Roi.getElem?_toList_eq : type_of% @_root_.Std.Roi.getElem?_toList_eq := by
  intro α r _ _ _ _ _ _ i
  rw [_root_.Std.Roi.toList_eq_match_rci, UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?]
  cases UpwardEnumerable.succ? r.lower with
  | none => rfl
  | some a => exact _root_.Std.Rci.getElem?_toList_eq

private theorem lookupPresent {o : Option α} {a : α} (eq : o = some a) : o.isSome := eq ▸ rfl

private theorem filterLookupPresent {p : α → Bool} {o : Option α} {a : α}
    (eq : o.filter p = some a) : o.isSome := by
  cases o with
  | none => cases eq
  | some x => rfl

public theorem Std.Rcc.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rcc.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rcc.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rcc.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rcc.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rcc.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roc.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roc.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roc.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roc.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roc.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roc.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Ric.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Ric.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Ric.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Ric.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Ric.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Ric.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rco.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rco.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rco.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rco.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rco.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rco.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roo.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roo.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roo.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roo.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roo.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Roo.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rio.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rio.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rio.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rio.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rio.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ _ _ i h
  exact filterLookupPresent ((_root_.Std.Rio.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rci.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rci.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rci.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rci.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rci.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rci.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Roi.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Roi.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Roi.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Roi.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Roi.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Roi.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

public theorem Std.Rii.isSome_succMany?_of_lt_length_toList :
    type_of% @_root_.Std.Rii.isSome_succMany?_of_lt_length_toList := by
  intro α r _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rii.getElem?_toList_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toList i h))

public theorem Std.Rii.isSome_succMany?_of_lt_size_toArray :
    type_of% @_root_.Std.Rii.isSome_succMany?_of_lt_size_toArray := by
  intro α r _ _ _ _ _ i h
  exact lookupPresent ((_root_.Std.Rii.getElem?_toArray_eq (r := r) (i := i)).symm.trans
    (getElem?_pos r.toArray i h))

private theorem rangeFilterEqSome {o : Option α} {a : α} (p : α → Bool) :
    o.filter p = some a ↔ o = some a ∧ p a := by
  constructor
  · intro eq
    cases o with
    | none => cases eq
    | some x =>
      by_cases pass : p x = true
      · rw [Option.filter_some_pos pass] at eq
        cases eq
        exact ⟨rfl, pass⟩
      · rw [Option.filter_some, ite_eq_right pass] at eq
        cases eq
  · rintro ⟨rfl, pass⟩
    exact Option.filter_some_pos pass

private theorem indexedRangeMem {xs : List α} {f : Nat → Option α} {a : α} (p : α → Bool)
    (lookup : ∀ i, xs[i]? = (f i).filter p) : a ∈ xs ↔ (∃ i, f i = some a) ∧ p a := by
  constructor
  · intro mem
    obtain ⟨i, h⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨someAt, pass⟩ := (rangeFilterEqSome p).mp ((lookup i).symm.trans h)
    exact ⟨⟨i, someAt⟩, pass⟩
  · rintro ⟨⟨i, hit⟩, pass⟩
    exact List.mem_iff_getElem?.mpr ⟨i, (lookup i).trans ((rangeFilterEqSome p).mpr ⟨hit, pass⟩)⟩

public theorem Std.Rcc.mem_toList_iff_mem : type_of% @_root_.Std.Rcc.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? i r.lower)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Rcc.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.le_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.le_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Rco.mem_toList_iff_mem : type_of% @_root_.Std.Rco.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? i r.lower)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Rco.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.le_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.le_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Roc.mem_toList_iff_mem : type_of% @_root_.Std.Roc.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? (i + 1) r.lower)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Roc.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.lt_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.lt_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Roo.mem_toList_iff_mem : type_of% @_root_.Std.Roo.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ a
  exact (indexedRangeMem (f := fun i => UpwardEnumerable.succMany? (i + 1) r.lower)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Roo.getElem?_toList_eq)).trans
      ⟨fun ⟨reach, above⟩ => ⟨UpwardEnumerable.lt_iff.mpr reach, of_decide_eq_true above⟩,
       fun h => ⟨UpwardEnumerable.lt_iff.mp h.1, decide_eq_true h.2⟩⟩

public theorem Std.Rci.mem_toList_iff_mem : type_of% @_root_.Std.Rci.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ a
  constructor
  · intro h
    obtain ⟨i, hit⟩ := List.mem_iff_getElem?.mp h
    exact UpwardEnumerable.le_iff.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.symm.trans hit⟩
  · intro h
    obtain ⟨i, hit⟩ := UpwardEnumerable.le_iff.mp h
    exact List.mem_iff_getElem?.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.trans hit⟩

public theorem Std.Roi.mem_toList_iff_mem : type_of% @_root_.Std.Roi.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [_root_.Std.Roi.toList_eq_match_rci]
  cases hs : UpwardEnumerable.succ? r.lower with
  | none =>
    constructor
    · intro h
      cases h
    · intro h
      obtain ⟨i, hit⟩ := UpwardEnumerable.lt_iff.mp h
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hit
      cases hit
  | some next =>
    constructor
    · intro h
      obtain ⟨i, hit⟩ := List.mem_iff_getElem?.mp h
      apply UpwardEnumerable.lt_iff.mpr
      refine ⟨i, ?_⟩
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs]
      exact _root_.Std.Rci.getElem?_toList_eq.symm.trans hit
    · intro h
      obtain ⟨i, hit⟩ := UpwardEnumerable.lt_iff.mp h
      rw [UpwardEnumerable.succMany?_add_one_eq_succ?_bind_succMany?, hs] at hit
      exact List.mem_iff_getElem?.mpr ⟨i, _root_.Std.Rci.getElem?_toList_eq.trans hit⟩

public theorem Std.Ric.mem_toList_iff_mem : type_of% @_root_.Std.Ric.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  letI : Nonempty α := ⟨r.upper⟩
  have mem := indexedRangeMem (a := a) (f := fun i => UpwardEnumerable.succMany? i UpwardEnumerable.least)
    (fun x => decide (x ≤ r.upper)) (fun _ => _root_.Std.Ric.getElem?_toList_eq (r := r))
  exact ⟨fun h => of_decide_eq_true (mem.mp h).2,
    fun h => mem.mpr ⟨UpwardEnumerable.least_le, decide_eq_true h⟩⟩

public theorem Std.Rio.mem_toList_iff_mem : type_of% @_root_.Std.Rio.mem_toList_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  letI : Nonempty α := ⟨r.upper⟩
  have mem := indexedRangeMem (a := a) (f := fun i => UpwardEnumerable.succMany? i UpwardEnumerable.least)
    (fun x => decide (x < r.upper)) (fun _ => _root_.Std.Rio.getElem?_toList_eq (r := r))
  exact ⟨fun h => of_decide_eq_true (mem.mp h).2,
    fun h => mem.mpr ⟨UpwardEnumerable.least_le, decide_eq_true h⟩⟩

public theorem Std.Rii.mem_toList : type_of% @_root_.Std.Rii.mem_toList := by
  intro α r _ _ _ _ _ a
  letI : Nonempty α := ⟨a⟩
  obtain ⟨i, hit⟩ := UpwardEnumerable.least_le (a := a)
  apply List.mem_iff_getElem?.mpr
  refine ⟨i, _root_.Std.Rii.getElem?_toList_eq.trans ?_⟩
  rw [UpwardEnumerable.least?_eq_some]
  exact hit

public theorem Std.Rcc.mem_toArray_iff_mem : type_of% @_root_.Std.Rcc.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rcc.toList_toArray]
  exact _root_.Std.Rcc.mem_toList_iff_mem

public theorem Std.Rco.mem_toArray_iff_mem : type_of% @_root_.Std.Rco.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rco.toList_toArray]
  exact _root_.Std.Rco.mem_toList_iff_mem

public theorem Std.Roc.mem_toArray_iff_mem : type_of% @_root_.Std.Roc.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roc.toList_toArray]
  exact _root_.Std.Roc.mem_toList_iff_mem

public theorem Std.Roo.mem_toArray_iff_mem : type_of% @_root_.Std.Roo.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roo.toList_toArray]
  exact _root_.Std.Roo.mem_toList_iff_mem

public theorem Std.Rci.mem_toArray_iff_mem : type_of% @_root_.Std.Rci.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rci.toList_toArray]
  exact _root_.Std.Rci.mem_toList_iff_mem

public theorem Std.Roi.mem_toArray_iff_mem : type_of% @_root_.Std.Roi.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Roi.toList_toArray]
  exact _root_.Std.Roi.mem_toList_iff_mem

public theorem Std.Ric.mem_toArray_iff_mem : type_of% @_root_.Std.Ric.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Ric.toList_toArray]
  exact _root_.Std.Ric.mem_toList_iff_mem

public theorem Std.Rio.mem_toArray_iff_mem : type_of% @_root_.Std.Rio.mem_toArray_iff_mem := by
  intro α r _ _ _ _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rio.toList_toArray]
  exact _root_.Std.Rio.mem_toList_iff_mem

public theorem Std.Rii.mem_toArray : type_of% @_root_.Std.Rii.mem_toArray := by
  intro α r _ _ _ _ _ a
  rw [Array.mem_def, _root_.Std.Rii.toList_toArray]
  exact _root_.Std.Rii.mem_toList

public theorem Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxc.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxc.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      dsimp only
      by_cases bound : a ≤ it.internalState.upperBound
      · rw [ite_eq_left bound]
        apply List.Pairwise.cons
        · intro b member
          obtain ⟨c, step, le⟩ := _root_.Std.Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
            (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
          exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
        · apply ihy (out := a)
          apply _root_.Std.Rxc.Iterator.isPlausibleStep_iff.mpr
          unfold _root_.Std.Rxc.Iterator.step
          rw [hn]
          dsimp only
          rw [ite_eq_left bound]
      · rw [ite_eq_right bound]
        exact .nil

public theorem Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxo.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxo.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      dsimp only
      by_cases bound : a < it.internalState.upperBound
      · rw [ite_eq_left bound]
        apply List.Pairwise.cons
        · intro b member
          obtain ⟨c, step, le⟩ := _root_.Std.Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
            (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
          exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
        · apply ihy (out := a)
          apply _root_.Std.Rxo.Iterator.isPlausibleStep_iff.mpr
          unfold _root_.Std.Rxo.Iterator.step
          rw [hn]
          dsimp only
          rw [ite_eq_left bound]
      · rw [ite_eq_right bound]
        exact .nil

public theorem Std.Rxi.Iterator.pairwise_toList_upwardEnumerableLt :
    type_of% @_root_.Std.Rxi.Iterator.pairwise_toList_upwardEnumerableLt := by
  intro α _ _ _ it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Rxi.Iterator.toList_eq_match]
    cases hn : it.internalState.next with
    | none => exact .nil
    | some a =>
      apply List.Pairwise.cons
      · intro b member
        obtain ⟨c, step, le⟩ := _root_.Std.Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput
          (_root_.Std.Iter.mem_toList_iff_isPlausibleIndirectOutput.mp member)
        exact UpwardEnumerable.lt_of_lt_of_le (UpwardEnumerable.lt_succ? step) le
      · apply ihy (out := a)
        apply _root_.Std.Rxi.Iterator.isPlausibleStep_iff.mpr
        unfold _root_.Std.Rxi.Iterator.step
        rw [hn]

private theorem orderedHeadAbsent {R : α → α → Prop} [Std.Asymm R] {x : α} {xs : List α}
    (ordered : (x :: xs).Pairwise R) (mem : x ∈ xs) : False :=
  let loop := List.rel_of_pairwise_cons ordered mem
  Std.Asymm.asymm x x loop loop

public theorem Std.eq_of_pairwise_lt_of_mem_iff_mem :
    type_of% (private_decl% @_root_.Std.eq_of_pairwise_lt_of_mem_iff_mem) := by
  intro α rel asymm l l' sorted sorted' same
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons y ys => cases (same y).mpr List.mem_cons_self
  | cons x xs ih =>
    cases l' with
    | nil => cases (same x).mp List.mem_cons_self
    | cons y ys =>
      have heads : x = y := by
        rcases List.mem_cons.mp ((same x).mp List.mem_cons_self) with eq | right
        · exact eq
        · rcases List.mem_cons.mp ((same y).mpr List.mem_cons_self) with eq | left
          · exact eq.symm
          · exact (Std.Asymm.asymm x y (List.rel_of_pairwise_cons sorted left)
              (List.rel_of_pairwise_cons sorted' right)).elim
      cases heads
      apply congrArg (List.cons x)
      apply ih sorted.tail sorted'.tail
      intro a
      constructor
      · intro mem
        rcases List.mem_cons.mp ((same a).mp (.tail x mem)) with rfl | found
        · exact (orderedHeadAbsent sorted mem).elim
        · exact found
      · intro mem
        rcases List.mem_cons.mp ((same a).mpr (.tail x mem)) with rfl | found
        · exact (orderedHeadAbsent sorted' mem).elim
        · exact found

private theorem sortedRangeImage [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α]
    (ys xs : List α) (left : ys.Pairwise UpwardEnumerable.LT) (right : xs.Pairwise UpwardEnumerable.LT)
    (preimage : ∀ y, y ∈ ys ↔ ∃ x, y = succ x ∧ x ∈ xs) : ys = xs.map succ := by
  apply (private_decl% _root_.Std.eq_of_pairwise_lt_of_mem_iff_mem) left
    (right.map succ fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr)
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := (preimage y).mp hy
    exact List.mem_map.mpr ⟨x, mem, eq.symm⟩
  · intro hy
    obtain ⟨x, mem, eq⟩ := List.mem_map.mp hy
    exact (preimage y).mpr ⟨x, eq.symm, mem⟩

public theorem Std.Rcc.toList_succ_succ_eq_map : type_of% @_root_.Std.Rcc.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Rcc.pairwise_toList_upwardEnumerableLt _root_.Std.Rcc.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rcc.mem_succ_succ_iff.mp (_root_.Std.Rcc.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rcc.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rcc.mem_toList_iff_mem.mpr (_root_.Std.Rcc.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rcc.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rco.toList_succ_succ_eq_map : type_of% @_root_.Std.Rco.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Rco.pairwise_toList_upwardEnumerableLt _root_.Std.Rco.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rco.mem_succ_succ_iff.mp (_root_.Std.Rco.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rco.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rco.mem_toList_iff_mem.mpr (_root_.Std.Rco.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rco.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rci.toList_succ_succ_eq_map : type_of% @_root_.Std.Rci.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo
  apply sortedRangeImage _ _ _root_.Std.Rci.pairwise_toList_upwardEnumerableLt _root_.Std.Rci.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Rci.mem_succ_iff.mp (_root_.Std.Rci.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Rci.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Rci.mem_toList_iff_mem.mpr (_root_.Std.Rci.mem_succ_iff.mpr
      ⟨x, eq, _root_.Std.Rci.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roc.toList_succ_succ_eq_map : type_of% @_root_.Std.Roc.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Roc.pairwise_toList_upwardEnumerableLt _root_.Std.Roc.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roc.mem_succ_succ_iff.mp (_root_.Std.Roc.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roc.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roc.mem_toList_iff_mem.mpr (_root_.Std.Roc.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roc.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roo.toList_succ_succ_eq_map : type_of% @_root_.Std.Roo.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo hi
  apply sortedRangeImage _ _ _root_.Std.Roo.pairwise_toList_upwardEnumerableLt _root_.Std.Roo.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roo.mem_succ_succ_iff.mp (_root_.Std.Roo.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roo.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roo.mem_toList_iff_mem.mpr (_root_.Std.Roo.mem_succ_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roo.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Roi.toList_succ_succ_eq_map : type_of% @_root_.Std.Roi.toList_succ_succ_eq_map := by
  intro α _ _ _ _ _ _ _ _ lo
  apply sortedRangeImage _ _ _root_.Std.Roi.pairwise_toList_upwardEnumerableLt _root_.Std.Roi.pairwise_toList_upwardEnumerableLt
  intro y
  constructor
  · intro hy
    obtain ⟨x, eq, mem⟩ := _root_.Std.Roi.mem_succ_iff.mp (_root_.Std.Roi.mem_toList_iff_mem.mp hy)
    exact ⟨x, eq, _root_.Std.Roi.mem_toList_iff_mem.mpr mem⟩
  · rintro ⟨x, eq, mem⟩
    exact _root_.Std.Roi.mem_toList_iff_mem.mpr (_root_.Std.Roi.mem_succ_iff.mpr
      ⟨x, eq, _root_.Std.Roi.mem_toList_iff_mem.mp mem⟩)

public theorem Std.Rco.toList_eq_ite_rco : type_of% @_root_.Std.Rco.toList_eq_ite_rco := by
  intro α r _ _ _ _ _ _
  rw [_root_.Std.Rco.toList_eq_ite_roo]
  by_cases inside : r.lower < r.upper
  · rw [ite_eq_left inside, ite_eq_left inside, _root_.Std.Roo.toList_eq_match_rco]
    cases UpwardEnumerable.succ? r.lower <;> rfl
  · rw [ite_eq_right inside, ite_eq_right inside]

public theorem Std.Ric.toList_ne_nil : type_of% @_root_.Std.Ric.toList_ne_nil := by
  intro α r _ _ _ _ _ _ _ _ empty
  have member := (_root_.Std.Ric.mem_toList_iff_mem (r := r)).mpr
    (UpwardEnumerable.le_iff.mpr (UpwardEnumerable.le_refl r.upper))
  rw [empty] at member
  cases member

public theorem Std.Ric.toArray_ne_empty : type_of% @_root_.Std.Ric.toArray_ne_empty := by
  intro α r _ _ _ _ _ _ _ _ empty
  exact _root_.Std.Ric.toList_ne_nil ((_root_.Std.Ric.toList_toArray (r := r)).symm.trans (congrArg Array.toList empty))

public theorem Std.Rii.toList_eq_nil_iff : type_of% @_root_.Std.Rii.toList_eq_nil_iff := by
  intro α r _ _ _ _ _ _ _ _
  constructor
  · intro empty ⟨a⟩
    have member := _root_.Std.Rii.mem_toList (r := r) (a := a)
    rw [empty] at member
    cases member
  · intro absent
    cases h : r.toList with
    | nil => rfl
    | cons a _ => exact (absent ⟨a⟩).elim

public theorem Std.Rii.toArray_eq_empty_iff : type_of% @_root_.Std.Rii.toArray_eq_empty_iff := by
  intro α r _ _ _ _ _ _ _ _
  rw [← _root_.Std.Rii.toArray_toList]
  exact (arrayNilOfList _).trans _root_.Std.Rii.toList_eq_nil_iff

end OmegaChecks.InitPort.Alternatives

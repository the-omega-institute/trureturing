module
public import Init.Data.Range.Polymorphic.Lemmas
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

end OmegaChecks.InitPort.Alternatives

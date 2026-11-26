module
public import Init.Data.List.Sublist

/-! Subsequence witnesses for finite filtering, mapping and splitting. -/
namespace OmegaChecks.InitPort.Alternatives.List
open _root_.List

public theorem filter_subset : type_of% @_root_.List.filter_subset := by
  intro α xs ys p sub x mem
  obtain ⟨inXs, keep⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨sub inXs, keep⟩

public theorem sublist_filterMap_iff : type_of% @_root_.List.sublist_filterMap_iff := by
  intro β α xs ys f
  refine ⟨?_, fun ⟨_, sub, eq⟩ => eq ▸ sub.filterMap f⟩
  induction xs generalizing ys with
  | nil => exact fun sub => ⟨[], .slnil, sublist_nil.mp sub⟩
  | cons x xs ih =>
    intro sub
    cases h : f x with
    | none =>
      rw [filterMap_cons_none h] at sub
      obtain ⟨pre, kept, eq⟩ := ih sub
      exact ⟨pre, kept.cons x, eq⟩
    | some y =>
      rw [filterMap_cons_some h] at sub
      cases sub with
      | cons _ rest =>
        obtain ⟨pre, kept, eq⟩ := ih rest
        exact ⟨pre, kept.cons x, eq⟩
      | cons_cons _ rest =>
        obtain ⟨pre, kept, rfl⟩ := ih rest
        exact ⟨x :: pre, kept.cons_cons x, (filterMap_cons_some h).symm⟩

private theorem filterMapPoint (p : α → Bool) (xs : _root_.List α) :
    xs.filterMap (_root_.Option.guard p) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases keep : p x
    · have eq : Option.guard p x = some x := ite_eq_left keep
      rw [filterMap_cons_some eq, filter_cons_of_pos keep, ih]
    · have eq : Option.guard p x = none := ite_eq_right keep
      rw [filterMap_cons_none eq, filter_cons_of_neg keep, ih]

public theorem Sublist.filter : type_of% @_root_.List.Sublist.filter := by
  intro α p xs ys sub
  rw [← filterMapPoint p xs, ← filterMapPoint p ys]
  exact sub.filterMap _

public theorem sublist_map_iff : type_of% @_root_.List.sublist_map_iff := by
  intro β α xs ys f
  have point (as : _root_.List α) : as.filterMap (some ∘ f) = as.map f := by
    induction as with
    | nil => rfl
    | cons x xs ih => exact congrArg (f x :: ·) ih
  refine ⟨fun sub => ?_, fun ⟨_, sub, eq⟩ => eq ▸ sub.map _⟩
  rw [← point] at sub
  obtain ⟨pre, kept, eq⟩ := sublist_filterMap_iff.mp sub
  exact ⟨pre, kept, eq.trans (point _)⟩

public theorem sublist_filter_iff : type_of% @_root_.List.sublist_filter_iff := by
  intro α xs ys p
  rw [← filterMapPoint]
  exact sublist_filterMap_iff.trans (exists_congr fun pre => and_congr_right fun _ =>
    ⟨fun eq => eq.trans (filterMapPoint p pre), fun eq => eq.trans (filterMapPoint p pre).symm⟩)

public theorem prefix_filter_iff : type_of% @_root_.List.prefix_filter_iff := by
  intro α p xs ys
  rw [← filterMapPoint]
  exact prefix_filterMap_iff.trans (exists_congr fun pre => and_congr_right fun _ =>
    ⟨fun eq => eq.trans (filterMapPoint p pre), fun eq => eq.trans (filterMapPoint p pre).symm⟩)

public theorem suffix_filter_iff : type_of% @_root_.List.suffix_filter_iff := by
  intro α p xs ys
  rw [← filterMapPoint]
  exact suffix_filterMap_iff.trans (exists_congr fun pre => and_congr_right fun _ =>
    ⟨fun eq => eq.trans (filterMapPoint p pre), fun eq => eq.trans (filterMapPoint p pre).symm⟩)

public theorem infix_filter_iff : type_of% @_root_.List.infix_filter_iff := by
  intro α p xs ys
  rw [← filterMapPoint]
  exact infix_filterMap_iff.trans (exists_congr fun pre => and_congr_right fun _ =>
    ⟨fun eq => eq.trans (filterMapPoint p pre), fun eq => eq.trans (filterMapPoint p pre).symm⟩)

public theorem prefix_iff_eq_take : type_of% @_root_.List.prefix_iff_eq_take := by
  intro α xs ys
  exact ⟨fun ⟨_, eq⟩ => eq ▸ take_left.symm, fun e => e ▸ take_prefix _ _⟩

public theorem append_sublist_iff : type_of% @_root_.List.append_sublist_iff := by
  intro α full xs ys
  refine ⟨?_, fun ⟨_, _, eq, h, k⟩ => eq ▸ h.append k⟩
  induction xs generalizing full with
  | nil => exact fun sub => ⟨[], full, rfl, .slnil, sub⟩
  | cons a xs ih =>
    intro sub
    obtain ⟨prefix₁, rest, rfl, member, tail⟩ := cons_sublist_iff.mp sub
    obtain ⟨prefix₂, suffix, rfl, sub₂, sub₃⟩ := ih tail
    exact ⟨prefix₁ ++ prefix₂, suffix, (append_assoc ..).symm, (singleton_sublist.mpr member).append sub₂, sub₃⟩

public theorem IsPrefix.head : type_of% @_root_.List.IsPrefix.head := by
  intro α xs ys h nonempty
  obtain ⟨tail, rfl⟩ := h
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons _ _ => rfl

public theorem IsSuffix.getLast : type_of% @_root_.List.IsSuffix.getLast := by
  intro α xs ys h nonempty
  obtain ⟨front, rfl⟩ := h
  exact (getLast_append_of_ne_nil _ nonempty).symm

public theorem prefix_iff_getElem? : type_of% @_root_.List.prefix_iff_getElem? := by
  intro α xs ys
  refine ⟨fun sub i bound =>
    (getElem?_eq_getElem (Nat.lt_of_lt_of_le bound sub.length_le)).trans
      (congrArg some (sub.getElem bound).symm), fun entries => ?_⟩
  induction xs generalizing ys with
  | nil => exact nil_prefix
  | cons x xs ih =>
    cases ys with
    | nil => exact nomatch entries 0 (Nat.zero_lt_succ _)
    | cons y ys =>
      have head : some y = some x := entries 0 (Nat.zero_lt_succ _)
      cases Option.some.inj head
      exact cons_prefix_cons.mpr ⟨rfl, ih (fun i bound => entries (i+1) (Nat.succ_lt_succ bound))⟩

public theorem append_cancel_right :
    type_of% @_root_.List.append_cancel_right := by
  intro α xs tail ys eq
  have sizes := congrArg _root_.List.length eq
  rw [length_append, length_append] at sizes
  have same := Nat.add_right_cancel sizes
  clear sizes
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => exact nomatch same
  | cons x xs ih =>
    cases ys with
    | nil => exact nomatch same
    | cons y ys =>
      obtain ⟨rfl, tails⟩ := cons.inj eq
      exact congrArg (x :: ·) (ih tails (Nat.succ.inj same))

public theorem isSublist_iff_sublist : type_of% @_root_.List.isSublist_iff_sublist := by
  intro α inst lawful xs ys
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => exact ⟨fun _ => .slnil, fun _ => rfl⟩
    | cons _ _ => exact ⟨(fun e => nomatch e), (fun h => nomatch h)⟩
  | cons y ys ih =>
    cases xs with
    | nil => exact ⟨fun _ => nil_sublist _, fun _ => rfl⟩
    | cons x xs =>
      rw [_root_.List.isSublist]
      by_cases hit : x == y
      · rw [ite_eq_left hit]
        cases eq_of_beq hit
        exact ih.trans cons_sublist_cons.symm
      · rw [ite_eq_right hit]
        refine ih.trans ⟨fun h => h.cons _, ?_⟩
        intro sub
        cases sub with
        | cons _ rest => exact rest
        | cons_cons => exact (hit (beq_self_eq_true _)).elim

public theorem isSuffixOf_iff_suffix : type_of% @_root_.List.isSuffixOf_iff_suffix := by
  intro α inst lawful xs ys
  exact _root_.List.isPrefixOf_iff_prefix.trans reverse_prefix

public theorem Sublist.of_sublist_append_left : type_of% @_root_.List.Sublist.of_sublist_append_left := by
  intro α xs ys zs disjoint sub
  obtain ⟨pre, post, rfl, lp, rp⟩ := sublist_append_iff.mp sub
  cases post with
  | nil => rw [append_nil]; exact lp
  | cons b bs => exact (disjoint b (mem_append_right _ mem_cons_self) (rp.mem mem_cons_self)).elim

public theorem Sublist.of_sublist_append_right : type_of% @_root_.List.Sublist.of_sublist_append_right := by
  intro α xs ys zs disjoint sub
  obtain ⟨pre, post, rfl, lp, rp⟩ := sublist_append_iff.mp sub
  cases pre with
  | nil => exact rp
  | cons a as => exact (disjoint a mem_cons_self (lp.mem mem_cons_self)).elim

public theorem sublist_flatten_iff : type_of% @_root_.List.sublist_flatten_iff := by
  intro α rows xs
  induction rows generalizing xs with
  | nil =>
    constructor
    · intro sub
      exact ⟨[], sublist_nil.mp sub, fun _ bound => nomatch bound⟩
    · rintro ⟨chosen, rfl, rowsEmpty⟩
      apply sublist_nil.mpr
      apply flatten_eq_nil_iff.mpr
      exact (forall_mem_iff_forall_getElem (P := (· = []))).mpr
        (fun i bound => sublist_nil.mp (rowsEmpty i bound))
  | cons row rows ih =>
    constructor
    · intro sub
      obtain ⟨first, more, rfl, sf, sm⟩ := sublist_append_iff.mp sub
      obtain ⟨chosen, rfl, point⟩ := ih.mp sm
      refine ⟨first :: chosen, rfl, ?_⟩
      intro i bound
      cases i with
      | zero => exact sf
      | succ i => exact point i (Nat.lt_of_succ_lt_succ bound)
    · rintro ⟨chosen, rfl, point⟩
      cases chosen with
      | nil => exact nil_sublist _
      | cons first more =>
        have sf : first <+ row := point 0 (Nat.zero_lt_succ _)
        have sm : more.flatten <+ rows.flatten :=
          ih.mpr ⟨more, rfl, fun i bound => point (i + 1) (Nat.succ_lt_succ bound)⟩
        exact sf.append sm

public theorem flatten_sublist_iff : type_of% @_root_.List.flatten_sublist_iff := by
  intro α rows xs
  induction rows generalizing xs with
  | nil =>
    exact ⟨fun _ => ⟨[xs], (append_nil _).symm, fun _ bound => nomatch bound⟩,
      fun _ => nil_sublist _⟩
  | cons row rows ih =>
    constructor
    · intro sub
      obtain ⟨first, more, rfl, sf, sm⟩ := append_sublist_iff.mp sub
      obtain ⟨chosen, rfl, point⟩ := ih.mp sm
      refine ⟨first :: chosen, rfl, ?_⟩
      intro i bound
      cases i with
      | zero => exact sf
      | succ i => exact point i (Nat.lt_of_succ_lt_succ bound)
    · rintro ⟨chosen, rfl, point⟩
      cases chosen with
      | nil =>
        have sf : row <+ [] := point 0 (Nat.zero_lt_succ _)
        have sm : rows.flatten <+ [] :=
          ih.mpr ⟨[], rfl, fun i bound => point (i+1) (Nat.succ_lt_succ bound)⟩
        exact sf.append sm
      | cons first more =>
        have sf : row <+ first := point 0 (Nat.zero_lt_succ _)
        have sm : rows.flatten <+ more.flatten :=
          ih.mpr ⟨more, rfl, fun i bound => point (i+1) (Nat.succ_lt_succ bound)⟩
        exact sf.append sm

end OmegaChecks.InitPort.Alternatives.List

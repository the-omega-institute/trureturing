module
public import Init.Data.List.Lemmas

/-! Structural proofs for boolean predicates and folds over strict lists. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem List.any_eq_true {α : Type u} {p : α → Bool} {l : _root_.List α} :
    l.any p = true ↔ ∃ x, x ∈ l ∧ p x = true := by
  induction l with
  | nil =>
    exact ⟨fun h => False.elim (Bool.false_ne_true h),
      fun ⟨_, m, _⟩ => False.elim (List.not_mem_nil m)⟩
  | cons a xs ih =>
    change (p a || xs.any p) = true ↔ _
    constructor
    · intro h
      cases Bool.or_eq_true_iff.mp h with
      | inl pa => exact ⟨a, .head _, pa⟩
      | inr rest =>
        obtain ⟨x, m, px⟩ := ih.mp rest
        exact ⟨x, .tail _ m, px⟩
    · rintro ⟨x, m, px⟩
      cases List.mem_cons.mp m with
      | inl e => exact Bool.or_eq_true_iff.mpr (.inl (e ▸ px))
      | inr t => exact Bool.or_eq_true_iff.mpr (.inr (ih.mpr ⟨x, t, px⟩))

public theorem List.all_eq_true {α : Type u} {p : α → Bool} {l : _root_.List α} :
    l.all p = true ↔ ∀ x, x ∈ l → p x = true := by
  induction l with
  | nil => exact ⟨fun _ _ m => False.elim (List.not_mem_nil m), fun _ => rfl⟩
  | cons a xs ih =>
    change (p a && xs.all p) = true ↔ _
    constructor
    · intro h x m
      obtain ⟨pa, rest⟩ := Bool.and_eq_true_iff.mp h
      cases List.mem_cons.mp m with
      | inl e => exact e.symm ▸ pa
      | inr t => exact ih.mp rest x t
    · exact fun h => Bool.and_eq_true_iff.mpr ⟨h a (.head _), ih.mpr (fun x m => h x (.tail _ m))⟩

public theorem List.foldl_eq_foldlM {β : Type u} {α : Type v} {f : β → α → β}
    {b : β} {l : _root_.List α} :
    l.foldl f b = (l.foldlM (m := Id) (pure <| f · ·) b).run := by
  induction l generalizing b with
  | nil => rfl
  | cons a xs ih => exact ih (b := f b a)

public theorem List.foldl_reverse {α : Type u} {β : Type v} {l : _root_.List α} {f : β → α → β} {b : β} :
    l.reverse.foldl f b = l.foldr (fun x y => f y x) b := by
  induction l with
  | nil => rfl
  | cons a xs ih =>
    exact (congrArg (fun ys => ys.foldl f b) List.reverse_cons).trans
      ((List.foldl_append (f := f) (b := b) (l := xs.reverse) (l' := [a])).trans
        (congrArg (fun x => f x a) ih))

public theorem List.foldr_eq_foldrM {α : Type u} {β : Type v} {f : α → β → β}
    {b : β} {l : _root_.List α} :
    l.foldr f b = (l.foldrM (m := Id) (pure <| f · ·) b).run :=
  List.foldl_reverse.symm.trans List.foldl_eq_foldlM

public theorem List.mem_filter : type_of% @_root_.List.mem_filter := by
  intro α p xs x
  induction xs with
  | nil => exact ⟨fun h => (List.not_mem_nil h).elim, fun h => (List.not_mem_nil h.1).elim⟩
  | cons a xs ih =>
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h]
      constructor
      · intro m
        cases List.mem_cons.mp m with
        | inl eq => exact ⟨List.mem_cons.mpr (.inl eq), eq.symm ▸ h⟩
        | inr rest => exact ⟨.tail _ (ih.mp rest).1, (ih.mp rest).2⟩
      · intro ⟨m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq => exact List.mem_cons.mpr (.inl eq)
        | inr tail => exact .tail _ (ih.mpr ⟨tail, hit⟩)
    · rw [List.filter_cons_of_neg h]
      constructor
      · intro m
        exact ⟨.tail _ (ih.mp m).1, (ih.mp m).2⟩
      · intro ⟨m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq => exact (h (eq ▸ hit)).elim
        | inr tail => exact ih.mpr ⟨tail, hit⟩

public theorem List.mem_filterMap : type_of% @_root_.List.mem_filterMap := by
  intro α β f xs b
  induction xs with
  | nil => exact ⟨fun m => (List.not_mem_nil m).elim, fun ⟨_, m, _⟩ => (List.not_mem_nil m).elim⟩
  | cons a xs ih =>
    cases h : f a with
    | none =>
      rw [List.filterMap_cons_none h]
      constructor
      · intro m
        obtain ⟨x, t, hit⟩ := ih.mp m
        exact ⟨x, .tail _ t, hit⟩
      · intro ⟨x, m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq =>
          cases eq
          cases h.symm.trans hit
        | inr tail => exact ih.mpr ⟨x, tail, hit⟩
    | some v =>
      rw [List.filterMap_cons_some h]
      constructor
      · intro m
        cases List.mem_cons.mp m with
        | inl eq => exact ⟨a, .head _, eq.symm ▸ h⟩
        | inr tail =>
          obtain ⟨x, t, hit⟩ := ih.mp tail
          exact ⟨x, .tail _ t, hit⟩
      · intro ⟨x, m, hit⟩
        cases List.mem_cons.mp m with
        | inl eq =>
          cases eq
          exact List.mem_cons.mpr (.inl (Option.some.inj (hit.symm.trans h)))
        | inr tail => exact .tail _ (ih.mpr ⟨x, tail, hit⟩)

public theorem List.head_eq_iff_head?_eq_some : type_of% @_root_.List.head_eq_iff_head?_eq_some := by
  intro α a xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons _ _ => exact ⟨congrArg some, Option.some.inj⟩

public theorem List.filter_reverse : type_of% @_root_.List.filter_reverse := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.reverse_cons, List.filter_append, ih]
    by_cases h : p a = true
    · rw [List.filter_cons_of_pos h, List.filter_cons_of_pos h, List.reverse_cons]
      rfl
    · rw [List.filter_cons_of_neg h, List.filter_cons_of_neg h]
      exact List.append_nil _

public theorem List.filterMap_filterMap : type_of% @_root_.List.filterMap_filterMap := by
  intro α β γ f g xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases fa : f a with
    | none =>
      have rhs : (f a).bind g = none := (congrArg (Option.bind · g) fa)
      rw [List.filterMap_cons_none fa, List.filterMap_cons_none (f := fun x => (f x).bind g) rhs]
      exact ih
    | some b =>
      have bind : (f a).bind g = g b := congrArg (Option.bind · g) fa
      cases gb : g b with
      | none =>
        rw [List.filterMap_cons_some fa, List.filterMap_cons_none gb, List.filterMap_cons_none (f := fun x => (f x).bind g) (bind.trans gb)]
        exact ih
      | some c =>
        rw [List.filterMap_cons_some fa, List.filterMap_cons_some gb, List.filterMap_cons_some (f := fun x => (f x).bind g) (bind.trans gb)]
        exact congrArg (c :: ·) ih

end OmegaChecks.InitPort.Alternatives

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

end OmegaChecks.InitPort.Alternatives

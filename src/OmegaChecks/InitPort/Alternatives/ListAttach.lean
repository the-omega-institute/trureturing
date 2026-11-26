module
public import Init.Data.List.Attach

/-! Equality of dependent list maps follows by comparing their values at each index. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.attach_congr : type_of% @_root_.List.attach_congr := by
  intro α xs ys eq
  subst ys
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_map]
  · intros
    rw [_root_.List.getElem_map]

public theorem List.attachWith_eq_map_attach : type_of% @_root_.List.attachWith_eq_map_attach := by
  intros
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_map, _root_.List.length_attachWith, _root_.List.length_attach]
  · intros
    rw [_root_.List.getElem_map, _root_.List.getElem_attach, _root_.List.getElem_attachWith]

public theorem List.map_attachWith : type_of% @_root_.List.map_attachWith := by
  intros
  rw [List.attachWith_eq_map_attach, _root_.List.map_map]
  rfl

public theorem List.mem_attachWith : type_of% @_root_.List.mem_attachWith := by
  intro α xs p H x
  change x ∈ xs.pmap Subtype.mk _ ↔ x.val ∈ xs
  constructor
  · intro h
    obtain ⟨a, ha, eq⟩ := _root_.List.mem_pmap.mp h
    exact (congrArg Subtype.val eq) ▸ ha
  · intro h
    exact _root_.List.mem_pmap_of_mem h

private theorem depValue {p : α → Prop} (f : (a : α) → p a → β) {a b : α}
    (eq : a = b) {ha : p a} {hb : p b} : f a ha = f b hb := by cases eq; rfl

public theorem List.pmap_attach {α : Type u} {β : Type v} {l : _root_.List α} {p : {x // x ∈ l} → Prop}
    {f : ∀ a, p a → β} (H : ∀ x ∈ l.attach, p x) :
    l.attach.pmap f H = l.pmap (P := fun a => ∃ h : a ∈ l, p ⟨a, h⟩)
      (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨h, H ⟨a,h⟩ (_root_.List.mem_attach ..)⟩) := by
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_pmap, _root_.List.length_pmap, _root_.List.length_attach]
  · intros
    rw [_root_.List.getElem_pmap, _root_.List.getElem_pmap]
    exact depValue f (_root_.List.getElem_attach _)

public theorem List.pmap_attachWith {α : Type u} {β : Type v} {q : α → Prop} {l : _root_.List α}
    {p : {x // q x} → Prop} {f : ∀ a, p a → β} (H₁ : ∀ a ∈ l, q a) (H₂ : ∀ a ∈ l.attachWith q H₁, p a) :
    (l.attachWith q H₁).pmap f H₂ = l.pmap (P := fun a => ∃ h : q a, p ⟨a, h⟩)
      (fun a h => f ⟨a, h.1⟩ h.2) (fun a h => ⟨H₁ a h, H₂ _ ((List.mem_attachWith H₁ _).mpr h)⟩) := by
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_pmap, _root_.List.length_pmap, _root_.List.length_attachWith]
  · intros
    rw [_root_.List.getElem_pmap, _root_.List.getElem_pmap]
    exact depValue f (_root_.List.getElem_attachWith _)

public theorem List.pmap_reverse : type_of% @_root_.List.pmap_reverse := by
  intros
  apply _root_.List.ext_getElem
  · simp only [_root_.List.length_pmap, _root_.List.length_reverse]
  · intros
    simp only [_root_.List.getElem_pmap, _root_.List.getElem_reverse, _root_.List.length_pmap]

public theorem List.filterMap_subtype : type_of% @_root_.List.filterMap_subtype := by
  intro α β p xs f g step
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change _ = (a.val :: xs.unattach).filterMap g
    rw [_root_.List.filterMap_cons, _root_.List.filterMap_cons, step a.val a.property]
    cases g a.val <;> simp only [ih]

public theorem List.flatMap_subtype : type_of% @_root_.List.flatMap_subtype := by
  intro α β p xs f g step
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change f a ++ xs.flatMap f = g a.val ++ xs.unattach.flatMap g
    rw [step a.val a.property, ih]

public theorem List.findSome?_subtype : type_of% @_root_.List.findSome?_subtype := by
  intro α β p xs f g step
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change _ = (a.val :: xs.unattach).findSome? g
    rw [_root_.List.findSome?_cons, _root_.List.findSome?_cons, step a.val a.property, ih]

public theorem List.find?_subtype : type_of% @_root_.List.find?_subtype := by
  intro α p xs f g step
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change _ = (a.val :: xs.unattach).find? g
    simp only [_root_.List.find?_cons, step a.val a.property]
    cases g a.val <;> first | rfl | exact ih

public theorem List.filterMap_unattach : type_of% @_root_.List.filterMap_unattach := by
  intros
  exact (List.filterMap_subtype (fun _ _ => rfl)).symm

public theorem List.flatMap_unattach : type_of% @_root_.List.flatMap_unattach := by
  intros
  exact (List.flatMap_subtype (fun _ _ => rfl)).symm

end OmegaChecks.InitPort.Alternatives

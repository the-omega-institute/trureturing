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

public theorem List.filterMap_attachWith : type_of% @_root_.List.filterMap_attachWith := by
  intros
  rw [List.attachWith_eq_map_attach, _root_.List.filterMap_map]
  rfl

public theorem List.filter_attachWith : type_of% @_root_.List.filter_attachWith := by
  intros
  rw [List.attachWith_eq_map_attach, _root_.List.filter_map]
  rfl

private theorem countValues {p : α → Prop} (xs : _root_.List α) (H : ∀ x ∈ xs, p x)
    (f : α → Bool) : (xs.attachWith p H).countP (fun a => f a.val) = xs.countP f := by
  exact (_root_.List.countP_map (f := Subtype.val) (p := f) (l := xs.attachWith p H)).symm.trans
    (congrArg (_root_.List.countP f) (_root_.List.attachWith_map_subtype_val H))

public theorem List.countP_attach : type_of% @_root_.List.countP_attach := by
  intros
  apply countValues

public theorem List.countP_attachWith : type_of% @_root_.List.countP_attachWith := by
  intros
  apply countValues

public theorem List.count_attach : type_of% @_root_.List.count_attach := by
  intro α inst xs a
  exact (_root_.List.countP_congr (fun x _ => by cases x; cases a; rfl)).trans
    (countValues xs (p := fun x => x ∈ xs) (fun _ h => h) (fun x => x == a.val))

public theorem List.count_attachWith : type_of% @_root_.List.count_attachWith := by
  intro α inst p xs H a
  exact (_root_.List.countP_congr (fun x _ => by cases x; cases a; rfl)).trans
    (countValues xs H (fun x => x == a.val))

public theorem List.unattach_flatten : type_of% @_root_.List.unattach_flatten := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (a ++ as.flatten).map Subtype.val = a.unattach ++ (as.map _root_.List.unattach).flatten
    exact (_root_.List.map_append ..).trans (congrArg (a.unattach ++ ·) ih)

private theorem pbindAtSome {p : α → Prop} {o : Option α} {a : α}
    (eq : o = some a) (H : ∀ x, o = some x → p x) :
    o.pbind (fun x e => some (⟨x, H x e⟩ : Subtype p)) = some ⟨a, H a eq⟩ := by
  cases eq
  rfl

public theorem List.getLast?_attachWith : type_of% @_root_.List.getLast?_attachWith := by
  intro α p xs H
  cases xs with
  | nil => rfl
  | cons a as =>
    let h : (a :: as).attachWith p H ≠ [] := by intros h; cases h
    have left := (_root_.List.getLast?_eq_some_getLast h)
    have right := (_root_.List.getLast?_eq_some_getLast (l := a :: as) (by intros h; cases h))
    rw [left, _root_.List.getLast_attachWith]
    exact (pbindAtSome right (fun x e => H x (_root_.List.mem_of_getLast? e))).symm

public theorem List.getLast?_attach : type_of% @_root_.List.getLast?_attach := by
  intro α xs
  exact List.getLast?_attachWith

public theorem List.map_inj_right : type_of% @_root_.List.map_inj_right := by
  intro α β l l' f injective
  constructor
  · intro eq
    apply _root_.List.ext_getElem
    · have len := congrArg _root_.List.length eq
      simpa only [_root_.List.length_map] using len
    · intro i hi hj
      apply injective
      have value := congrArg (fun xs => xs[i]?) eq
      rw [_root_.List.getElem?_eq_getElem (show i < (l.map f).length by rw [_root_.List.length_map]; exact hi),
        _root_.List.getElem?_eq_getElem (show i < (l'.map f).length by rw [_root_.List.length_map]; exact hj),
        _root_.List.getElem_map, _root_.List.getElem_map] at value
      exact Option.some.inj value
  · intro eq
    exact congrArg (_root_.List.map f) eq

public theorem List.map_filterMap : type_of% @_root_.List.map_filterMap := by
  intro α β γ f g xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [_root_.List.filterMap_cons, _root_.List.filterMap_cons]
    cases f a <;> simp only [Option.map, _root_.List.map_cons, ih]

private theorem filterMapValues {p : α → Prop} {f : α → Option β} {g : Subtype p → Option β}
    (xs : List (Subtype p)) (step : ∀ x, g x = f x.val) :
    xs.filterMap g = (xs.map Subtype.val).filterMap f :=
  List.filterMap_subtype (fun x h => step ⟨x,h⟩)

private theorem valueOfPbind {p : β → Prop} (o : Option β) (h : ∀ x, o = some x → p x) :
    (o.pbind (fun x e => some (⟨x, h x e⟩ : Subtype p))).map Subtype.val = o := by
  cases o <;> rfl

public theorem List.attach_filterMap : type_of% @_root_.List.attach_filterMap := by
  intro α β xs f
  apply (List.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [_root_.List.attach_map_subtype_val, List.map_filterMap]
  apply Eq.symm
  apply Eq.trans (filterMapValues xs.attach (f := f) _)
  · rw [_root_.List.attach_map_subtype_val]
  · intro x
    exact valueOfPbind _ _

private theorem projectFilter (p : α → Bool) (xs : List α) {q : α → Prop}
    (g : Subtype q → Option α) (H : ∀ x, g x = if p x.val then some x.val else none)
    (ys : List (Subtype q)) (eq : ys.map Subtype.val = xs) : ys.filterMap g = xs.filter p := by
  have via := filterMapValues (f := fun x => if p x then some x else none) ys H
  rw [eq] at via
  apply via.trans
  clear via eq
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [_root_.List.filterMap_cons, _root_.List.filter_cons]
    cases p a <;> simp only [Bool.false_eq_true, ite_false, ite_true, ih]

public theorem List.attach_filter : type_of% @_root_.List.attach_filter := by
  intro α xs p
  apply (List.map_inj_right (f := Subtype.val) (fun _ _ => Subtype.ext)).mp
  rw [_root_.List.attach_map_subtype_val, List.map_filterMap]
  apply Eq.symm
  apply projectFilter p xs _ _ xs.attach (_root_.List.attach_map_subtype_val xs)
  intro x
  by_cases h : p x.val = true
  · rw [dite_eq_left h, ite_eq_left h]
    rfl
  · rw [dite_eq_right h, ite_eq_right h]
    rfl

end OmegaChecks.InitPort.Alternatives

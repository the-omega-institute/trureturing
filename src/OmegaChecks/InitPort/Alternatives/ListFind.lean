module
public import Init.Data.List.Find
import Init.Data.List.Impl

/-! Constructive witnesses for the first successful element and its index. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.findSome?_eq_some_iff : type_of% @_root_.List.findSome?_eq_some_iff := by
  intro α β f xs b
  constructor
  · induction xs with
    | nil => intro h; cases h
    | cons x xs ih =>
      intro h
      rw [_root_.List.findSome?_cons] at h
      cases fx : f x with
      | some c =>
        rw [fx] at h
        exact ⟨[], x, xs, rfl, fx.trans h, fun _ m => nomatch m⟩
      | none =>
        rw [fx] at h
        obtain ⟨pre, a, post, rfl, hit, missing⟩ := ih h
        refine ⟨x :: pre, a, post, rfl, hit, ?_⟩
        intro y mem
        cases mem with
        | head => exact fx
        | tail _ hy => exact missing y hy
  · rintro ⟨pre, a, post, rfl, hit, missing⟩
    rw [_root_.List.findSome?_append, _root_.List.findSome?_eq_none_iff.mpr missing,
      _root_.List.findSome?_cons, hit]
    rfl

public theorem List.isSome_findSome? : type_of% @_root_.List.isSome_findSome? := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.List.findSome?_isSome_iff.trans _root_.List.any_eq_true.symm)

public theorem List.isSome_find? : type_of% @_root_.List.isSome_find? := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.List.find?_isSome.trans _root_.List.any_eq_true.symm)

public theorem List.findIdx_lt_length : type_of% @_root_.List.findIdx_lt_length := by
  intro α p xs
  exact ⟨fun h => ⟨xs[xs.findIdx p], _root_.List.getElem_mem h, _root_.List.findIdx_getElem⟩,
    _root_.List.findIdx_lt_length_of_exists⟩

public theorem List.findIdx_le_findIdx : type_of% @_root_.List.findIdx_le_findIdx := by
  intro α xs p q h
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    rw [_root_.List.findIdx_cons, _root_.List.findIdx_cons]
    by_cases hit : q x
    · rw [ite_eq_left hit]; exact Nat.zero_le _
    · rw [ite_eq_right hit, ite_eq_right (fun hp => hit (h x (.head _) hp))]
      exact Nat.succ_le_succ (ih (fun y mem => h y (.tail _ mem)))

public theorem List.of_findIdx?_eq_some : type_of% @_root_.List.of_findIdx?_eq_some := by
  intro α i xs p eq
  obtain ⟨bound, hit, _⟩ := _root_.List.findIdx?_eq_some_iff_getElem.mp eq
  rw [getElem?_pos xs i bound]
  exact hit

public theorem List.of_findIdx?_eq_none : type_of% @_root_.List.of_findIdx?_eq_none := by
  intro α xs p eq i
  cases atIndex : xs[i]? with
  | none => rfl
  | some x =>
    exact Bool.eq_false_iff.mp (_root_.List.findIdx?_eq_none_iff.mp eq x
      (_root_.List.mem_iff_getElem?.mpr ⟨i, atIndex⟩))

public theorem List.idxOf_eq_length : type_of% @_root_.List.idxOf_eq_length := by
  intro α a _ _ xs absent
  apply _root_.List.findIdx_eq_length.mpr
  exact fun x mem => Bool.eq_false_iff.mpr (fun eq => absent ((eq_of_beq eq : x = a) ▸ mem))

public theorem List.idxOf_lt_length_iff : type_of% @_root_.List.idxOf_lt_length_iff := by
  intro α _ _ xs a
  exact ⟨fun h => _root_.List.getElem_idxOf h ▸ _root_.List.getElem_mem h,
    _root_.List.idxOf_lt_length_of_mem⟩

public theorem List.idxOf?_eq_none_iff : type_of% @_root_.List.idxOf?_eq_none_iff := by
  intro α _ _ xs a
  constructor
  · intro eq mem
    have no := _root_.List.findIdx?_eq_none_iff.mp eq a mem
    exact Bool.noConfusion (no.symm.trans (BEq.rfl (a := a)))
  · intro absent
    exact _root_.List.findIdx?_eq_none_iff.mpr fun x mem =>
      Bool.eq_false_iff.mpr (fun eq => absent ((eq_of_beq eq : x = a) ▸ mem))

public theorem List.find?_replicate_eq_some_iff : type_of% @_root_.List.find?_replicate_eq_some_iff := by
  intro α n a b p
  cases n with
  | zero => exact ⟨fun h => (nomatch h), fun ⟨ne, _⟩ => (ne rfl).elim⟩
  | succ n =>
    rw [List.find?_replicate_of_length_pos (Nat.zero_lt_succ n)]
    cases h : p a with
    | true => exact ⟨fun eq => ⟨Nat.succ_ne_zero n, rfl, Option.some.inj eq⟩, fun ands => congrArg some ands.2.2⟩
    | false => exact ⟨fun h => (nomatch h), fun ands => Bool.noConfusion ands.2.1⟩

public theorem List.find?_replicate_eq_none_iff : type_of% @_root_.List.find?_replicate_eq_none_iff := by
  intro α n a p
  cases n with
  | zero => exact ⟨fun _ => .inl rfl, fun _ => rfl⟩
  | succ n =>
    rw [List.find?_replicate_of_length_pos (Nat.zero_lt_succ n)]
    cases h : p a with
    | false => exact ⟨fun _ => .inr rfl, fun _ => rfl⟩
    | true => exact ⟨fun h => (nomatch h), fun h => h.elim (fun eq => (Nat.succ_ne_zero n eq).elim) Bool.noConfusion⟩

public theorem List.find?_filter : type_of% @_root_.List.find?_filter := by
  intro α xs p q
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.filter_cons, List.find?_cons]
    cases hp : p a <;> cases hq : q a <;> simp only [hq, ite_true, Bool.false_eq_true, ite_false, List.find?_cons, ih] <;> first | rfl | exact ih

public theorem List.findIdx_subtype : type_of% @_root_.List.findIdx_subtype := by
  intro α pred xs f g agrees
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx_cons]
    change _ = (x.val :: xs.unattach).findIdx g
    rw [List.findIdx_cons, agrees x.val x.property]
    cases g x.val <;> first | rfl | exact congrArg Nat.succ ih

public theorem List.findIdx?_subtype : type_of% @_root_.List.findIdx?_subtype := by
  intro α pred xs f g agrees
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx?_cons]
    change _ = (x.val :: xs.unattach).findIdx? g
    rw [List.findIdx?_cons, agrees x.val x.property]
    cases g x.val <;> first | rfl | exact congrArg (Option.map Nat.succ) ih

public theorem List.findIdx?_eq_bind_find?_idxOf? : type_of% @_root_.List.findIdx?_eq_bind_find?_idxOf? := by
  intro α _ _ xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.findIdx?_cons, List.find?_cons]
    cases hit : p x with
    | true =>
      change some 0 = (x :: xs).idxOf? x
      rw [List.idxOf?_cons, beq_self_eq_true]
      rfl
    | false =>
      change (xs.findIdx? p).map Nat.succ = (xs.find? p).bind _
      rw [ih]
      cases found : xs.find? p with
      | none => rfl
      | some y =>
        change ((xs.idxOf? y).map Nat.succ) = (x :: xs).idxOf? y
        have neq : ¬ (x == y) := fun eq =>
          Bool.noConfusion (hit.symm.trans ((eq_of_beq eq) ▸ List.find?_some found))
        rw [List.idxOf?_cons, ite_eq_right neq]

private theorem sameFinOption {i j : Option (Fin n)} (eq : i.map Fin.val = j.map Fin.val) : i = j := by
  cases i <;> cases j
  · rfl
  · cases eq
  · cases eq
  · exact congrArg some (Fin.ext (Option.some.inj eq))

public theorem List.findFinIdx?_eq_bind_find?_finIdxOf? : type_of% @_root_.List.findFinIdx?_eq_bind_find?_finIdxOf? := by
  intro α _ _ xs p
  apply sameFinOption
  rw [← List.findIdx?_eq_map_findFinIdx?_val, _root_.List.findIdx?_eq_bind_find?_idxOf?]
  cases xs.find? p with
  | none => rfl
  | some a => exact _root_.List.idxOf?_eq_map_finIdxOf?_val

public theorem List.head_filterMap._proof_2 : type_of% (private_decl% @_root_.List.head_filterMap._proof_2) := by
  intros
  exact Option.isSome_of_eq_some (_root_.List.head?_filterMap.symm.trans (_root_.List.head?_eq_some_head ‹_›))

public theorem List.head_filterMap : type_of% @_root_.List.head_filterMap := by
  intros
  exact Option.some.inj ((_root_.List.head?_eq_some_head ‹_›).symm.trans
    (_root_.List.head?_filterMap.trans (Option.some_get _).symm))

public theorem List.head_filter._proof_1 : type_of% (private_decl% @_root_.List.head_filter._proof_1) := by
  intros
  exact Option.isSome_of_eq_some (_root_.List.head?_filter.symm.trans (_root_.List.head?_eq_some_head ‹_›))

public theorem List.head_filter : type_of% @_root_.List.head_filter := by
  intros
  exact Option.some.inj ((_root_.List.head?_eq_some_head ‹_›).symm.trans
    (_root_.List.head?_filter.trans (Option.some_get _).symm))

public theorem List.getLast_filter._proof_1 : type_of% (private_decl% @_root_.List.getLast_filter._proof_1) := by
  intros
  exact Option.isSome_of_eq_some (_root_.List.getLast?_filter.symm.trans (_root_.List.getLast?_eq_some_getLast ‹_›))

public theorem List.getLast_filter : type_of% @_root_.List.getLast_filter := by
  intros
  exact Option.some.inj ((_root_.List.getLast?_eq_some_getLast ‹_›).symm.trans
    (_root_.List.getLast?_filter.trans (Option.some_get _).symm))


end OmegaChecks.InitPort.Alternatives

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

end OmegaChecks.InitPort.Alternatives

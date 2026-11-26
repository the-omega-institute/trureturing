module
public import Init.Data.Vector.Perm
public import Init.Data.Array.Lemmas

/-! Splitting an array append reduces to splitting its underlying list at the same position. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem Array.append_eq_append_iff_of_size_eq_left :
    type_of% @_root_.Array.append_eq_append_iff_of_size_eq_left := by
  intro α ws xs ys zs h
  exact ⟨fun eq => _root_.Array.append_inj eq h, fun ⟨e, e'⟩ => e ▸ e' ▸ rfl⟩

public theorem Array.append_eq_append_iff_of_size_eq_right :
    type_of% @_root_.Array.append_eq_append_iff_of_size_eq_right := by
  intro α ws xs ys zs h
  exact ⟨fun eq => _root_.Array.append_inj' eq h, fun ⟨e, e'⟩ => e ▸ e' ▸ rfl⟩

private theorem toListAppend {a b c : Array α} (h : a.toList = b.toList ++ c.toList) :
    a = b ++ c := _root_.Array.ext' (h.trans _root_.Array.toList_append.symm)

public theorem Array.append_eq_append_iff : type_of% @_root_.Array.append_eq_append_iff := by
  intro α ws xs ys zs
  constructor
  · intro eq
    have underlying := congrArg _root_.Array.toList eq
    rw [_root_.Array.toList_append, _root_.Array.toList_append] at underlying
    obtain (⟨as, left, right⟩ | ⟨cs, left, right⟩) := _root_.List.append_eq_append_iff.mp underlying
    · exact .inl ⟨as.toArray, toListAppend left, toListAppend right⟩
    · exact .inr ⟨cs.toArray, toListAppend left, toListAppend right⟩
  · rintro (⟨as, rfl, rfl⟩ | ⟨cs, rfl, rfl⟩)
    · exact _root_.Array.append_assoc.symm
    · exact _root_.Array.append_assoc

public theorem Array.append_eq_push_iff : type_of% @_root_.Array.append_eq_push_iff := by
  intro α xs ys zs x
  constructor
  · intro eq
    by_cases h : ys.size = 0
    · have empty := _root_.Array.eq_empty_of_size_eq_zero h
      cases empty
      exact .inl ⟨rfl, (_root_.Array.append_empty).symm.trans eq⟩
    · obtain ⟨bs, a, rfl⟩ := _root_.Array.exists_push_of_size_pos (Nat.zero_lt_of_ne_zero h)
      rw [← _root_.Array.push_append] at eq
      obtain ⟨rfl, rest⟩ := _root_.Array.push_eq_push.mp eq
      exact .inr ⟨bs, rfl, rest.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨as, rfl, rfl⟩)
    · exact _root_.Array.append_empty
    · exact _root_.Array.push_append.symm

public theorem Array.getElem?_eq_none_iff : type_of% @_root_.Array.getElem?_eq_none_iff := by
  intro α i xs
  constructor
  · intro eq
    apply Nat.le_of_not_gt
    intro inside
    exact Option.some_ne_none _ ((getElem?_pos xs i inside).symm.trans eq)
  · intro h
    exact getElem?_neg xs i (Nat.not_lt_of_ge h)

public theorem Array.getElem?_push : type_of% @_root_.Array.getElem?_push := by
  intro α i xs x
  by_cases atEnd : i = xs.size
  · cases atEnd
    rw [ite_eq_left rfl, getElem?_pos (xs.push x) xs.size (by rw [_root_.Array.size_push]; exact Nat.lt_succ_self _),
      _root_.Array.getElem_push_eq]
  · rw [ite_eq_right atEnd]
    by_cases before : i < xs.size
    · rw [getElem?_pos xs i before, getElem?_pos (xs.push x) i
        (by rw [_root_.Array.size_push]; exact Nat.lt_succ_of_lt before), _root_.Array.getElem_push_lt before]
    · have after := Nat.lt_of_le_of_ne (Nat.le_of_not_gt before) (Ne.symm atEnd)
      rw [getElem?_neg xs i before, getElem?_neg (xs.push x) i
        (by rw [_root_.Array.size_push]; exact Nat.not_lt_of_ge after)]

public theorem Array.back?_eq_none_iff : type_of% @_root_.Array.back?_eq_none_iff := by
  intro α xs
  constructor
  · intro empty
    by_cases h : xs.size = 0
    · exact _root_.Array.eq_empty_of_size_eq_zero h
    · obtain ⟨as, a, rfl⟩ := _root_.Array.exists_push_of_size_pos (Nat.zero_lt_of_ne_zero h)
      rw [_root_.Array.back?_push] at empty
      exact (Option.some_ne_none _ empty).elim
  · rintro rfl
    rfl

public theorem Array.back_append_right : type_of% @_root_.Array.back_append_right := by
  intros
  exact _root_.Array.back_append_of_size_pos ‹_›

private theorem backCongr {a b : Array α} (eq : a = b) (ha : 0 < a.size) (hb : 0 < b.size) :
    a.back ha = b.back hb := by cases eq; rfl

public theorem Array.back_append_left : type_of% @_root_.Array.back_append_left := by
  intro α xs ys w h
  cases _root_.Array.eq_empty_of_size_eq_zero h
  exact backCongr _root_.Array.append_empty _ _

public theorem Array.back_append : type_of% @_root_.Array.back_append := by
  intro α ys xs h
  by_cases empty : ys.isEmpty
  · rw [dite_eq_left empty]
    exact Array.back_append_left h (_root_.Array.isEmpty_iff_size_eq_zero.mp empty)
  · rw [dite_eq_right empty]
    exact Array.back_append_right (Nat.zero_lt_of_ne_zero (fun e => empty (_root_.Array.isEmpty_iff_size_eq_zero.mpr e)))

public theorem Array.Perm.push : type_of% @_root_.Array.Perm.push := by
  intro α x xs ys h
  apply Array.Perm.of_toList_perm
  rw [Array.toList_push, Array.toList_push]
  exact h.toList.append List.Perm.rfl

public theorem Vector.Perm.push : type_of% @_root_.Vector.Perm.push := by
  intro α n x xs ys h
  exact Vector.Perm.of_toArray_perm (_root_.Array.Perm.push x h.toArray)

end OmegaChecks.InitPort.Alternatives

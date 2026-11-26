module
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

end OmegaChecks.InitPort.Alternatives

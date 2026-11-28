module
import all Init.Data.Array.Basic
import all Init.Data.Array.Lemmas

/-! The two endpoints of the official swapping loop remain symmetric in the original list. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem swappedAt {α : Type u} (xs : _root_.Array α) (i j k : Nat)
    (hi : i < xs.size) (hj : j < xs.size) :
    (xs.swap i j hi hj).toList[k]? =
      if j = k then xs.toList[i]? else if i = k then xs.toList[j]? else xs.toList[k]? := by
  rw [_root_.Array.getElem?_toList, _root_.Array.getElem?_swap]
  by_cases eq : j = k
  · rw [ite_eq_left eq, ite_eq_left eq]
    exact ((_root_.Array.getElem?_toList).trans (_root_.Array.getElem?_eq_getElem hi)).symm
  · rw [ite_eq_right eq, ite_eq_right eq]
    by_cases eq : i = k
    · rw [ite_eq_left eq, ite_eq_left eq]
      exact ((_root_.Array.getElem?_toList).trans (_root_.Array.getElem?_eq_getElem hj)).symm
    · rw [ite_eq_right eq, ite_eq_right eq]
      exact _root_.Array.getElem?_toList.symm

private theorem reverseAt {α : Type u} (orig : List α) (j : Nat) (xs : _root_.Array α) (i : Nat)
    (hj : j < xs.size) (mirror : i + j + 1 = orig.length)
    (middle : ∀ k, i ≤ k → k ≤ j → xs.toList[k]? = orig[k]?)
    (outside : ∀ k, (k < i ∨ j < k) → xs.toList[k]? = orig.reverse[k]?)
    (k : Nat) : (_root_.Array.reverse.loop xs i ⟨j, hj⟩).toList[k]? = orig.reverse[k]? := by
  induction j generalizing xs i with
  | zero =>
    rw [_root_.Array.reverse.loop.eq_def, dite_eq_right (Nat.not_lt_zero _)]
    by_cases left : k < i
    · exact outside k (.inl left)
    · by_cases right : 0 < k
      · exact outside k (.inr right)
      · have ke : k = 0 := Nat.eq_zero_of_not_pos right
        have ie : i = k := Nat.le_antisymm (Nat.ge_of_not_lt left) (ke ▸ Nat.zero_le _)
        cases ie
        cases ke
        exact (middle 0 (Nat.le_refl _) (Nat.le_refl _)).trans (List.getElem?_reverse' mirror).symm
  | succ j ih =>
    rw [_root_.Array.reverse.loop.eq_def]
    by_cases move : i < j + 1
    · rw [dite_eq_left move]
      let next := xs.swap i (j+1) (Nat.lt_trans move hj) hj
      have nextJ : j < next.size := by rw [_root_.Array.size_swap]; exact Nat.lt_trans (Nat.lt_succ_self _) hj
      have symmMirror : j + 1 + i + 1 = orig.length :=
        (congrArg (· + 1) (Nat.add_comm (j + 1) i)).trans mirror
      have newMirror : i + 1 + j + 1 = orig.length :=
        (congrArg (· + 1) (Nat.succ_add i j)).trans mirror
      apply ih next (i+1) nextJ newMirror
      · intro t lo hi
        have neJ : j+1 ≠ t := Nat.ne_of_gt (Nat.lt_of_le_of_lt hi (Nat.lt_succ_self _))
        have neI : i ≠ t := Nat.ne_of_lt lo
        exact ((swappedAt xs i (j+1) t _ _).trans
          ((ite_eq_right neJ).trans (ite_eq_right neI))).trans
          (middle t (Nat.le_trans (Nat.le_succ _) lo) (Nat.le_trans hi (Nat.le_succ _)))
      · intro t endpt
        have atT := swappedAt xs i (j+1) t (Nat.lt_trans move hj) hj
        by_cases right : j+1 = t
        · cases right
          exact (atT.trans (ite_eq_left rfl)).trans
            ((middle i (Nat.le_refl _) (Nat.le_of_lt move)).trans (List.getElem?_reverse' symmMirror).symm)
        · by_cases left : i = t
          · cases left
            exact (atT.trans ((ite_eq_right right).trans (ite_eq_left rfl))).trans
              ((middle (j+1) (Nat.le_of_lt move) (Nat.le_refl _)).trans (List.getElem?_reverse' mirror).symm)
          · apply (atT.trans ((ite_eq_right right).trans (ite_eq_right left))).trans
            apply outside
            cases endpt with
            | inl h => exact .inl (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) (Ne.symm left))
            | inr h => exact .inr (Nat.lt_of_le_of_ne h right)
    · rw [dite_eq_right move]
      by_cases low : k < i
      · exact outside k (.inl low)
      · by_cases high : j+1 < k
        · exact outside k (.inr high)
        · have ki := Nat.ge_of_not_lt low
          have kj := Nat.ge_of_not_lt high
          have ie := Nat.le_antisymm (Nat.le_trans ki kj) (Nat.ge_of_not_lt move)
          have ke := Nat.le_antisymm kj (Nat.le_trans (Nat.ge_of_not_lt move) ki)
          cases ke
          subst i
          exact (middle _ (Nat.le_refl _) (Nat.le_refl _)).trans (List.getElem?_reverse' mirror).symm

public theorem Array.toList_reverse.go : type_of% (private_decl% @_root_.Array.toList_reverse.go) := by
  intro α xs as i j hj mirror _ slot k
  apply reverseAt xs.toList j as i hj mirror _ _ k
  · intro pos lo hi
    exact (slot pos).trans (ite_eq_left ⟨lo, hi⟩)
  · intro pos out
    apply (slot pos).trans (ite_eq_right _)
    intro inside
    cases out with
    | inl lo => exact Nat.not_le_of_lt lo inside.1
    | inr hi => exact Nat.not_le_of_lt hi inside.2

public theorem Array.toList_reverse.go._unary :
    type_of% (private_decl% @_root_.Array.toList_reverse.go._unary) := by
  intro α xs state
  obtain ⟨as, i, j, bound, mirror, size, slot, k⟩ := state
  exact Array.toList_reverse.go as i j bound mirror size slot k

public theorem Array.toList_reverse : type_of% @_root_.Array.toList_reverse := by
  intro α xs
  unfold _root_.Array.reverse
  by_cases small : xs.size ≤ 1
  · rw [dite_eq_left small]
    rcases xs with ⟨_ | ⟨a, _ | ⟨b, rest⟩⟩⟩
    · rfl
    · rfl
    · exact (Nat.not_succ_le_zero _ (Nat.le_of_succ_le_succ small)).elim
  · rw [dite_eq_right small]
    have pos : 1 ≤ xs.size := Nat.le_of_lt (Nat.lt_of_not_ge small)
    have len := Nat.sub_add_cancel pos
    apply List.ext_getElem?
    intro k
    apply reverseAt xs.toList (xs.size-1) xs 0 _ ((congrArg (· + 1) (Nat.zero_add _)).trans len)
    · exact fun _ _ _ => rfl
    · intro t out
      cases out with
      | inl h => exact (Nat.not_lt_zero _ h).elim
      | inr h =>
        have past : xs.toList.length ≤ t := Eq.subst (motive := (· ≤ t)) len h
        exact (List.getElem?_eq_none past).trans
          (List.getElem?_eq_none (Eq.subst (motive := (· ≤ t)) List.length_reverse.symm past)).symm

public theorem Array.size_reverse : type_of% @_root_.Array.size_reverse := by
  intro α xs
  exact (congrArg List.length (_root_.Array.toList_reverse (xs := xs))).trans List.length_reverse

public theorem Array.getElem_reverse._proof_1 :
    type_of% (private_decl% @_root_.Array.getElem_reverse._proof_1) := by
  intro α xs i h impossible
  exact impossible (Nat.sub_one_sub_lt_of_lt h)

public theorem Array.getElem_reverse._proof_2 : type_of% @_root_.Array.getElem_reverse._proof_2 := by
  intro α xs i h
  exact Nat.sub_one_sub_lt_of_lt (Eq.subst (motive := (i < ·)) Array.size_reverse h)

public theorem Array.getElem_reverse : type_of% @_root_.Array.getElem_reverse := by
  intro α xs i h
  have hi : i < xs.size := Eq.subst (motive := (i < ·)) Array.size_reverse h
  exact Option.some.inj (((_root_.Array.getElem?_eq_getElem h).symm.trans
    (_root_.Array.getElem?_reverse hi)).trans (_root_.Array.getElem?_eq_getElem (Nat.sub_one_sub_lt_of_lt hi)))

public theorem Array.getElem_swap : type_of% @_root_.Array.getElem_swap := by
  intro α xs i j hi hj k hk
  have shape := (_root_.Array.getElem?_eq_getElem hk).symm.trans (_root_.Array.getElem?_swap hi hj)
  have original : k < xs.size := Eq.subst (motive := (k < ·)) (_root_.Array.size_swap ..) hk
  by_cases il : k = i
  · cases il
    rw [ite_eq_left rfl]
    by_cases same : j = i
    · cases same
      exact Option.some.inj (shape.trans (ite_eq_left rfl))
    · exact Option.some.inj (shape.trans ((ite_eq_right same).trans (ite_eq_left rfl)))
  · rw [ite_eq_right il]
    by_cases jr : k = j
    · cases jr
      rw [ite_eq_left rfl]
      exact Option.some.inj (shape.trans (ite_eq_left rfl))
    · rw [ite_eq_right jr]
      exact Option.some.inj (shape.trans ((ite_eq_right (Ne.symm jr)).trans
        ((ite_eq_right (Ne.symm il)).trans (_root_.Array.getElem?_eq_getElem original))))

public theorem Array.getElem_swap_right : type_of% @_root_.Array.getElem_swap_right := by
  intro α xs i j hi hj
  exact Option.some.inj (((_root_.Array.getElem?_eq_getElem _).symm.trans
    (_root_.Array.getElem?_swap hi hj)).trans (ite_eq_left rfl))

end OmegaChecks.InitPort.Alternatives

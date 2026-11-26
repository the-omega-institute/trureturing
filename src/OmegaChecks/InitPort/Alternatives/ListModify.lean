module
import all Init.Data.List.Nat.Modify
import all Init.Data.List.Basic

/-! Lookup and commutation of finite list updates by structural recursion. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem List.modify_id : type_of% @_root_.List.modify_id := by
  intro α i xs
  induction xs generalizing i with
  | nil => exact _root_.List.modify_nil ..
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

public theorem List.modify_eq_self : type_of% @_root_.List.modify_eq_self := by
  intro α f i xs past
  induction xs generalizing i with
  | nil => exact _root_.List.modify_nil ..
  | cons x xs ih =>
    cases i with
    | zero => exact (Nat.not_succ_le_zero _ past).elim
    | succ i => exact congrArg (x :: ·) (ih (Nat.le_of_succ_le_succ past))

public theorem List.modify_modify_eq : type_of% @_root_.List.modify_modify_eq := by
  intro α f g i xs
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

public theorem List.modify_modify_ne : type_of% @_root_.List.modify_modify_ne := by
  intro α f g i j xs ne
  induction xs generalizing i j with
  | nil => cases i <;> cases j <;> rfl
  | cons x xs ih =>
    cases i <;> cases j
    case zero.zero => exact (ne rfl).elim
    case zero.succ | succ.zero => rfl
    case succ.succ => exact congrArg (x :: ·) (ih (fun eq => ne (congrArg Nat.succ eq)))

public theorem List.modify_eq_set : type_of% @_root_.List.modify_eq_set := by
  intro α _ f i xs
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

public theorem List.getElem?_modify : type_of% @_root_.List.getElem?_modify := by
  intro α f i xs j
  induction xs generalizing i j with
  | nil => cases i <;> cases j <;> rfl
  | cons x xs ih =>
    cases i <;> cases j
    case zero.zero | succ.zero => rfl
    case zero.succ j =>
      change xs[j]? = Option.map _ xs[j]?
      cases xs[j]? <;> rfl
    case succ.succ i j =>
      rw [_root_.List.getElem?_cons_succ]
      refine (ih i j).trans ?_
      cases xs[j]? with
      | none => rfl
      | some y =>
        change some (if i = j then _ else _) = some (if i+1 = j+1 then _ else _)
        by_cases eq : i = j
        · rw [ite_eq_left eq, ite_eq_left (congrArg Nat.succ eq)]
        · rw [ite_eq_right eq, ite_eq_right (fun h => eq (Nat.succ.inj h))]

public theorem List.getElem?_modify_eq : type_of% @_root_.List.getElem?_modify_eq := by
  intro α f i xs
  rw [_root_.List.getElem?_modify]
  cases xs[i]? with
  | none => rfl
  | some y => exact congrArg some (ite_eq_left rfl)

public theorem List.getElem?_modify_ne : type_of% @_root_.List.getElem?_modify_ne := by
  intro α f i j xs ne
  rw [_root_.List.getElem?_modify]
  cases xs[j]? with
  | none => rfl
  | some y => exact congrArg some (ite_eq_right ne)

public theorem List.getElem_modify : type_of% @_root_.List.getElem_modify := by
  intro α f i xs j valid
  have bound : j < xs.length := _root_.List.length_modify f xs i ▸ valid
  apply Option.some.inj
  rw [← _root_.List.getElem?_eq_getElem valid, _root_.List.getElem?_modify,
    _root_.List.getElem?_eq_getElem bound]
  rfl

public theorem List.getElem_modify_eq : type_of% @_root_.List.getElem_modify_eq := by
  intro α f i xs valid
  exact (_root_.List.getElem_modify f i xs i valid).trans (ite_eq_left rfl)

public theorem List.getElem_modify_ne : type_of% @_root_.List.getElem_modify_ne := by
  intro α f i j xs ne valid
  exact (_root_.List.getElem_modify f i xs j valid).trans (ite_eq_right ne)

public theorem List.drop_modify_of_lt : type_of% @_root_.List.drop_modify_of_lt := by
  intro α f i j xs lt
  induction xs generalizing i j with
  | nil => rw [_root_.List.modify_nil]
  | cons x xs ih =>
    cases j with
    | zero => exact (Nat.not_lt_zero _ lt).elim
    | succ j =>
      cases i with
      | zero => rfl
      | succ i => exact ih i j (Nat.lt_of_succ_lt_succ lt)

public theorem List.drop_modify_of_ge : type_of% @_root_.List.drop_modify_of_ge := by
  intro α f i j xs ge
  induction j generalizing i xs with
  | zero => rfl
  | succ j ih =>
    cases i with
    | zero => exact (Nat.not_succ_le_zero _ ge).elim
    | succ i =>
      cases xs with
      | nil => rw [_root_.List.modify_nil, _root_.List.drop_nil, _root_.List.modify_nil]
      | cons x xs =>
        rw [Nat.succ_sub_succ]
        exact ih i xs (Nat.le_of_succ_le_succ ge)

public theorem List.eraseIdx_modify_of_eq : type_of% @_root_.List.eraseIdx_modify_of_eq := by
  intro α f i xs
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih i)

public theorem List.eraseIdx_modify_of_lt : type_of% @_root_.List.eraseIdx_modify_of_lt := by
  intro α f i j xs lt
  induction xs generalizing i j with
  | nil => rw [_root_.List.modify_nil, _root_.List.eraseIdx_nil, _root_.List.modify_nil]
  | cons x xs ih =>
    cases i with
    | zero => exact (Nat.not_lt_zero _ lt).elim
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        cases i with
        | zero => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ lt)).elim
        | succ i => exact congrArg (x :: ·) (ih (i+1) j (Nat.lt_of_succ_lt_succ lt))

public theorem List.eraseIdx_modify_of_gt : type_of% @_root_.List.eraseIdx_modify_of_gt := by
  intro α f i j xs gt
  induction xs generalizing i j with
  | nil => rw [_root_.List.modify_nil, _root_.List.eraseIdx_nil, _root_.List.modify_nil]
  | cons x xs ih =>
    cases j with
    | zero => exact (Nat.not_lt_zero _ gt).elim
    | succ j =>
      cases i with
      | zero => rfl
      | succ i => exact congrArg (x :: ·) (ih i j (Nat.lt_of_succ_lt_succ gt))

public theorem List.modify_eraseIdx_of_lt : type_of% @_root_.List.modify_eraseIdx_of_lt := by
  intro α f i j xs lt
  exact (_root_.List.eraseIdx_modify_of_gt f j i xs lt).symm

public theorem List.modify_eraseIdx_of_ge : type_of% @_root_.List.modify_eraseIdx_of_ge := by
  intro α f i j xs ge
  exact (_root_.List.eraseIdx_modify_of_lt f (j+1) i xs (Nat.lt_succ_of_le ge)).symm

end OmegaChecks.InitPort.Alternatives

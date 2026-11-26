module
public import Init.Data.List.Count

/-! Count elements by induction on a sublist or on the inputs of a traversal. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.Sublist.countP_le : type_of% @_root_.List.Sublist.countP_le := by
  intro α p xs ys sub
  induction sub with
  | slnil => exact Nat.le_refl _
  | cons a _ ih =>
    rw [_root_.List.countP_cons]
    exact Nat.le_trans ih (Nat.le_add_right ..)
  | cons_cons a _ ih =>
    rw [_root_.List.countP_cons, _root_.List.countP_cons]
    exact Nat.add_le_add_right ih _

public theorem List.countP_flatten : type_of% @_root_.List.countP_flatten := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (a ++ as.flatten).countP p = a.countP p + _
    rw [_root_.List.countP_append, ih]
    rfl

public theorem List.countP_flatMap : type_of% @_root_.List.countP_flatMap := by
  intro α β p xs f
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change (f a ++ as.flatMap f).countP p = (f a).countP p + _
    rw [_root_.List.countP_append, ih]
    rfl

public theorem List.count_flatten : type_of% @_root_.List.count_flatten := by
  intros
  apply List.countP_flatten

public theorem List.count_flatMap : type_of% @_root_.List.count_flatMap := by
  intros
  apply List.countP_flatMap

public theorem List.countP_filterMap : type_of% @_root_.List.countP_filterMap := by
  intro α β p f xs
  induction xs with
  | nil => rfl
  | cons a as ih =>
    rw [_root_.List.filterMap_cons, _root_.List.countP_cons]
    cases f a with
    | none => exact ih
    | some b =>
      rw [_root_.List.countP_cons, ih]
      rfl

public theorem List.count_filterMap : type_of% @_root_.List.count_filterMap := by
  intro β α inst b f xs
  rw [_root_.List.count_eq_countP, List.countP_filterMap]
  apply _root_.List.countP_congr
  intro a _
  cases f a <;> rfl

public theorem List.filter_eq : type_of% @_root_.List.filter_eq := by
  intro α inst lawful dec xs a
  apply Eq.trans (_root_.List.filter_congr _)
  · exact _root_.List.filter_beq a
  · intro x _
    exact (Bool.beq_eq_decide_eq x a).symm

end OmegaChecks.InitPort.Alternatives

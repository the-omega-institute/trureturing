module
public import Init.Data.List.SplitOn.Lemmas
import all Init.Data.List.SplitOn.Lemmas
import all Init.Data.List.SplitOn.Basic

/-! Track the reversed prefix of a split and reconstruct the original list from its separators. -/

namespace OmegaChecks.InitPort.Alternatives

@[expose] public noncomputable def List.splitOnPTR {α : Type u} (p : α → Bool) (xs : List α) : List (List α) :=
  _root_.List.splitOnP p xs

public theorem List.splitOnP_eq_splitOnPTR : @_root_.List.splitOnP = @List.splitOnPTR := rfl

public theorem List.splitOnPPrepend_eq_modifyHead : type_of% @_root_.List.splitOnPPrepend_eq_modifyHead := by
  intro α p xs acc
  induction xs generalizing acc with
  | nil => exact congrArg (fun first => [first]) (_root_.List.append_nil acc.reverse).symm
  | cons x xs ih =>
    rw [_root_.List.splitOnP_cons_eq_ite_splitOnPPrepend]
    by_cases sep : p x = true
    · rw [_root_.List.splitOnPPrepend_cons_pos sep, ite_eq_left sep, _root_.List.modifyHead_cons,
        _root_.List.append_nil]
    · rw [_root_.List.splitOnPPrepend_cons_neg (Bool.eq_false_iff.mpr sep), ite_eq_right sep, ih, ih]
      cases xs.splitOnP p with
      | nil => rfl
      | cons head tail =>
        change ((x :: acc).reverse ++ head) :: tail = (acc.reverse ++ x :: head) :: tail
        apply congrArg (· :: tail)
        rw [_root_.List.reverse_cons, _root_.List.append_assoc]
        rfl

public theorem List.splitOnP_cons_eq_ite_modifyHead : type_of% @_root_.List.splitOnP_cons_eq_ite_modifyHead := by
  intro α p x xs
  rw [_root_.List.splitOnP_cons_eq_ite_splitOnPPrepend]
  by_cases sep : p x = true
  · rw [ite_eq_left sep, ite_eq_left sep]
  · rw [ite_eq_right sep, ite_eq_right sep, List.splitOnPPrepend_eq_modifyHead]
    cases xs.splitOnP p <;> rfl

public theorem List.splitOnP_spec : type_of% @_root_.List.splitOnP_spec := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.splitOnP_cons_eq_ite_modifyHead]
    by_cases sep : p x = true
    · rw [ite_eq_left sep, _root_.List.filter_cons_of_pos sep]
      exact congrArg (x :: ·) ih
    · rw [ite_eq_right sep, _root_.List.filter_cons_of_neg sep]
      have separators : ((xs.filter p).map (fun a => [a]) ++ [[]]) ≠ [] := by
        intro empty
        exact _root_.List.cons_ne_nil [] [] (_root_.List.append_eq_nil_iff.mp empty).2
      rw [(private_decl% @_root_.List.splitOnP_spec.flatten_zipWith) (_root_.List.splitOnP_ne_nil p xs) separators]
      exact congrArg (x :: ·) ih

public theorem List.intercalate_splitOn : type_of% @_root_.List.intercalate_splitOn := by
  intro α xs _ _ sep
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [_root_.List.splitOn_cons_eq_ite_modifyHead]
    by_cases hit : x == sep
    · rw [ite_eq_left hit, _root_.List.intercalate_cons_of_ne_nil (_root_.List.splitOn_ne_nil sep xs), ih]
      cases eq_of_beq hit
      rfl
    · rw [ite_eq_right hit]
      have nonempty := _root_.List.splitOn_ne_nil sep xs
      generalize xs.splitOn sep = parts at nonempty ih ⊢
      cases parts with
      | nil => exact (nonempty rfl).elim
      | cons first rest =>
        cases rest with
        | nil =>
          rw [_root_.List.modifyHead_cons, _root_.List.intercalate_singleton]
          rw [_root_.List.intercalate_singleton] at ih
          exact congrArg (x :: ·) ih
        | cons y ys =>
          have more := _root_.List.cons_ne_nil y ys
          rw [_root_.List.modifyHead_cons, _root_.List.intercalate_cons_of_ne_nil more]
          rw [_root_.List.intercalate_cons_of_ne_nil more] at ih
          exact congrArg (x :: ·) ih

end OmegaChecks.InitPort.Alternatives

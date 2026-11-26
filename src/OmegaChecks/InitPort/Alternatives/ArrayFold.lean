module
public import OmegaChecks.InitPort.Alternatives.VectorFold
import all Init.Data.Array.Basic
public import Init.Data.Array.Lemmas

/-! Array folds computed over the list representation. -/

namespace OmegaChecks.InitPort.Alternatives

public theorem Array.foldl_append : type_of% @_root_.Array.foldl_append := by
  intros
  simp only [← _root_.Array.foldl_toList, _root_.Array.toList_append, List.foldl_append]

public theorem Array.foldr_append : type_of% @_root_.Array.foldr_append := by
  intros
  simp only [← _root_.Array.foldr_toList, _root_.Array.toList_append, List.foldr_append]

public theorem Array.foldl_append' : type_of% @_root_.Array.foldl_append' := by
  intro α β f b xs ys stop h
  rw [← _root_.Array.size_append] at h
  subst stop
  exact Array.foldl_append

public theorem Array.foldr_append' : type_of% @_root_.Array.foldr_append' := by
  intro α β f b xs ys start h
  rw [← _root_.Array.size_append] at h
  subst start
  exact Array.foldr_append

public theorem Array.foldl_push : type_of% @_root_.Array.foldl_push := by
  intros
  simp only [← _root_.Array.foldl_toList, _root_.Array.toList_push, List.foldl_append]
  rfl

public theorem Array.foldr_push : type_of% @_root_.Array.foldr_push := by
  intros
  simp only [← _root_.Array.foldr_toList, _root_.Array.toList_push, List.foldr_append]
  rfl

public theorem Array.foldl_push' : type_of% @_root_.Array.foldl_push' := by
  intro β α f b xs a stop h
  rw [← _root_.Array.size_push a] at h
  subst stop
  exact Array.foldl_push

public theorem Array.foldr_push' : type_of% @_root_.Array.foldr_push' := by
  intro α β f b xs a start h
  rw [← _root_.Array.size_push a] at h
  subst start
  exact Array.foldr_push

public theorem Array.foldl_reverse : type_of% @_root_.Array.foldl_reverse := by
  intros
  simp only [← _root_.Array.foldl_toList, ← _root_.Array.foldr_toList,
    _root_.Array.toList_reverse, List.foldl_reverse]

public theorem Array.foldr_reverse : type_of% @_root_.Array.foldr_reverse := by
  intros
  simp only [← _root_.Array.foldl_toList, ← _root_.Array.foldr_toList,
    _root_.Array.toList_reverse, List.foldr_reverse]

public theorem Array.foldl_reverse' : type_of% @_root_.Array.foldl_reverse' := by
  intro α β xs f b stop h
  rw [← _root_.Array.size_reverse] at h
  subst stop
  exact Array.foldl_reverse

public theorem Array.foldr_reverse' : type_of% @_root_.Array.foldr_reverse' := by
  intro α β xs f b start h
  rw [← _root_.Array.size_reverse] at h
  subst start
  exact Array.foldr_reverse

public theorem List.foldl_rel : type_of% @_root_.List.foldl_rel := by
  intro α β γ l f g a b r h step
  induction l generalizing a b with
  | nil => exact h
  | cons x xs ih =>
    exact ih (step x (.head _) a b h) (fun y mem => step y (.tail _ mem))

public theorem Array.foldl_rel : type_of% @_root_.Array.foldl_rel := by
  intro α β γ xs f g a b r h step
  rw [← _root_.Array.foldl_toList, ← _root_.Array.foldl_toList]
  exact List.foldl_rel h (fun x hx => step x (_root_.Array.mem_def.mpr hx))

public theorem Array.foldlM_loop_empty : type_of% @_root_.Array.foldlM_loop_empty := by
  intro m β α s h monad f b i j
  unfold _root_.Array.foldlM.loop
  exact dite_eq_right (Nat.not_lt_of_ge (Nat.le_trans h (Nat.zero_le j)))

public theorem Array.foldlM_empty : type_of% @_root_.Array.foldlM_empty := by
  intros
  unfold _root_.Array.foldlM
  split <;> apply Array.foldlM_loop_empty


private theorem foldLeftPointwise (xs : List α) (f g : β → α → β)
    (step : ∀ b x, f b x = g b x) (b : β) : xs.foldl f b = xs.foldl g b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => exact (ih (f b x)).trans (congrArg (fun a => xs.foldl g a) (step b x))

private theorem foldRightPointwise (xs : List α) (f g : α → β → β)
    (step : ∀ x b, f x b = g x b) (b : β) : xs.foldr f b = xs.foldr g b := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact (congrArg (f x) ih).trans (step x _)

public theorem Array.foldl_flatMap : type_of% @_root_.Array.foldl_flatMap := by
  intro α β γ f g xs b
  rw [← _root_.Array.foldl_toList, _root_.Array.toList_flatMap, List.foldl_flatMap,
    ← _root_.Array.foldl_toList]
  exact foldLeftPointwise _ _ _ (fun _ _ => _root_.Array.foldl_toList g) b

public theorem Array.foldr_flatMap : type_of% @_root_.Array.foldr_flatMap := by
  intro α β γ f g xs b
  rw [← _root_.Array.foldr_toList, _root_.Array.toList_flatMap, List.foldr_flatMap,
    ← _root_.Array.foldr_toList]
  exact foldRightPointwise _ _ _ (fun _ _ => _root_.Array.foldr_toList g) b

public theorem Array.foldl_flatten : type_of% @_root_.Array.foldl_flatten := by
  intros
  rw [← _root_.Array.foldl_toList, _root_.Array.toList_flatten, List.foldl_flatten,
    List.foldl_map, ← _root_.Array.foldl_toList]
  apply foldLeftPointwise
  intros
  apply _root_.Array.foldl_toList

public theorem Array.foldr_flatten : type_of% @_root_.Array.foldr_flatten := by
  intros
  rw [← _root_.Array.foldr_toList, _root_.Array.toList_flatten, List.foldr_flatten,
    List.foldr_map, ← _root_.Array.foldr_toList]
  apply foldRightPointwise
  intros
  apply _root_.Array.foldr_toList

public theorem Array.foldl_flatten' : type_of% @_root_.Array.foldl_flatten' := by
  intros _ _ _ _ _ _ h
  cases h
  exact Array.foldl_flatten

public theorem Array.foldr_flatten' : type_of% @_root_.Array.foldr_flatten' := by
  intros _ _ _ _ _ _ h
  cases h
  exact Array.foldr_flatten

end OmegaChecks.InitPort.Alternatives

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

public theorem Array.map_eq_foldl : type_of% @_root_.Array.map_eq_foldl := by
  intros
  rw [_root_.Array.foldl_push_eq_append rfl, _root_.Array.empty_append]

public theorem Array.getElem_extract_loop_ge : type_of% @_root_.Array.getElem_extract_loop_ge := by
  intro α i xs ys count start ge bound
  induction count generalizing start ys with
  | zero =>
    rw [_root_.Array.extract_loop_zero] at bound
    exact (Nat.not_lt_of_ge ge bound).elim
  | succ count ih =>
    have valid := _root_.Array.getElem_extract_loop_ge_aux ge bound
    have before : start < xs.size := by omega
    have step := _root_.Array.extract_loop_succ (ys := ys) (size := count) before
    have next := Eq.subst (motive := fun a : _root_.Array α => i < a.size) step bound
    apply (getElem_congr_coll step).trans
    by_cases eq : ys.size = i
    · subst i
      have inside : ys.size < (ys.push xs[start]).size :=
        (_root_.Array.size_push ..).symm ▸ Nat.lt_succ_self _
      apply (_root_.Array.getElem_extract_loop_lt inside next).trans
      exact _root_.Array.getElem_push_eq.trans (getElem_congr_idx (Nat.add_sub_cancel ..).symm)
    · have ge' : (ys.push xs[start]).size ≤ i :=
        (_root_.Array.size_push ..).symm ▸ Nat.lt_of_le_of_ne ge eq
      apply (ih ge' next).trans
      apply getElem_congr_idx
      rw [_root_.Array.size_push]
      omega

public theorem List.foldl_flip_cons_eq_append' : type_of% @_root_.List.foldl_flip_cons_eq_append' := by
  intro α xs acc
  exact (_root_.List.foldl_flip_cons_eq_append (l := xs) (f := id)).trans
    (congrArg (fun ys => ys.reverse ++ acc) (_root_.List.map_id xs))



public theorem Array.foldlM_reverse : type_of% @_root_.Array.foldlM_reverse := by
  intros
  rw [← Array.foldlM_toList, ← Array.foldrM_toList, Array.toList_reverse]
  exact List.foldlM_reverse

public theorem Array.foldrM_reverse : type_of% @_root_.Array.foldrM_reverse := by
  intros
  rw [← Array.foldrM_toList, ← Array.foldlM_toList, Array.toList_reverse]
  exact List.foldrM_reverse

public theorem Array.foldlM_reverse' : type_of% @_root_.Array.foldlM_reverse' := by
  intro m α β mon xs f b stop w
  subst stop
  exact (congrArg (fun bound => xs.reverse.foldlM f b 0 bound) Array.size_reverse.symm).trans
    (_root_.Array.foldlM_reverse (xs := xs))

public theorem Array.foldrM_reverse' : type_of% @_root_.Array.foldrM_reverse' := by
  intro m α β mon xs f b start w
  subst start
  exact (congrArg (fun bound => xs.reverse.foldrM f b bound 0) Array.size_reverse.symm).trans
    (_root_.Array.foldrM_reverse (xs := xs))

end OmegaChecks.InitPort.Alternatives

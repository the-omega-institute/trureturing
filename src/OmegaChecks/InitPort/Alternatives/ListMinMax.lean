module
import all Init.Data.List.MinMaxIdx
import all Init.Data.List.MinMaxOn
import Init.Data.List.MinMax
import all Init.Data.Array.MinMax

/-! Nonemptiness and ordering of list extrema, proved using only membership and order laws. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem emptyHasNoResult {α : Type u} :
    false = true ↔ ([] : List α) ≠ [] :=
  ⟨(fun h => nomatch h), fun h => (h rfl).elim⟩

private theorem consHasResult {x : α} {xs : List α} :
    true = true ↔ x :: xs ≠ [] :=
  ⟨fun _ => List.cons_ne_nil x xs, fun _ => rfl⟩

public theorem List.isSome_min?_iff : type_of% @_root_.List.isSome_min?_iff := by
  intro α inst xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_max?_iff : type_of% @_root_.List.isSome_max?_iff := by
  intro α inst xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_minOn?_iff : type_of% @_root_.List.isSome_minOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_maxOn?_iff : type_of% @_root_.List.isSome_maxOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.isSome_minIdxOn?_iff : type_of% @_root_.List.isSome_minIdxOn?_iff := by
  intro β α le dec f xs
  cases xs with
  | nil => exact emptyHasNoResult
  | cons => exact consHasResult

public theorem List.le_apply_minOn_iff : type_of% @_root_.List.le_apply_minOn_iff := by
  intro β α le dec order xs f nonempty b
  exact ⟨fun below _ member => Std.IsPreorder.le_trans _ _ _ below (_root_.List.apply_minOn_le_of_mem member),
    fun below => below _ _root_.List.minOn_mem⟩

public theorem List.apply_minOn_le_apply_minOn_of_subset :
    type_of% @_root_.List.apply_minOn_le_apply_minOn_of_subset := by
  intro β α le dec order xs ys f subset nonempty
  exact _root_.List.apply_minOn_le_of_mem (subset _root_.List.minOn_mem)

private theorem foldAfterHead (f : β → α → β) (x : α) (xs : List α) (init : β) :
    (x :: xs).toArray.foldl f init 1 = xs.foldl f init := by
  rw [Array.foldl_eq_foldl_extract, ← Array.foldl_toList, Array.toList_extract]
  change (xs.take (xs.length + 1 - 1)).foldl f init = xs.foldl f init
  rw [Nat.add_sub_cancel, List.take_length]

public theorem List.min_toArray : type_of% @_root_.List.min_toArray := by
  intro α inst xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons a as => exact foldAfterHead min a as a

public theorem List.max_toArray : type_of% @_root_.List.max_toArray := by
  intro α inst xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons a as => exact foldAfterHead max a as a

public theorem List.min?_toArray : type_of% @_root_.List.min?_toArray := by
  intro α inst xs
  cases xs with
  | nil => rfl
  | cons a as =>
    unfold Array.min?
    rw [dite_eq_left (fun e => List.cons_ne_nil a as (congrArg Array.toList e))]
    exact congrArg some List.min_toArray

public theorem List.max?_toArray : type_of% @_root_.List.max?_toArray := by
  intro α inst xs
  cases xs with
  | nil => rfl
  | cons a as =>
    unfold Array.max?
    rw [dite_eq_left (fun e => List.cons_ne_nil a as (congrArg Array.toList e))]
    exact congrArg some List.max_toArray

end OmegaChecks.InitPort.Alternatives

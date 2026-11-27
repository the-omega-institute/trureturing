module
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Basic
import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop

/-! Finite filtering follows the yielding and skipping steps of the input iterator. -/

open Std Std.Iterators
namespace OmegaChecks.InitPort.Alternatives

public theorem Std.Iter.toList_filterMap : type_of% @_root_.Std.Iter.toList_filterMap := by
  intro α β γ iterator it finite f
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Iter.toList_eq_match_step (it := it.filterMap f),
      _root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Iter.val_step_filterMap]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h =>
      cases keep : f out with
      | none => simpa only [List.filterMap_cons, keep] using ihy h
      | some y => simpa only [List.filterMap_cons, keep] using congrArg (List.cons y) (ihy h)
    | skip next h => exact ihs h
    | done _ => rfl

public theorem Std.Iter.toList_filter : type_of% @_root_.Std.Iter.toList_filter := by
  intro α β iterator it finite f
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Iter.toList_eq_match_step (it := it.filter f),
      _root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Iter.val_step_filter]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h =>
      cases keep : f out with
      | false => simpa only [List.filter_cons, keep, Bool.false_eq_true, ite_false] using ihy h
      | true => simpa only [List.filter_cons, keep, ite_true] using congrArg (List.cons out) (ihy h)
    | skip next h => exact ihs h
    | done _ => rfl

public theorem Std.Iter.toArray_filterMap : type_of% @_root_.Std.Iter.toArray_filterMap := by
  intros
  apply Array.toList_inj.mp
  rw [Array.toList_filterMap, _root_.Std.Iter.toList_toArray, _root_.Std.Iter.toList_toArray,
    _root_.Std.Iter.toList_filterMap]

public theorem Std.Iter.toArray_filter : type_of% @_root_.Std.Iter.toArray_filter := by
  intros
  apply Array.toList_inj.mp
  rw [Array.toList_filter, _root_.Std.Iter.toList_toArray, _root_.Std.Iter.toList_toArray,
    _root_.Std.Iter.toList_filter]

public theorem Std.Iter.toArray_map : type_of% @_root_.Std.Iter.toArray_map := by
  intros
  apply Array.toList_inj.mp
  rw [Array.toList_map, _root_.Std.Iter.toList_toArray, _root_.Std.Iter.toList_toArray, _root_.Std.Iter.toList_map]

public theorem Std.Iter.toListRev_filter : type_of% @_root_.Std.Iter.toListRev_filter := by
  intros
  rw [_root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toList_filter, List.filter_reverse]

public theorem Std.Iter.toListRev_map : type_of% @_root_.Std.Iter.toListRev_map := by
  intros
  rw [_root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toList_map, List.map_reverse]

public theorem Std.Iter.toListRev_filterMap : type_of% @_root_.Std.Iter.toListRev_filterMap := by
  intros
  rw [_root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toList_filterMap, List.filterMap_reverse]

public theorem Std.Iter.reverse_toListRev : type_of% @_root_.Std.Iter.reverse_toListRev := by
  intros
  rw [_root_.Std.Iter.toListRev_eq, List.reverse_reverse]

public theorem Std.Iter.toListRev_ensureTermination : type_of% @_root_.Std.Iter.toListRev_ensureTermination := by
  intro α β _ _ it
  exact _root_.Std.Iter.toListRev_ensureTermination_eq_toListRev.trans (_root_.Std.Iter.toListRev_eq (it := it))

public theorem Std.Iter.toArray_eq_match_step : type_of% @_root_.Std.Iter.toArray_eq_match_step := by
  intro α β _ _ it
  apply Array.toList_inj.mp
  rw [_root_.Std.Iter.toList_toArray, _root_.Std.Iter.toList_eq_match_step]
  cases it.step.val with
  | yield next out => rw [Array.toList_append, _root_.Std.Iter.toList_toArray]; rfl
  | skip next => exact _root_.Std.Iter.toList_toArray.symm
  | done => rfl

public theorem Std.Iter.toListRev_eq_match_step : type_of% @_root_.Std.Iter.toListRev_eq_match_step := by
  intro α β _ _ it
  rw [_root_.Std.Iter.toListRev_eq, _root_.Std.Iter.toList_eq_match_step]
  cases it.step.val with
  | yield next out =>
    dsimp only
    rw [List.reverse_cons, _root_.Std.Iter.toListRev_eq]
  | skip next => exact _root_.Std.Iter.toListRev_eq.symm
  | done => rfl

public theorem Std.IterM.drain_eq_foldM : type_of% @_root_.Std.IterM.drain_eq_foldM := by
  intro α β m iterator finite mon law loop it
  exact congrArg (fun action => ForIn.forIn (m := m) it PUnit.unit (fun _ _ => action))
    (map_pure (f := m) ForInStep.yield PUnit.unit).symm

public theorem Std.Iter.fold_map : type_of% @_root_.Std.Iter.fold_map := by
  intros
  rw [← _root_.Std.Iter.foldl_toList, ← _root_.Std.Iter.foldl_toList, _root_.Std.Iter.toList_map, List.foldl_map]
public theorem Std.Iter.fold_filter : type_of% @_root_.Std.Iter.fold_filter := by
  intros
  rw [← _root_.Std.Iter.foldl_toList, ← _root_.Std.Iter.foldl_toList, _root_.Std.Iter.toList_filter, List.foldl_filter]
public theorem Std.Iter.fold_filterMap : type_of% @_root_.Std.Iter.fold_filterMap := by
  intro α β γ δ iter finite loop laws f g init it
  rw [← _root_.Std.Iter.foldl_toList, ← _root_.Std.Iter.foldl_toList, _root_.Std.Iter.toList_filterMap, List.foldl_filterMap]
  induction it.toList generalizing init with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.foldl]
    cases f x <;> exact ih
public theorem Std.Iter.length_map : type_of% @_root_.Std.Iter.length_map := by
  intros
  rw [← _root_.Std.Iter.length_toList_eq_length, ← _root_.Std.Iter.length_toList_eq_length, _root_.Std.Iter.toList_map, List.length_map]

end OmegaChecks.InitPort.Alternatives

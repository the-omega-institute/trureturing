module
public import Init.Data.Iterators.Lemmas.Combinators.FilterMap
public import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Basic

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

end OmegaChecks.InitPort.Alternatives

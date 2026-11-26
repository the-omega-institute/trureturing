module
public import Init.Data.Iterators.Lemmas.Producers.List
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Combinators.Take

open Std Std.Iterators

namespace OmegaChecks.InitPort.Alternatives

public theorem List.toList_iter : type_of% @_root_.List.toList_iter := by
  intro α xs
  induction xs with
  | nil =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.List.step_iter_nil]
  | cons a xs ih =>
    rw [_root_.Std.Iter.toList_eq_match_step, _root_.List.step_iter_cons]
    exact congrArg (a :: ·) ih

public theorem Std.Iter.toList_toTake : type_of% @_root_.Std.Iter.toList_toTake := by
  intro α β iter finite it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy ihs =>
    rw [_root_.Std.Iter.toList_eq_match_step (it := it.toTake),
      _root_.Std.Iter.toList_eq_match_step (it := it), _root_.Std.Iter.step_toTake]
    cases it.step using PlausibleIterStep.casesOn with
    | yield next out h => exact congrArg (out :: ·) (ihy h)
    | skip next h => exact ihs h
    | done _ => rfl

end OmegaChecks.InitPort.Alternatives

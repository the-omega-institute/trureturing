module
public import Init.Data.Iterators.Lemmas.Producers.List
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Combinators.Take
public import Init.Data.Slice.Array.Lemmas
public import OmegaChecks.InitPort.Alternatives.IteratorSlice
import all OmegaChecks.InitPort.Alternatives.IteratorSlice
public import Init.Data.Slice.List.Lemmas
import all Init.Data.Slice.List.Basic
import all Init.Data.Slice.Array.Lemmas
import all Init.Data.Slice.Array.Iterator
import all Init.Data.Iterators.Basic
import all Init.Data.Slice.Operations

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

public theorem SubarrayIterator.val_step_eq :
    type_of% (private_decl% @_root_.SubarrayIterator.val_step_eq) := by
  intro α it
  simp only [_root_.Std.Iter.step, IterM.Step.toPure, IterM.step, Iterator.step,
    Id.run_pure, Shrink.inflate_deflate]
  rcases it with ⟨⟨xs⟩⟩
  dsimp only [Iter.toIterM, _root_.SubarrayIterator.step]
  by_cases h : xs.start < xs.stop
  · rw [dite_eq_left h, dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

set_option backward.proofsInPublic true in
public theorem SubarrayIterator.step_eq {α : Type u} {it : Iter (α := _root_.SubarrayIterator α) α} :
    it.step = if h : it.internalState.xs.start < it.internalState.xs.stop then
        ⟨.yield ⟨⟨it.internalState.xs.array, it.internalState.xs.start + 1, it.internalState.xs.stop,
                h, it.internalState.xs.stop_le_array_size⟩⟩
            (it.internalState.xs.array[it.internalState.xs.start]'(Nat.lt_of_lt_of_le h it.internalState.xs.stop_le_array_size)),
          by
            change .yield _ _ = _root_.SubarrayIterator.step _
            rcases it with ⟨⟨s⟩⟩
            dsimp only [_root_.SubarrayIterator.step, Iter.toIterM]
            rw [dite_eq_left h]⟩
      else
        ⟨.done, by
          change .done = _root_.SubarrayIterator.step _
          rcases it with ⟨⟨s⟩⟩
          dsimp only [_root_.SubarrayIterator.step, Iter.toIterM]
          rw [dite_eq_right h]⟩ := by
  by_cases h : it.internalState.xs.start < it.internalState.xs.stop
  · rw [dite_eq_left h]
    apply Subtype.ext
    exact ((private_decl% _root_.SubarrayIterator.val_step_eq) : it.step.val = _).trans (dite_eq_left h)
  · rw [dite_eq_right h]
    apply Subtype.ext
    exact ((private_decl% _root_.SubarrayIterator.val_step_eq) : it.step.val = _).trans (dite_eq_right h)

public theorem SubarrayIterator.toList_eq :
    type_of% (private_decl% @_root_.SubarrayIterator.toList_eq) := by
  intro α it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy _ =>
    let xs := it.internalState.xs
    have width : (xs.array.toList.take xs.stop).length = xs.stop :=
      _root_.List.length_take_of_le xs.stop_le_array_size
    rw [_root_.Std.Iter.toList_eq_match_step, private_decl% _root_.SubarrayIterator.val_step_eq]
    by_cases h : xs.start < xs.stop
    · rw [dite_eq_left h]
      let next : Iter (α := _root_.SubarrayIterator α) α :=
        ⟨⟨xs.array, xs.start + 1, xs.stop, h, xs.stop_le_array_size⟩⟩
      have read : xs.start < xs.array.size := Nat.lt_of_lt_of_le h xs.stop_le_array_size
      have step : it.IsPlausibleStep (.yield next xs.array[xs.start]) := by
        have seen := it.step.property
        rw [private_decl% _root_.SubarrayIterator.val_step_eq, dite_eq_left h] at seen
        exact seen
      have valid : xs.start < (xs.array.toList.take xs.stop).length := width.symm ▸ h
      have head := _root_.List.getElem_take (xs := xs.array.toList) (i := xs.start) (j := xs.stop) (h := valid)
      exact (congrArg (xs.array[xs.start] :: ·) (ihy step)).trans
        ((congrArg (· :: (xs.array.toList.take xs.stop).drop (xs.start + 1)) head.symm).trans
          (_root_.List.drop_eq_getElem_cons valid).symm)
    · rw [dite_eq_right h]
      exact (_root_.List.drop_eq_nil_of_le (width.symm ▸ Nat.le_of_not_gt h)).symm

public theorem ListSlice.toArray_mkSlice_rci : type_of% @_root_.ListSlice.toArray_mkSlice_rci := by
  intros
  rw [← _root_.ListSlice.toArray_toList, _root_.ListSlice.toList_mkSlice_rci,
    _root_.List.toArray_drop, _root_.ListSlice.toArray_toList]

public theorem Subarray.getElem_toList._proof_1 :
    type_of% (private_decl% @_root_.Subarray.getElem_toList._proof_1) := by
  intro α i xs bound
  exact Nat.lt_of_lt_of_eq bound _root_.Subarray.length_toList

public theorem Subarray.getElem_eq_getElem_toList._proof_1 :
    type_of% (private_decl% @_root_.Subarray.getElem_eq_getElem_toList._proof_1) := by
  intro α i xs bound
  exact Nat.lt_of_lt_of_eq bound _root_.Subarray.length_toList.symm

public theorem Subarray.getElem_toList : type_of% @_root_.Subarray.getElem_toList := by
  intro α i xs bound
  exact (getElem_congr_coll (c := xs.toList) (i := i) (w := bound) _root_.Subarray.toList_eq_drop_take).trans
    (_root_.List.getElem_drop.trans _root_.List.getElem_take)

public theorem Subarray.size_toArray : type_of% @_root_.Subarray.size_toArray := by
  intro α xs
  exact (_root_.Array.length_toList (xs := xs.toArray)).symm.trans
    ((congrArg _root_.List.length _root_.Subarray.toList_toArray).trans _root_.Subarray.length_toList)

public theorem Subarray.toArray_mkSlice_rci : type_of% @_root_.Subarray.toArray_mkSlice_rci := by
  intros
  rw [← _root_.Subarray.toArray_toList, _root_.Subarray.toList_mkSlice_rci,
    _root_.List.toArray_drop, _root_.Subarray.toArray_toList]

public theorem ListSlice.toArray_mkSlice_roi : type_of% @_root_.ListSlice.toArray_mkSlice_roi := by
  intros
  rw [_root_.ListSlice.mkSlice_roi_eq_mkSlice_rci, ListSlice.toArray_mkSlice_rci]

public theorem Subarray.toArray_mkSlice_roi : type_of% @_root_.Subarray.toArray_mkSlice_roi := by
  intros
  rw [_root_.Subarray.mkSlice_roi_eq_mkSlice_rci, Subarray.toArray_mkSlice_rci]

private theorem listSliceArrayCongr {a b : ListSlice α} (h : a.toList = b.toList) :
    a.toArray = b.toArray := by
  exact _root_.ListSlice.toArray_toList.symm.trans
    ((congrArg _root_.List.toArray h).trans _root_.ListSlice.toArray_toList)

section
local notation "sizeOfSlice" => fun xs => @_root_.Std.Slice.size _ xs (@instSliceSizeListSliceData _)

public theorem ListSlice.size_eq_length_toList {xs : ListSlice α} : (sizeOfSlice xs) = xs.toList.length := by
  change (@instSliceSizeListSliceData α).size xs = _
  rw [_root_.ListSlice.toList_eq]
  rcases xs with ⟨⟨xs, stop⟩⟩
  cases stop with
  | none => rfl
  | some n => exact (_root_.List.length_take (l := xs) (i := n)).symm

public theorem ListSlice.toList_mkSlice_rci_eq_toList_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toList = xs[lo...(sizeOfSlice xs)].toList := by
  rw [_root_.ListSlice.toList_mkSlice_rci, _root_.ListSlice.toList_mkSlice_rco,
    ListSlice.size_eq_length_toList, _root_.List.take_length]

public theorem ListSlice.toList_mkSlice_roi_eq_toList_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs[(lo + 1)...(sizeOfSlice xs)].toList := by
  rw [_root_.ListSlice.mkSlice_roi_eq_mkSlice_rci, ListSlice.toList_mkSlice_rci_eq_toList_mkSlice_rco]

public theorem ListSlice.toList_mkSlice_roi_eq_toList_mkSlice_roo {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toList = xs[lo<...(sizeOfSlice xs)].toList := by
  rw [_root_.ListSlice.mkSlice_roo_eq_mkSlice_rco, ListSlice.toList_mkSlice_roi_eq_toList_mkSlice_rco]

public theorem ListSlice.toArray_mkSlice_rci_eq_toArray_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].toArray = xs[lo...(sizeOfSlice xs)].toArray :=
  listSliceArrayCongr ListSlice.toList_mkSlice_rci_eq_toList_mkSlice_rco

public theorem ListSlice.toArray_mkSlice_roi_eq_toArray_mkSlice_rco {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toArray = xs[(lo + 1)...(sizeOfSlice xs)].toArray :=
  listSliceArrayCongr ListSlice.toList_mkSlice_roi_eq_toList_mkSlice_rco

public theorem ListSlice.toArray_mkSlice_roi_eq_toArray_mkSlice_roo {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].toArray = xs[lo<...(sizeOfSlice xs)].toArray :=
  listSliceArrayCongr ListSlice.toList_mkSlice_roi_eq_toList_mkSlice_roo

end
end OmegaChecks.InitPort.Alternatives

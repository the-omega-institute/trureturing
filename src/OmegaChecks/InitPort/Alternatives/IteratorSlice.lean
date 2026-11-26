module
public import Init.Data.Iterators.Consumers.Monadic.Access
public import OmegaChecks.InitPort.Alternatives.FiniteLoop
public import Init.Data.Slice.Array.Lemmas
import all Init.Data.Slice.Array.Iterator
public import Init.Data.Slice.List.Lemmas
import all Init.Data.Slice.List.Basic
import all Init.Data.Iterators.Combinators.Monadic.Take
import all Init.Data.Iterators.Combinators.Monadic.FlatMap
import all Init.Data.Iterators.Combinators.Monadic.FilterMap
import all Init.Data.Iterators.Combinators.FlatMap
public import Init.Data.Iterators.Lemmas.Combinators.FlatMap
public import Init.Data.Iterators.Lemmas.Combinators.Take
import all Init.Data.Iterators.Combinators.Monadic.ULift
public import Init.Data.Iterators.Lemmas.Combinators.ULift

/-! Slice lengths from endpoints and pure iterator reductions from their step constructors. -/

open Std Std.Iterators Std.Iterators.Types

namespace OmegaChecks.InitPort.Alternatives

public theorem Id.instLawfulMonad : type_of% @_root_.Id.instLawfulMonad := by
  exact {
    map_const := rfl
    id_map := fun _ => rfl
    comp_map := fun _ _ _ => rfl
    seqLeft_eq := fun _ _ => rfl
    seqRight_eq := fun _ _ => rfl
    pure_seq := fun _ _ => rfl
    map_pure := fun _ _ => rfl
    seq_pure := fun _ _ => rfl
    seq_assoc := fun _ _ _ => rfl
    bind_pure_comp := fun _ _ => rfl
    bind_map := fun _ _ => rfl
    pure_bind := fun _ _ => rfl
    bind_assoc := fun _ _ _ => rfl }

public theorem Array.size_mkSlice_rco : type_of% @_root_.Array.size_mkSlice_rco := by
  intro α xs lo hi
  rw [Subarray.size_eq, Array.start_mkSlice_rco, Array.stop_mkSlice_rco]
  omega

public theorem Subarray.size_mkSlice_rco : type_of% @_root_.Subarray.size_mkSlice_rco := by
  intro α xs lo hi
  change (xs.array[(max lo 0 + xs.start)...(min hi xs.size + xs.start)]).size = _
  rw [Array.size_mkSlice_rco]
  have h := xs.start_le_stop
  have h' := xs.stop_le_array_size
  rw [Subarray.size_eq]
  omega

public theorem Array.size_mkSlice_rcc : type_of% @_root_.Array.size_mkSlice_rcc := by
  intros
  rw [_root_.Array.mkSlice_rcc_eq_mkSlice_rco, Array.size_mkSlice_rco]

public theorem Array.size_mkSlice_rci : type_of% @_root_.Array.size_mkSlice_rci := by
  intros
  rw [_root_.Array.mkSlice_rci_eq_mkSlice_rco, Array.size_mkSlice_rco, Nat.min_self]

public theorem Array.size_mkSlice_roo : type_of% @_root_.Array.size_mkSlice_roo := by
  intros
  rw [_root_.Array.mkSlice_roo_eq_mkSlice_rco, Array.size_mkSlice_rco]

public theorem Array.size_mkSlice_roc : type_of% @_root_.Array.size_mkSlice_roc := by
  intros
  rw [_root_.Array.mkSlice_roc_eq_mkSlice_rco, Array.size_mkSlice_rco]

public theorem Array.size_mkSlice_roi : type_of% @_root_.Array.size_mkSlice_roi := by
  intros
  rw [_root_.Array.mkSlice_roi_eq_mkSlice_rco, Array.size_mkSlice_rco, Nat.min_self]

public theorem Array.size_mkSlice_rio : type_of% @_root_.Array.size_mkSlice_rio := by
  intros
  rw [_root_.Array.mkSlice_rio_eq_mkSlice_rco, Array.size_mkSlice_rco, Nat.sub_zero]

public theorem Array.size_mkSlice_ric : type_of% @_root_.Array.size_mkSlice_ric := by
  intros
  rw [_root_.Array.mkSlice_ric_eq_mkSlice_rco, Array.size_mkSlice_rco, Nat.sub_zero]

public theorem Array.size_mkSlice_rii : type_of% @_root_.Array.size_mkSlice_rii := by
  intros
  rw [_root_.Array.mkSlice_rii_eq_mkSlice_rco, Array.size_mkSlice_rco, Nat.min_self, Nat.sub_zero]

public theorem Subarray.size_mkSlice_rcc : type_of% @_root_.Subarray.size_mkSlice_rcc := by
  intros
  rw [_root_.Subarray.mkSlice_rcc_eq_mkSlice_rco, Subarray.size_mkSlice_rco]

public theorem Subarray.size_mkSlice_rci : type_of% @_root_.Subarray.size_mkSlice_rci := by
  intros
  rw [_root_.Subarray.mkSlice_rci_eq_mkSlice_rco, Subarray.size_mkSlice_rco, Nat.min_self]

public theorem Subarray.size_mkSlice_roo : type_of% @_root_.Subarray.size_mkSlice_roo := by
  intros
  rw [_root_.Subarray.mkSlice_roo_eq_mkSlice_rco, Subarray.size_mkSlice_rco]

public theorem Subarray.size_mkSlice_roc : type_of% @_root_.Subarray.size_mkSlice_roc := by
  intros
  rw [_root_.Subarray.mkSlice_roc_eq_mkSlice_rco, Subarray.size_mkSlice_rco]

public theorem Subarray.size_mkSlice_roi : type_of% @_root_.Subarray.size_mkSlice_roi := by
  intros
  rw [_root_.Subarray.mkSlice_roi_eq_mkSlice_rco, Subarray.size_mkSlice_rco, Nat.min_self]

public theorem Subarray.size_mkSlice_rio : type_of% @_root_.Subarray.size_mkSlice_rio := by
  intros
  rw [_root_.Subarray.mkSlice_rio_eq_mkSlice_rco, Subarray.size_mkSlice_rco, Nat.sub_zero]

public theorem Subarray.size_mkSlice_ric : type_of% @_root_.Subarray.size_mkSlice_ric := by
  intros
  rw [_root_.Subarray.mkSlice_ric_eq_mkSlice_rco, Subarray.size_mkSlice_rco, Nat.sub_zero]

@[instance_reducible] public def instSliceSizeListSliceData {α : Type u} : Std.Slice.SliceSize (Std.Slice.Internal.ListSliceData α) where
  size s := match s.internalRepresentation.stop with
    | none => s.internalRepresentation.list.length
    | some n => min n s.internalRepresentation.list.length

section ListSize

attribute [local instance] instSliceSizeListSliceData

public theorem List.size_mkSlice_rco {xs : List α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.length - lo := by
  change (@instSliceSizeListSliceData α).size (xs.toSlice lo hi) = _
  unfold _root_.List.toSlice
  split
  · change min (hi - lo) (xs.drop lo).length = _
    rw [_root_.List.length_drop]
    omega
  · change min 0 0 = _
    omega

public theorem List.size_mkSlice_rci {xs : List α} {lo : Nat} :
    xs[lo...*].size = xs.length - lo := by
  exact _root_.List.length_drop

public theorem List.size_mkSlice_rcc {xs : List α} {lo hi : Nat} :
    xs[lo...=hi].size = min (hi + 1) xs.length - lo := by
  rw [_root_.List.mkSlice_rcc_eq_mkSlice_rco, List.size_mkSlice_rco]

public theorem List.size_mkSlice_roo {xs : List α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.length - (lo + 1) := by
  rw [_root_.List.mkSlice_roo_eq_mkSlice_rco, List.size_mkSlice_rco]

public theorem List.size_mkSlice_roc {xs : List α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.length - (lo + 1) := by
  rw [_root_.List.mkSlice_roc_eq_mkSlice_rco, List.size_mkSlice_rco]

public theorem List.size_mkSlice_roi {xs : List α} {lo : Nat} :
    xs[lo<...*].size = xs.length - (lo + 1) := by
  rw [_root_.List.mkSlice_roi_eq_mkSlice_rci, List.size_mkSlice_rci]

public theorem List.size_mkSlice_rio {xs : List α} {hi : Nat} :
    xs[*...hi].size = min hi xs.length := by
  rw [_root_.List.mkSlice_rio_eq_mkSlice_rco, List.size_mkSlice_rco, Nat.sub_zero]

public theorem List.size_mkSlice_ric {xs : List α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.length := by
  rw [_root_.List.mkSlice_ric_eq_mkSlice_rco, List.size_mkSlice_rco, Nat.sub_zero]

public theorem List.size_mkSlice_rii {xs : List α} :
    xs[*...*].size = xs.length := by
  rw [_root_.List.mkSlice_rii_eq_mkSlice_rci, List.size_mkSlice_rci, Nat.sub_zero]

public theorem ListSlice.size_mkSlice_rco {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.size - lo := by
  change (xs.internalRepresentation.list[lo...(match xs.internalRepresentation.stop with
    | none => hi | some n => min n hi)]).size = _
  rw [List.size_mkSlice_rco]
  change _ = min hi (match xs.internalRepresentation.stop with
    | none => xs.internalRepresentation.list.length
    | some n => min n xs.internalRepresentation.list.length) - lo
  cases xs.internalRepresentation.stop <;> dsimp <;> omega

public theorem ListSlice.size_mkSlice_rcc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo...=hi].size = min (hi + 1) xs.size - lo := by
  rw [_root_.ListSlice.mkSlice_rcc_eq_mkSlice_rco, ListSlice.size_mkSlice_rco]

public theorem ListSlice.size_mkSlice_rci {xs : ListSlice α} {lo : Nat} :
    xs[lo...*].size = xs.size - lo := by
  change (match xs.internalRepresentation.stop with
    | none => xs.internalRepresentation.list[lo...*]
    | some n => xs.internalRepresentation.list[lo...n]).size = _
  change _ = (match xs.internalRepresentation.stop with
    | none => xs.internalRepresentation.list.length
    | some n => min n xs.internalRepresentation.list.length) - lo
  cases xs.internalRepresentation.stop with
  | none => exact List.size_mkSlice_rci
  | some n => exact List.size_mkSlice_rco

public theorem ListSlice.size_mkSlice_roo {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.size - (lo + 1) := by
  rw [_root_.ListSlice.mkSlice_roo_eq_mkSlice_rco, ListSlice.size_mkSlice_rco]

public theorem ListSlice.size_mkSlice_roc {xs : ListSlice α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.size - (lo + 1) := by
  rw [_root_.ListSlice.mkSlice_roc_eq_mkSlice_rco, ListSlice.size_mkSlice_rco]

public theorem ListSlice.size_mkSlice_roi {xs : ListSlice α} {lo : Nat} :
    xs[lo<...*].size = xs.size - (lo + 1) := by
  rw [_root_.ListSlice.mkSlice_roi_eq_mkSlice_rci, ListSlice.size_mkSlice_rci]

public theorem ListSlice.size_mkSlice_rio {xs : ListSlice α} {hi : Nat} :
    xs[*...hi].size = min hi xs.size := by
  rw [_root_.ListSlice.mkSlice_rio_eq_mkSlice_rco, ListSlice.size_mkSlice_rco, Nat.sub_zero]

public theorem ListSlice.size_mkSlice_ric {xs : ListSlice α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.size := by
  rw [_root_.ListSlice.mkSlice_ric_eq_mkSlice_rco, ListSlice.size_mkSlice_rco, Nat.sub_zero]

end ListSize

public theorem Std.Iter.step_take : type_of% @_root_.Std.Iter.step_take := by
  intro α β _ n it
  apply Subtype.ext
  cases n with
  | zero =>
    exact congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate
  | succ n =>
    unfold Iter.step IterM.step
    dsimp only [Iter.take, IterM.take, Take.instIterator, IterM.step, Iterator.step,
      Iter.toIterM, IterM.toIter, pure, Bind.bind, Id.run]
    generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
    cases q using PlausibleIterStep.casesOn <;>
      exact congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate

public theorem Std.Iter.step_flatMapAfter : type_of% @_root_.Std.Iter.step_flatMapAfter := by
  intro α β α₂ γ _ _ f outer inner
  apply Subtype.ext
  cases inner with
  | none =>
    unfold Iter.step IterM.step
    dsimp only [Iter.flatMapAfter, IterM.flatMapAfter, IterM.flattenAfter, Flatten.instIterator,
      IterM.map, IterM.mapWithPostcondition, IterM.InternalCombinators.map,
      Iterators.Types.Map, Iterators.Types.Map.instIterator, Iterators.Types.Map.instIterator._aux_3,
      Iterators.Types.FilterMap.instIterator, IterM.step, Iterator.step, Iter.toIterM, IterM.toIter,
      Option.map, Functor.map, pure, Bind.bind, monadLift, Id.run]
    generalize Shrink.inflate (Iterator.step { internalState := outer.internalState : IterM (α := α) Id β}) = q
    cases q using PlausibleIterStep.casesOn <;>
      dsimp only [PostconditionT.map, PostconditionT.pure, bind, pure, Functor.map] <;>
      erw [Shrink.inflate_deflate] <;>
      exact congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate
  | some inner =>
    unfold Iter.step IterM.step
    dsimp only [Iter.flatMapAfter, IterM.flatMapAfter, IterM.flattenAfter, Flatten.instIterator,
      IterM.step, Iterator.step, Iter.toIterM, IterM.toIter, Option.map, Functor.map, pure, Bind.bind, Id.run]
    generalize Shrink.inflate (Iterator.step { internalState := inner.internalState : IterM (α := α₂) Id γ}) = q
    cases q using PlausibleIterStep.casesOn <;>
      exact congrArg (fun s => (IterM.Step.toPure s).val) Shrink.inflate_deflate

public theorem Std.Iter.step_uLift : type_of% @_root_.Std.Iter.step_uLift := by
  intro α β _ it
  apply Subtype.ext
  unfold Iter.step IterM.step
  dsimp only [Iter.uLift, IterM.uLift, ULiftIterator.instIterator, IterM.step, Iterator.step,
    Iter.toIterM, IterM.toIter, ULiftT.run, pure, Bind.bind, monadLift, Id.run]
  refine Eq.trans (congrArg (fun s => (IterM.Step.toPure (it := it.uLift.toIterM) s).val) Shrink.inflate_deflate) ?_
  dsimp only [IterM.Step.toPure]
  generalize Shrink.inflate (Iterator.step { internalState := it.internalState : IterM (α := α) Id β}) = q
  cases q using PlausibleIterStep.casesOn <;> rfl

public theorem SubarrayIterator.instFinitelessRelation._proof_2 :
    type_of% (private_decl% @_root_.SubarrayIterator.instFinitelessRelation._proof_2) := by
  intro α it next h
  obtain ⟨s, nextEq, stepEq⟩ := h
  rcases it with ⟨⟨xs⟩⟩
  change s = SubarrayIterator.step _ at stepEq
  subst s
  dsimp only [SubarrayIterator.step] at nextEq
  split at nextEq
  · cases Option.some.inj nextEq
    change xs.stop - (xs.start + 1) < xs.stop - xs.start
    omega
  · cases nextEq

@[instance_reducible] public def Array.instAppendSubarray {α : Type u} : Append (Subarray α) where
  append x y :=
    let data := x.copy ++ y.copy
    data.toSubarray 0 data.size

private def listSliceContents {α : Type u} (s : ListSlice α) : List α :=
  match s.internalRepresentation.stop with
  | none => s.internalRepresentation.list
  | some n => s.internalRepresentation.list.take n

@[instance_reducible] public def List.instAppendListSlice {α : Type u} : Append (ListSlice α) where
  append x y :=
    let data := listSliceContents x ++ listSliceContents y
    data.toSlice 0 data.length

public def Array.Subarray.repr {α : Type u} [Repr α] (s : Subarray α) : Std.Format :=
  _root_.repr s.copy ++ ".toSubarray"

@[instance_reducible] public def Array.instToStringSubarray {α : Type u} [ToString α] : ToString (Subarray α) :=
  ⟨fun s => toString s.copy⟩

public def List.ListSlice.repr {α : Type u} [Repr α] (s : ListSlice α) : Std.Format :=
  let xs := listSliceContents s
  _root_.repr xs ++ ".toSlice 0 " ++ toString xs.length

@[instance_reducible] public def List.instToStringListSlice {α : Type u} [ToString α] : ToString (ListSlice α) :=
  ⟨fun s => toString (listSliceContents s).toArray⟩

public theorem Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure :
    type_of% @_root_.Std.Iterators.Types.Flatten.IsPlausibleStep.outerYield_flatMapM_pure := by
  intros α β α₂ γ m _ _ _ _ _ _ f it it' inner out h returns
  apply Flatten.IsPlausibleStep.outerYield_flatMapM (b := out)
  · apply FilterMap.PlausibleStep.yieldSome h
    exact ⟨⟨out, rfl⟩, rfl⟩
  · exact returns

public theorem Std.IterM.not_isPlausibleNthOutputStep_yield :
    type_of% @_root_.Std.IterM.not_isPlausibleNthOutputStep_yield := by
  intro α β m _ n it it' h
  generalize eq : IterStep.skip it' = s at h
  induction h with
  | zero_yield => cases eq
  | done => cases eq
  | yield _ _ ih => exact ih eq
  | skip _ _ ih => exact ih eq

end OmegaChecks.InitPort.Alternatives

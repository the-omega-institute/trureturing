module
public import Init.Data.Slice.Array.Lemmas
public import Init.Data.Slice.List.Lemmas
import all Init.Data.Slice.List.Basic
public import Init.Data.Iterators.Lemmas.Combinators.Take

/-! Slice lengths follow from their endpoints, and identity-monad laws reduce pointwise. -/

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

end OmegaChecks.InitPort.Alternatives

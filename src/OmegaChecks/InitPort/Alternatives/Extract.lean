module
public import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Extract

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.min_zero (a : Nat) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le a)

public theorem Nat.zero_min (a : Nat) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le a)

public theorem Nat.add_min_add_left (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  cases Nat.le_total b c with
  | inl h => rw [Nat.min_eq_left (Nat.add_le_add_left h a), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.add_le_add_left h a), Nat.min_eq_right h]

public theorem Nat.add_min_add_right (a b c : Nat) : min (a + c) (b + c) = min a b + c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left (Nat.add_le_add_right h c), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.add_le_add_right h c), Nat.min_eq_right h]

public theorem Nat.add_max_add_left (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  cases Nat.le_total b c with
  | inl h => rw [Nat.max_eq_right (Nat.add_le_add_left h a), Nat.max_eq_right h]
  | inr h => rw [Nat.max_eq_left (Nat.add_le_add_left h a), Nat.max_eq_left h]

public theorem Nat.add_max_add_right (a b c : Nat) : max (a + c) (b + c) = max a b + c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.max_eq_right (Nat.add_le_add_right h c), Nat.max_eq_right h]
  | inr h => rw [Nat.max_eq_left (Nat.add_le_add_right h c), Nat.max_eq_left h]

public theorem Nat.min_assoc (a b c : Nat) : min (min a b) c = min a (min b c) :=
  Nat.le_antisymm
    (Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_left ..),
      Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left ..) (Nat.min_le_right ..), Nat.min_le_right ..⟩⟩)
    (Nat.le_min.mpr ⟨Nat.le_min.mpr ⟨Nat.min_le_left ..,
      Nat.le_trans (Nat.min_le_right ..) (Nat.min_le_left ..)⟩,
      Nat.le_trans (Nat.min_le_right ..) (Nat.min_le_right ..)⟩)

public theorem Nat.sub_min_sub_right (a b c : Nat) :
    min (a - c) (b - c) = min a b - c := by
  cases Nat.le_total a b with
  | inl h => rw [Nat.min_eq_left (Nat.sub_le_sub_right h c), Nat.min_eq_left h]
  | inr h => rw [Nat.min_eq_right (Nat.sub_le_sub_right h c), Nat.min_eq_right h]

public theorem List.ext_getElem : type_of% @_root_.List.ext_getElem := by
  intro α xs ys lengths atIndex
  apply List.ext_getElem?
  intro i
  by_cases hx : i < xs.length
  · have hy : i < ys.length := lengths ▸ hx
    exact (List.getElem?_eq_getElem hx).trans
      ((congrArg some (atIndex i hx hy)).trans (List.getElem?_eq_getElem hy).symm)
  · have hx := Nat.le_of_not_lt hx
    have hy : ys.length ≤ i := lengths ▸ hx
    exact (List.getElem?_eq_none hx).trans (List.getElem?_eq_none hy).symm

private theorem extractLoopList {α : Type u} (xs : _root_.Array α) (count start : Nat)
    (acc : _root_.Array α) :
    (_root_.Array.extract.loop xs count start acc).toList =
      acc.toList ++ (xs.toList.drop start).take count := by
  induction count generalizing start acc with
  | zero => rw [Array.extract_loop_zero, List.take_zero, List.append_nil]
  | succ count ih =>
    by_cases h : start < xs.size
    · rw [Array.extract_loop_succ h, ih, Array.toList_push, List.append_assoc,
        List.drop_eq_getElem_cons (l := xs.toList) h]
      rfl
    · have past : xs.toList.length ≤ start := Nat.le_of_not_lt h
      rw [Array.extract_loop_of_ge past, List.drop_eq_nil_of_le past, List.take_nil, List.append_nil]

public theorem Array.toList_extract : type_of% @_root_.Array.toList_extract := by
  intro α xs start stop
  unfold _root_.Array.extract _root_.List.extract
  rw [extractLoopList, Array.emptyWithCapacity_eq, Array.toList_empty, List.nil_append]
  change (xs.toList.drop start).take (min stop xs.size - start) = _
  by_cases h : stop ≤ xs.size
  · rw [Nat.min_eq_left h]
  · have past := Nat.le_of_not_le h
    rw [Nat.min_eq_right past]
    have len : (xs.toList.drop start).length = xs.size - start := List.length_drop
    exact (List.take_of_length_le (Nat.le_of_eq len)).trans
      (List.take_of_length_le (Nat.le_trans (Nat.le_of_eq len) (Nat.sub_le_sub_right past start))).symm

public theorem Array.extract_size : type_of% @_root_.Array.extract_size := by
  intro α xs
  apply Array.ext'
  exact Array.toList_extract.trans (show (xs.toList.drop 0).take (xs.size - 0) = xs.toList from
    @List.take_length α xs.toList)

public theorem Array.extract_eq_empty_of_le :
    type_of% @_root_.Array.extract_eq_empty_of_le := by
  intro α stop xs start h
  apply Array.eq_empty_of_size_eq_zero
  exact Array.size_extract.trans (Nat.sub_eq_zero_of_le h)

public theorem ByteArray.data_extract :
    type_of% @_root_.ByteArray.data_extract := by
  intro a b e
  change #[] ++ a.data.extract b (b + (e - b)) ++ (#[] : Array UInt8).extract _ _ = a.data.extract b e
  rw [Array.extract_empty, Array.append_empty, Array.empty_append]
  cases Nat.le_total b e with
  | inl h => rw [Nat.add_comm, Nat.sub_add_cancel h]
  | inr h =>
    rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Array.extract_eq_empty_of_le (Nat.min_le_left ..),
      Array.extract_eq_empty_of_le (Nat.le_trans (Nat.min_le_left ..) h)]

public theorem ByteArray.extract_same :
    type_of% @_root_.ByteArray.extract_same := by
  intro b i
  apply ByteArray.ext
  exact ByteArray.data_extract.trans (Array.extract_eq_empty_of_le (Nat.min_le_left ..))

public theorem ByteArray.extract_zero_size : type_of% @_root_.ByteArray.extract_zero_size := by
  intro b
  apply ByteArray.ext
  exact ByteArray.data_extract.trans Array.extract_size

public theorem ByteArray.extract_eq_empty_iff : type_of% @_root_.ByteArray.extract_eq_empty_iff := by
  intro b i j
  exact Iff.trans ByteArray.size_eq_zero_iff.symm
    ⟨fun h => Nat.le_of_sub_eq_zero (ByteArray.size_extract.symm.trans h),
      fun h => ByteArray.size_extract.trans (Nat.sub_eq_zero_of_le h)⟩

end OmegaChecks.InitPort.Alternatives

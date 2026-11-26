module
public import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Extract

namespace OmegaChecks.InitPort.Alternatives

public theorem Nat.min_zero (a : Nat) : min a 0 = 0 := Nat.min_eq_right (Nat.zero_le a)

public theorem Nat.zero_min (a : Nat) : min 0 a = 0 := Nat.min_eq_left (Nat.zero_le a)

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

end OmegaChecks.InitPort.Alternatives

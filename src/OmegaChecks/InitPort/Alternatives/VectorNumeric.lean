module
public import OmegaChecks.InitPort.Alternatives.ListFinRange
public import Init.Data.Vector.Int
public import Init.Data.Vector.Nat
public import Init.Data.Vector.Count
public import Init.Data.Vector.Extract
import all Init.Data.Vector.FinRange
public import Init.Data.Vector.Range
/-! Folds, finite ranges, and arithmetic of vector entries. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem Vector.sum_eq_foldl_nat : type_of% @_root_.Vector.sum_eq_foldl_nat := by
  intros
  rw [← Vector.sum_toList, ← Vector.foldl_toList]
  exact List.sum_eq_foldl_nat

public theorem Vector.prod_eq_foldl_nat : type_of% @_root_.Vector.prod_eq_foldl_nat := by
  intros
  rw [← Vector.prod_toList, ← Vector.foldl_toList]
  exact List.prod_eq_foldl_nat

public theorem Vector.sum_eq_foldl_int : type_of% @_root_.Vector.sum_eq_foldl_int := by
  intros
  rw [← Vector.sum_toList, ← Vector.foldl_toList]
  exact List.sum_eq_foldl

public theorem Vector.prod_eq_foldl_int : type_of% @_root_.Vector.prod_eq_foldl_int := by
  intros
  rw [← Vector.prod_toList, ← Vector.foldl_toList]
  exact List.prod_eq_foldl

public theorem Vector.sum_eq_zero_iff_forall_eq_nat : type_of% @_root_.Vector.sum_eq_zero_iff_forall_eq_nat := by
  intros
  rw [← Vector.sum_toList, List.sum_eq_zero_iff_forall_eq_nat]
  exact ⟨fun h x mem => h x (Vector.mem_toList_iff.mpr mem), fun h x mem => h x (Vector.mem_toList_iff.mp mem)⟩

public theorem Vector.prod_eq_zero_iff_exists_zero_nat : type_of% @_root_.Vector.prod_eq_zero_iff_exists_zero_nat := by
  intros
  rw [← Vector.prod_toList, List.prod_eq_zero_iff_exists_zero_nat]
  exact ⟨fun ⟨x, mem, e⟩ => ⟨x, Vector.mem_toList_iff.mp mem, e⟩,
    fun ⟨x, mem, e⟩ => ⟨x, Vector.mem_toList_iff.mpr mem, e⟩⟩

public theorem Vector.extract_append_left : type_of% @_root_.Vector.extract_append_left := by
  intro α n m xs ys
  apply Vector.toArray_inj.mp
  rcases xs with ⟨xs, rfl⟩
  exact Array.extract_append_left
public theorem Vector.map_sub_range' : type_of% @_root_.Vector.map_sub_range' := by
  intro step a s h n
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_map, Vector.toArray_range', Vector.toArray_range']
  exact Array.map_sub_range' h n

public theorem Vector.finRange_succ : type_of% @_root_.Vector.finRange_succ := by
  intro n
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_finRange, Vector.getElem_cast, Vector.getElem_append]
  cases i with
  | zero => rfl
  | succ j =>
    rw [dite_eq_right (Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le j))), Vector.getElem_map,
      Vector.getElem_finRange]
    rfl

public theorem Vector.size_eq_countP_add_countP :
    type_of% @_root_.Vector.size_eq_countP_add_countP := by
  rintro α p n ⟨xs, rfl⟩
  exact Array.size_eq_countP_add_countP

public theorem Vector.countP_le_size : type_of% @_root_.Vector.countP_le_size := by
  rintro α p n ⟨xs, rfl⟩
  exact Array.countP_le_size

public theorem Vector.countP_replace : type_of% @_root_.Vector.countP_replace := by
  rintro α inst lawful n a b ⟨xs, rfl⟩ p
  exact Array.countP_replace

public theorem Vector.count_replace : type_of% @_root_.Vector.count_replace := by
  rintro α inst lawful n a b c ⟨xs, rfl⟩
  exact Array.count_replace

end OmegaChecks.InitPort.Alternatives

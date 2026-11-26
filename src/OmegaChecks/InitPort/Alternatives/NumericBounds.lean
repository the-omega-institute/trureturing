module
public import OmegaChecks.InitPort.Alternatives.SequenceExtrema
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Int.Sum
public import Init.Data.Array.Nat
public import Init.Data.Array.Int
/-! Sums, products, and bounds on arithmetic means of finite sequences. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.min_le_sum_div_length_nat : type_of% @_root_.List.min_le_sum_div_length_nat := by
  intro xs h
  exact (Nat.le_div_iff_mul_le (List.length_pos_iff.mpr h)).mpr (List.min_mul_length_le_sum_nat h)

public theorem List.le_sum_div_length_of_min?_eq_some_nat : type_of% @_root_.List.le_sum_div_length_of_min?_eq_some_nat := by
  intro x xs h
  have nz : xs ≠ [] := fun e => by cases e; cases h
  exact (Nat.le_div_iff_mul_le (List.length_pos_iff.mpr nz)).mpr (List.mul_length_le_sum_of_min?_eq_some_nat h)

public theorem List.sum_div_length_le_max_nat : type_of% @_root_.List.sum_div_length_le_max_nat := by
  intro xs h
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  exact List.sum_le_max_mul_length_nat h

public theorem List.sum_div_length_le_max_of_max?_eq_some_nat : type_of% @_root_.List.sum_div_length_le_max_of_max?_eq_some_nat := by
  intro x xs h
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm]
  exact List.sum_le_max_mul_length_of_max?_eq_some_nat h

public theorem Array.sum_eq_foldl_nat : type_of% @_root_.Array.sum_eq_foldl_nat := by
  intros
  exact Array.sum_eq_foldl

public theorem Array.prod_eq_foldl_nat : type_of% @_root_.Array.prod_eq_foldl_nat := by
  intros
  exact Array.prod_eq_foldl

public theorem Array.sum_eq_foldl_int : type_of% @_root_.Array.sum_eq_foldl_int := by
  intros
  exact Array.sum_eq_foldl

public theorem Array.prod_eq_foldl_int : type_of% @_root_.Array.prod_eq_foldl_int := by
  intros
  exact Array.prod_eq_foldl

public theorem Array.sum_eq_zero_iff_forall_eq_nat : type_of% @_root_.Array.sum_eq_zero_iff_forall_eq_nat := by
  intros
  rw [← Array.sum_toList, List.sum_eq_zero_iff_forall_eq_nat]
  exact ⟨fun h x mem => h x (Array.mem_toList_iff.mpr mem), fun h x mem => h x (Array.mem_toList_iff.mp mem)⟩

public theorem Array.prod_eq_zero_iff_exists_zero_nat : type_of% @_root_.Array.prod_eq_zero_iff_exists_zero_nat := by
  intros
  rw [← Array.prod_toList, List.prod_eq_zero_iff_exists_zero_nat]
  exact ⟨fun ⟨x, mem, e⟩ => ⟨x, Array.mem_toList_iff.mp mem, e⟩,
    fun ⟨x, mem, e⟩ => ⟨x, Array.mem_toList_iff.mpr mem, e⟩⟩

private theorem lowerSum (bound : Int) (xs : List Int) (holds : ∀ x ∈ xs, bound ≤ x) :
    bound * (xs.length : Int) ≤ xs.sum := by
  induction xs with
  | nil => simp only [List.length_nil, List.sum_nil, Int.ofNat_zero, Int.mul_zero]; exact Int.le_refl _
  | cons x xs ih =>
    rw [List.sum_cons, List.length_cons, Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_comm (bound * _)]
    exact Int.add_le_add (holds _ (.head _)) (ih (fun y mem => holds y (.tail _ mem)))

public theorem List.min_mul_length_le_sum_int : type_of% @_root_.List.min_mul_length_le_sum_int := by
  intro xs h
  letI : Std.IsLinearOrder Int := Int.instIsLinearOrder
  letI : Std.LawfulOrderMin Int := {
    min_eq_or := fun a b => by
      by_cases h : a ≤ b
      · exact .inl (Int.min_eq_left h)
      · exact .inr (Int.min_eq_right (Int.le_of_lt (Int.lt_of_not_ge h)))
    le_min_iff := fun _ _ _ => Int.le_min }
  exact lowerSum _ xs (fun _ mem => List.min_le_of_mem mem)

public theorem List.mul_length_le_sum_of_min?_eq_some_int : type_of% @_root_.List.mul_length_le_sum_of_min?_eq_some_int := by
  intro x xs h
  have nz : xs ≠ [] := fun e => by cases e; cases h
  have eq := Option.some.inj ((List.min?_eq_some_min nz).symm.trans h)
  rw [← eq]
  exact _root_.List.min_mul_length_le_sum_int nz

public theorem List.min_le_sum_div_length_int : type_of% @_root_.List.min_le_sum_div_length_int := by
  intro xs h
  exact Int.le_ediv_of_mul_le (Int.natCast_pos.mpr (List.length_pos_iff.mpr h)) (_root_.List.min_mul_length_le_sum_int h)

public theorem List.le_sum_div_length_of_min?_eq_some_int : type_of% @_root_.List.le_sum_div_length_of_min?_eq_some_int := by
  intro x xs h
  have nz : xs ≠ [] := fun e => by cases e; cases h
  exact Int.le_ediv_of_mul_le (Int.natCast_pos.mpr (List.length_pos_iff.mpr nz)) (_root_.List.mul_length_le_sum_of_min?_eq_some_int h)

private theorem upperSum (bound : Int) (xs : List Int) (holds : ∀ x ∈ xs, x ≤ bound) :
    xs.sum ≤ bound * (xs.length : Int) := by
  induction xs with
  | nil => simp only [List.length_nil, List.sum_nil, Int.ofNat_zero, Int.mul_zero]; exact Int.le_refl _
  | cons x xs ih =>
    rw [List.sum_cons, List.length_cons, Int.natCast_succ, Int.mul_add, Int.mul_one, Int.add_comm (bound * _)]
    exact Int.add_le_add (holds _ (.head _)) (ih (fun y mem => holds y (.tail _ mem)))

public theorem List.sum_le_max_mul_length_int : type_of% @_root_.List.sum_le_max_mul_length_int := by
  intro xs h
  letI : Std.IsLinearOrder Int := Int.instIsLinearOrder
  letI : Std.LawfulOrderMax Int := {
    max_eq_or := fun a b => by
      by_cases h : b ≤ a
      · exact .inl (Int.max_eq_left h)
      · exact .inr (Int.max_eq_right (Int.le_of_lt (Int.lt_of_not_ge h)))
    max_le_iff := fun _ _ _ => Int.max_le }
  exact upperSum _ xs (fun _ mem => List.le_max_of_mem mem)

public theorem List.sum_le_max_mul_length_of_max?_eq_some_int : type_of% @_root_.List.sum_le_max_mul_length_of_max?_eq_some_int := by
  intro x xs h
  have nz : xs ≠ [] := fun e => by cases e; cases h
  have eq := Option.some.inj ((List.max?_eq_some_max nz).symm.trans h)
  rw [← eq]
  exact _root_.List.sum_le_max_mul_length_int nz

public theorem List.sum_div_length_le_max_int : type_of% @_root_.List.sum_div_length_le_max_int := by
  intro xs h
  exact Int.ediv_le_of_le_mul (Int.natCast_pos.mpr (List.length_pos_iff.mpr h)) (_root_.List.sum_le_max_mul_length_int h)

public theorem List.sum_div_length_le_max_of_max?_eq_some_int : type_of% @_root_.List.sum_div_length_le_max_of_max?_eq_some_int := by
  intro x xs h
  have nz : xs ≠ [] := fun e => by cases e; cases h
  exact Int.ediv_le_of_le_mul (Int.natCast_pos.mpr (List.length_pos_iff.mpr nz)) (_root_.List.sum_le_max_mul_length_of_max?_eq_some_int h)
end OmegaChecks.InitPort.Alternatives

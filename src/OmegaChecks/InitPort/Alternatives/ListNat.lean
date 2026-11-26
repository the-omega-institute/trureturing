module
public import OmegaChecks.InitPort.Alternatives.NumericBounds
public import Init.Data.List.Nat.Count
public import Init.Data.List.Nat.Prod
public import Init.Data.List.Nat.Sum
public import Init.Data.List.Nat.Pairwise
public import Init.Data.List.Nat.Sublist

/-! Products, counts, and natural index witnesses for ordered sublists. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.count_replace : type_of% @_root_.List.count_replace := by
  intro α _ _ a b c xs
  exact List.countP_replace (p := (· == c))

public theorem List.prod_eq_foldl_nat : type_of% @_root_.List.prod_eq_foldl_nat := by
  intro xs
  have fold (ys : List Nat) (a : Nat) : ys.foldl (· * ·) a = a * ys.prod := by
    induction ys generalizing a with
    | nil => exact (Nat.mul_one a).symm
    | cons y ys ih => exact (ih (a * y)).trans (Nat.mul_assoc ..)
  exact (Nat.one_mul _).symm.trans (fold xs 1).symm

public theorem List.prod_eq_zero_iff_exists_zero_nat : type_of% @_root_.List.prod_eq_zero_iff_exists_zero_nat := by
  intro xs
  induction xs with
  | nil => exact ⟨fun eq => (nomatch eq), fun ⟨_, mem, _⟩ => (nomatch mem)⟩
  | cons x xs ih =>
    rw [List.prod_cons, Nat.mul_eq_zero]
    constructor
    · rintro (eq | eq)
      · exact ⟨x, .head _, eq⟩
      · obtain ⟨a, mem, eq⟩ := ih.mp eq
        exact ⟨a, .tail _ mem, eq⟩
    · rintro ⟨a, mem, eq⟩
      cases mem with
      | head => exact .inl eq
      | tail _ mem => exact .inr (ih.mpr ⟨a, mem, eq⟩)

public theorem List.prefix_take_iff : type_of% @_root_.List.prefix_take_iff := by
  intro α xs ys i
  constructor
  · intro h
    exact ⟨h.trans (List.take_prefix i ys), Nat.le_trans h.length_le (List.length_take_le _ _)⟩
  · rintro ⟨hp, hi⟩
    apply List.prefix_iff_eq_take.mpr
    rw [List.take_take, Nat.min_eq_left hi]
    exact List.prefix_iff_eq_take.mp hp

public theorem List.prefix_map_iff_of_injective : type_of% @_root_.List.prefix_map_iff_of_injective := by
  intro α β xs ys f inj
  constructor
  · intro h
    have eq := List.prefix_iff_eq_take.mp h
    rw [List.length_map, ← List.map_take] at eq
    exact List.prefix_iff_eq_take.mpr ((List.map_inj_right inj).mp eq)
  · exact fun h => h.map f

public theorem List.suffix_map_iff_of_injective : type_of% @_root_.List.suffix_map_iff_of_injective := by
  intro α β xs ys f inj
  constructor
  · intro h
    have eq := List.suffix_iff_eq_drop.mp h
    rw [List.length_map, List.length_map, ← List.map_drop] at eq
    exact List.suffix_iff_eq_drop.mpr ((List.map_inj_right inj).mp eq)
  · exact fun h => h.map f

public theorem List.sublist_eq_map_getElem : type_of% @_root_.List.sublist_eq_map_getElem := by
  intro α xs ys h
  induction h with
  | slnil => exact ⟨[], rfl, .nil⟩
  | @cons xs ys a sub ih =>
    obtain ⟨is, eq, pairs⟩ := ih
    refine ⟨is.map Fin.succ, ?_, ?_⟩
    · rw [List.map_map]
      exact eq
    · exact List.pairwise_map.mpr (pairs.imp (fun h => Nat.succ_lt_succ h))
  | @cons_cons xs ys a sub ih =>
    obtain ⟨is, eq, pairs⟩ := ih
    refine ⟨⟨0, Nat.zero_lt_succ _⟩ :: is.map Fin.succ, ?_, ?_⟩
    · rw [List.map_cons, List.map_map]
      exact congrArg (a :: ·) eq
    · constructor
      · intro j mem
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
        exact Nat.zero_lt_succ i.val
      · exact List.pairwise_map.mpr (pairs.imp (fun h => Nat.succ_lt_succ h))

public theorem List.sum_eq_foldl_nat : type_of% @_root_.List.sum_eq_foldl_nat := by
  intros
  exact List.sum_eq_foldl

public theorem List.sum_eq_zero_iff_forall_eq_nat : type_of% @_root_.List.sum_eq_zero_iff_forall_eq_nat := by
  intro xs
  induction xs with
  | nil => exact ⟨fun _ _ mem => (nomatch mem), fun _ => rfl⟩
  | cons x xs ih =>
    rw [List.sum_cons, Nat.add_eq_zero_iff]
    constructor
    · rintro ⟨head, rest⟩ a ha
      cases ha with
      | head => exact head
      | tail _ mem => exact ih.mp rest _ mem
    · intro all
      exact ⟨all _ (.head _), ih.mpr (fun a ha => all a (.tail _ ha))⟩

public theorem List.getElem?_intersperse_two_mul_add_one : type_of% @_root_.List.getElem?_intersperse_two_mul_add_one := by
  intro α l sep i h
  induction l generalizing i with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | cons a tail ih =>
    cases tail with
    | nil => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ h)).elim
    | cons b xs =>
      cases i with
      | zero => rfl
      | succ i =>
        rw [Nat.mul_succ]
        exact ih (Nat.lt_of_succ_lt_succ h)

end OmegaChecks.InitPort.Alternatives

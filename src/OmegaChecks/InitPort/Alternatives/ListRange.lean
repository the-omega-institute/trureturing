module
public import Init.Data.List.Nat.Range

/-! Constructive membership, order and counting proofs for finite arithmetic progressions. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.mem_range' : type_of% @_root_.List.mem_range' := by
  intro s step m n
  constructor
  · intro mem
    obtain ⟨i, within, value⟩ := _root_.List.mem_iff_getElem.mp mem
    exact ⟨i, Nat.lt_of_lt_of_eq within _root_.List.length_range',
      value.symm.trans (_root_.List.getElem_range' within)⟩
  · rintro ⟨i, bound, rfl⟩
    exact _root_.List.mem_iff_getElem?.mpr ⟨i, _root_.List.getElem?_range' bound⟩

public theorem List.mem_range'_1 : type_of% @_root_.List.mem_range'_1 := by
  intro s n m
  constructor
  · intro h
    obtain ⟨i, hi, eq⟩ := _root_.List.mem_range'.mp h
    rw [Nat.one_mul] at eq
    exact eq ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left hi _⟩
  · intro ⟨lo, hi⟩
    apply _root_.List.mem_range'.mpr
    exact ⟨m - s, Nat.sub_lt_left_of_lt_add lo hi, by rw [Nat.one_mul, Nat.add_sub_cancel' lo]⟩

public theorem List.mem_range : type_of% @_root_.List.mem_range := by
  intro m n
  rw [_root_.List.range_eq_range']
  exact ⟨fun h => (Nat.zero_add n) ▸ (List.mem_range'_1.mp h).2,
    fun h => List.mem_range'_1.mpr ⟨Nat.zero_le _, (Nat.zero_add n).symm ▸ h⟩⟩

public theorem List.not_mem_range_self : type_of% @_root_.List.not_mem_range_self := by
  intro n h
  exact (Nat.lt_irrefl n) (List.mem_range.mp h)

public theorem List.self_mem_range_succ : type_of% @_root_.List.self_mem_range_succ := by
  intro n
  exact List.mem_range.mpr (Nat.lt_succ_self _)

private theorem rangeLower {s n step x : Nat} (h : x ∈ _root_.List.range' s n step) : s ≤ x := by
  obtain ⟨i, _, eq⟩ := _root_.List.mem_range'.mp h
  exact eq ▸ Nat.le_add_right ..

public theorem List.pairwise_lt_range' : type_of% @_root_.List.pairwise_lt_range' := by
  intro s n step pos
  induction n generalizing s with
  | zero => exact .nil
  | succ n ih =>
    rw [_root_.List.range'_succ]
    exact .cons (fun x h => Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right pos) (rangeLower h)) ih

public theorem List.pairwise_le_range' : type_of% @_root_.List.pairwise_le_range' := by
  intro s n step
  induction n generalizing s with
  | zero => exact .nil
  | succ n ih =>
    rw [_root_.List.range'_succ]
    exact .cons (fun x h => Nat.le_trans (Nat.le_add_right ..) (rangeLower h)) ih

public theorem List.pairwise_lt_range : type_of% @_root_.List.pairwise_lt_range := by
  intro n
  rw [_root_.List.range_eq_range']
  exact List.pairwise_lt_range' 1 (Nat.zero_lt_succ 0)

public theorem List.nodup_range : type_of% @_root_.List.nodup_range := by
  intro n
  exact List.pairwise_lt_range.imp Nat.ne_of_lt

private theorem countWhen {α : Type u} [BEq α] [LawfulBEq α] {a : α} {xs : _root_.List α}
    (unique : xs.Nodup) {p : Prop} [Decidable p] (member : a ∈ xs ↔ p) :
    xs.count a = if p then 1 else 0 := by
  rw [unique.count]
  by_cases h : p
  · rw [ite_eq_left h, ite_eq_left (member.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hm => h (member.mp hm))]

public theorem List.count_range : type_of% @_root_.List.count_range := by
  intros
  exact countWhen List.nodup_range List.mem_range

public theorem List.count_range_1' : type_of% @_root_.List.count_range_1' := by
  intros
  exact countWhen ((List.pairwise_lt_range' 1 (Nat.zero_lt_succ 0)).imp Nat.ne_of_lt) List.mem_range'_1

public theorem List.count_range' : type_of% @_root_.List.count_range' := by
  intro a s n step h
  exact countWhen ((List.pairwise_lt_range' step h).imp Nat.ne_of_lt) _root_.List.mem_range'

public theorem List.zipIdx_map : type_of% @_root_.List.zipIdx_map := by
  intros
  exact _root_.List.map_zipIdx.symm

public theorem List.map_sub_range' : type_of% @_root_.List.map_sub_range' := by
  intro step a s le n
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [_root_.List.range'_succ, _root_.List.map_cons, ih (Nat.le_trans le (Nat.le_add_right ..)),
      _root_.List.range'_succ]
    have e : s + step - a = s - a + step := by omega
    rw [e]

public theorem List.range'_eq_append_iff : type_of% @_root_.List.range'_eq_append_iff := by
  intro s n step xs ys
  constructor
  · intro h
    have len := congrArg _root_.List.length h
    rw [_root_.List.length_range', _root_.List.length_append] at len
    have bound : xs.length ≤ n := len ▸ Nat.le_add_right ..
    have left := congrArg (_root_.List.take xs.length) h
    have right := congrArg (_root_.List.drop xs.length) h
    rw [_root_.List.take_left, _root_.List.take_range'_of_length_ge bound] at left
    rw [_root_.List.drop_left, _root_.List.drop_range'] at right
    exact ⟨xs.length, bound, left.symm, right.symm⟩
  · rintro ⟨k, bound, rfl, rfl⟩
    have h := _root_.List.take_append_drop k (_root_.List.range' s n step)
    rw [_root_.List.take_range'_of_length_ge bound, _root_.List.drop_range'] at h
    exact h.symm

private theorem zipLower {xs : _root_.List α} {x : α} {i k : Nat}
    (h : (x,i) ∈ xs.zipIdx k) : k ≤ i := by
  induction xs generalizing k with
  | nil => cases h
  | cons a as ih =>
    cases h with
    | head => exact Nat.le_refl _
    | tail _ ht => exact Nat.le_trans (Nat.le_succ k) (ih ht)

public theorem List.mk_mem_zipIdx_iff_le_and_getElem?_sub :
    type_of% @_root_.List.mk_mem_zipIdx_iff_le_and_getElem?_sub := by
  intro α k i x l
  constructor
  · intro mem
    have h := zipLower mem
    exact ⟨h, _root_.List.mk_add_mem_zipIdx_iff_getElem?.mp
      ((Nat.add_sub_cancel' h).symm ▸ mem)⟩
  · intro ⟨h, value⟩
    exact (Nat.add_sub_cancel' h) ▸ _root_.List.mk_add_mem_zipIdx_iff_getElem?.mpr value

public theorem List.mk_mem_zipIdx_iff_getElem? : type_of% @_root_.List.mk_mem_zipIdx_iff_getElem? := by
  intros
  exact ⟨fun h => (List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mp h).2,
    fun value => List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr ⟨Nat.zero_le _, value⟩⟩

public theorem List.mem_zipIdx_iff_le_and_getElem?_sub : type_of% @_root_.List.mem_zipIdx_iff_le_and_getElem?_sub := by
  intro α x l k
  cases x
  exact List.mk_mem_zipIdx_iff_le_and_getElem?_sub

public theorem List.mem_zipIdx_iff_getElem? : type_of% @_root_.List.mem_zipIdx_iff_getElem? := by
  intro α x l
  cases x
  exact List.mk_mem_zipIdx_iff_getElem?

public theorem List.zipIdx_eq_cons_iff : type_of% @_root_.List.zipIdx_eq_cons_iff := by
  intro α x l' l k
  constructor
  · intro h
    cases l with
    | nil => cases h
    | cons a as =>
      obtain ⟨head, tail⟩ := _root_.List.cons.inj h
      exact ⟨a, as, rfl, head.symm, tail.symm⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    rfl

private theorem notBool (b : Bool) : (b ≠ true) ↔ (!b) = true := by
  cases b with
  | false => exact ⟨fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | true => exact ⟨fun h => (h rfl).elim, fun h => Bool.noConfusion h⟩

public theorem List.find?_range'_eq_none : type_of% @_root_.List.find?_range'_eq_none := by
  intro s n p
  constructor
  · intro none i lo hi
    exact (notBool _).mp (_root_.List.find?_eq_none.mp none i (List.mem_range'_1.mpr ⟨lo, hi⟩))
  · intro reject
    apply _root_.List.find?_eq_none.mpr
    intro i mem
    obtain ⟨lo, hi⟩ := List.mem_range'_1.mp mem
    exact (notBool _).mpr (reject i lo hi)

public theorem List.find?_range_eq_none : type_of% @_root_.List.find?_range_eq_none := by
  intro n p
  constructor
  · intro none i hi
    exact (notBool _).mp (_root_.List.find?_eq_none.mp none i (List.mem_range.mpr hi))
  · intro reject
    exact _root_.List.find?_eq_none.mpr (fun i mem => (notBool _).mpr (reject i (List.mem_range.mp mem)))

public theorem List.getLast_range' : type_of% @_root_.List.getLast_range' := by
  intro s n nonempty
  apply (_root_.List.getLast_eq_iff_getLast?_eq_some nonempty).mpr
  rw [_root_.List.getLast?_range', ite_eq_right]
  intro zero
  subst n
  exact nonempty rfl

end OmegaChecks.InitPort.Alternatives

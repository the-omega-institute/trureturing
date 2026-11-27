module
import Init.Data.Array.Range
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

public theorem List.find?_range'_eq_some : type_of% @_root_.List.find?_range'_eq_some := by
  intro s n i p
  induction n generalizing s with
  | zero =>
    constructor
    · intro none
      cases none
    · intro ⟨_, mem, _⟩
      cases mem
  | succ n ih =>
    rw [_root_.List.range'_succ]
    by_cases test : p s = true
    · rw [_root_.List.find?_cons_of_pos test]
      constructor
      · intro hit
        cases Option.some.inj hit
        exact ⟨test, .head _, fun j lo hi => (Nat.not_lt_of_ge lo hi).elim⟩
      · intro ⟨_, mem, before⟩
        cases mem with
        | head => rfl
        | tail _ tail =>
          have lo := (List.mem_range'_1.mp tail).1
          exact ((notBool _).mpr (before s (Nat.le_refl _) lo) test).elim
    · rw [_root_.List.find?_cons_of_neg test]
      constructor
      · intro hit
        obtain ⟨atIndex, mem, before⟩ := ih.mp hit
        refine ⟨atIndex, .tail _ mem, fun j lo hi => ?_⟩
        cases Nat.eq_or_lt_of_le lo with
        | inl eq => exact eq ▸ (notBool _).mp test
        | inr lt => exact before j lt hi
      · intro ⟨atIndex, mem, before⟩
        apply ih.mpr
        cases mem with
        | head => exact (test atIndex).elim
        | tail _ tail => exact ⟨atIndex, tail, fun j lo => before j (Nat.le_trans (Nat.le_succ _) lo)⟩

public theorem List.find?_range_eq_some : type_of% @_root_.List.find?_range_eq_some := by
  intro n i p
  rw [_root_.List.range_eq_range']
  constructor
  · intro hit
    obtain ⟨yes, mem, before⟩ := List.find?_range'_eq_some.mp hit
    exact ⟨yes, mem, fun j => before j (Nat.zero_le _)⟩
  · intro ⟨yes, mem, before⟩
    exact List.find?_range'_eq_some.mpr ⟨yes, mem, fun j _ => before j⟩

public theorem List.zipIdx_eq_append_iff : type_of% @_root_.List.zipIdx_eq_append_iff := by
  intro α l₁ l₂ l k
  constructor
  · intro split
    induction l₁ generalizing l k with
    | nil => exact ⟨[], l, rfl, rfl, split.symm⟩
    | cons x xs ih =>
      obtain ⟨a, as, rfl, rfl, tail⟩ := List.zipIdx_eq_cons_iff.mp split
      obtain ⟨front, back, rfl, left, right⟩ := ih tail.symm
      refine ⟨a :: front, back, rfl, congrArg (_ :: ·) left, ?_⟩
      rw [right, _root_.List.length_cons]
      apply congrArg (back.zipIdx ·)
      omega
  · rintro ⟨as, bs, rfl, rfl, rfl⟩
    exact _root_.List.zipIdx_append

public theorem List.reverse_range' : type_of% @_root_.List.reverse_range' := by
  intro s n
  apply _root_.List.ext_getElem
  · rw [_root_.List.length_reverse, _root_.List.length_map, _root_.List.length_range', _root_.List.length_range]
  · intro i ha hb
    rw [_root_.List.getElem_reverse, _root_.List.getElem_range', _root_.List.getElem_map,
      _root_.List.getElem_range, Nat.one_mul]
    rw [_root_.List.length_map, _root_.List.length_range] at hb
    rw [_root_.List.length_range']
    omega

public theorem List.getLast?_zipIdx : type_of% @_root_.List.getLast?_zipIdx := by
  intro α l k
  induction l generalizing k with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => simp only [_root_.List.zipIdx_cons, _root_.List.zipIdx_nil, _root_.List.getLast?_singleton,
        Option.map_some, _root_.List.length_cons, _root_.List.length_nil, Nat.add_one_sub_one]
    | cons b bs =>
      rw [_root_.List.zipIdx_cons, _root_.List.zipIdx_cons, _root_.List.getLast?_cons_cons,
        ← _root_.List.zipIdx_cons, ih, _root_.List.getLast?_cons_cons]
      have e : k + 1 + (b :: bs).length - 1 = k + (a :: b :: bs).length - 1 := by
        simp only [_root_.List.length_cons]
        omega
      rw [e]

public theorem List.erase_range' : type_of% @_root_.List.erase_range' := by
  intro s n i
  induction n generalizing s with
  | zero =>
    rw [Nat.zero_min]
    have h : min s (i + 1) + 0 - (i + 1) = 0 := Nat.sub_eq_zero_of_le (Nat.min_le_right ..)
    rw [h]
    rfl
  | succ n ih =>
    rw [_root_.List.range'_succ]
    by_cases eq : s = i
    · subst i
      rw [_root_.List.erase_cons_head]
      simp only [Nat.sub_self, Nat.min_zero, Nat.max_eq_right (Nat.le_succ s),
        Nat.min_eq_left (Nat.le_succ s)]
      have len : s + (n + 1) - (s + 1) = n := by omega
      rw [len]
      rfl
    · by_cases before : i < s
      · have absent : i ∉ _root_.List.range' s (n+1) :=
          fun mem => (Nat.not_le_of_gt before) (List.mem_range'_1.mp mem).1
        rw [← _root_.List.range'_succ, _root_.List.erase_of_not_mem absent,
          Nat.sub_eq_zero_of_le (Nat.le_of_lt before), Nat.min_zero,
          Nat.max_eq_left before, Nat.min_eq_right before, Nat.add_sub_cancel_left]
        rfl
      · have after := Nat.lt_of_le_of_ne (Nat.le_of_not_gt before) eq
        have ne : ¬(s == i) := fun h => eq (eq_of_beq h)
        rw [_root_.List.erase_cons_tail ne, ih]
        have len : min (n+1) (i-s) = min n (i-(s+1)) + 1 := by omega
        rw [len, _root_.List.range'_succ]
        have maxEq : max (s+1) (i+1) = max s (i+1) := by omega
        have minEq : min (s+1) (i+1) + n = min s (i+1) + (n+1) := by omega
        rw [maxEq, minEq]
        rfl

public theorem List.erase_range : type_of% @_root_.List.erase_range := by
  intros
  simp only [_root_.List.range_eq_range', List.erase_range', Nat.sub_zero, Nat.zero_max,
    Nat.zero_min, Nat.zero_add]


public theorem Array.range_eq_range' : type_of% @_root_.Array.range_eq_range' := by
  intro n
  exact _root_.Array.ext' (_root_.Array.toList_range.trans
    (_root_.List.range_eq_range'.trans _root_.Array.toList_range'.symm))

public theorem Array.mem_range : type_of% @_root_.Array.mem_range := by
  intros
  exact _root_.Array.mem_toList_iff.symm.trans (_root_.Array.toList_range ▸ _root_.List.mem_range)


public theorem Array.range_ne_empty_iff : type_of% @_root_.Array.range_ne_empty_iff := by
  intros
  exact not_congr _root_.Array.range_eq_empty_iff

public theorem Array.range'_ne_empty_iff : type_of% @_root_.Array.range'_ne_empty_iff := by
  intros
  exact not_congr _root_.Array.range'_eq_empty_iff

public theorem Array.map_sub_range' : type_of% @_root_.Array.map_sub_range' := by
  intros
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_range', _root_.Array.toList_range']
  exact _root_.List.map_sub_range' ‹_› _

public theorem List.map_snd_add_zipIdx_eq_zipIdx : type_of% @_root_.List.map_snd_add_zipIdx_eq_zipIdx := by
  intro α xs n k
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih =>
    rw [_root_.List.zipIdx_cons, _root_.List.map_cons, _root_.List.zipIdx_cons, ih]
    exact congrArg (fun i => (a, i) :: xs.zipIdx (n + (k + 1))) (Nat.add_comm k n)

public theorem Array.map_snd_add_zipIdx_eq_zipIdx : type_of% @_root_.Array.map_snd_add_zipIdx_eq_zipIdx := by
  intros
  apply _root_.Array.ext'
  rw [_root_.Array.toList_map, _root_.Array.toList_zipIdx, _root_.Array.toList_zipIdx]
  exact List.map_snd_add_zipIdx_eq_zipIdx

public theorem List.range_ne_nil : type_of% @_root_.List.range_ne_nil := by
  intro n
  constructor
  · intro h e; subst n; exact h rfl
  · intro ne e; exact ne (List.length_range.symm.trans (congrArg List.length e))

public theorem List.range_succ_eq_map : type_of% @_root_.List.range_succ_eq_map := by
  intro n
  rw [List.range_eq_range', List.range']
  apply congrArg (0 :: ·)
  rw [List.range'_eq_map_range]
  exact List.map_congr_left (fun i _ => Nat.one_add i)

public theorem List.head_range : type_of% @_root_.List.head_range := by
  intro n h
  have nz := _root_.List.range_ne_nil.mp h
  apply Option.some.inj
  rw [← List.head?_eq_some_head h, List.head?_range, ite_eq_right nz]

public theorem List.getLast_range : type_of% @_root_.List.getLast_range := by
  intro n h
  have nz := _root_.List.range_ne_nil.mp h
  apply Option.some.inj
  rw [← List.getLast?_eq_some_getLast h, List.getLast?_range, ite_eq_right nz]

end OmegaChecks.InitPort.Alternatives

module
public import Init.Data.Array.Count
public import Init.Data.Array.Erase
public import Init.Data.Vector.Erase
import all Init.Data.List.Nat.Erase

/-! Transfer array erasure, counting, and update laws through the list representation. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.getElem?_eraseIdx : type_of% @_root_.List.getElem?_eraseIdx := by
  intro α xs i j
  induction xs generalizing i j with
  | nil => cases i <;> cases j <;> split <;> rfl
  | cons a xs ih =>
    cases i with
    | zero => rw [ite_eq_right (Nat.not_lt_zero _)]; rfl
    | succ i =>
      cases j with
      | zero => rw [ite_eq_left (Nat.zero_lt_succ _)]; rfl
      | succ j =>
        change (xs.eraseIdx i)[j]? = if j + 1 < i + 1 then xs[j]? else xs[j + 1]?
        by_cases lt : j < i
        · rw [ih, ite_eq_left lt, ite_eq_left (Nat.succ_lt_succ lt)]
        · rw [ih, ite_eq_right lt, ite_eq_right (fun h => lt (Nat.lt_of_succ_lt_succ h))]

public theorem List.eraseIdx_set_eq : type_of% @_root_.List.eraseIdx_set_eq := by
  intro α xs i a
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact congrArg (x :: ·) (ih (i := i))

public theorem List.eraseIdx_set_lt : type_of% @_root_.List.eraseIdx_set_lt := by
  intro α xs i j a lt
  induction xs generalizing i j with
  | nil => cases i <;> cases j <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => exact (Nat.not_lt_zero _ lt).elim
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        cases i with
        | zero => exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ lt)).elim
        | succ i => exact congrArg (x :: ·) (ih (Nat.lt_of_succ_lt_succ lt))

public theorem List.eraseIdx_set_gt : type_of% @_root_.List.eraseIdx_set_gt := by
  intro α xs i j a lt
  induction xs generalizing i j with
  | nil => cases i <;> cases j <;> rfl
  | cons x xs ih =>
    cases j with
    | zero => exact (Nat.not_lt_zero _ lt).elim
    | succ j =>
      cases i with
      | zero => rfl
      | succ i => exact congrArg (x :: ·) (ih (Nat.lt_of_succ_lt_succ lt))

public theorem List.set_eraseIdx_le : type_of% @_root_.List.set_eraseIdx_le := by
  intro α xs i j a le
  exact (List.eraseIdx_set_lt (l := xs) (a := a) (Nat.lt_succ_of_le le)).symm

public theorem List.set_eraseIdx_gt : type_of% @_root_.List.set_eraseIdx_gt := by
  intro α xs i j a lt
  exact (List.eraseIdx_set_gt (l := xs) (a := a) lt).symm

public theorem List.mem_eraseIdx_iff_getElem? : type_of% @_root_.List.mem_eraseIdx_iff_getElem? := by
  intro α x xs k
  induction xs generalizing k with
  | nil =>
    exact ⟨(fun h => nomatch h), (fun ⟨i, ne, h⟩ => nomatch h)⟩
  | cons a xs ih =>
    cases k with
    | zero =>
      constructor
      · intro mem
        obtain ⟨i, e⟩ := List.mem_iff_getElem?.mp mem
        exact ⟨i+1, Nat.succ_ne_zero _, e⟩
      · rintro ⟨i, ne, e⟩
        cases i with
        | zero => exact (ne rfl).elim
        | succ i => exact List.mem_iff_getElem?.mpr ⟨i, e⟩
    | succ k =>
      constructor
      · intro mem
        rcases List.mem_cons.mp mem with rfl | tail
        · exact ⟨0, Nat.zero_ne_add_one _, rfl⟩
        · obtain ⟨i, ne, e⟩ := (ih (k := k)).mp tail
          exact ⟨i+1, fun eq => ne (Nat.succ.inj eq), e⟩
      · rintro ⟨i, ne, e⟩
        cases i with
        | zero =>
          have same : a = x := Option.some.inj e
          exact same ▸ List.Mem.head _
        | succ i => exact List.Mem.tail _ ((ih (k := k)).mpr ⟨i, fun h => ne (congrArg Nat.succ h), e⟩)

public theorem List.mem_eraseIdx_iff_getElem : type_of% @_root_.List.mem_eraseIdx_iff_getElem := by
  intro α x xs k
  constructor
  · intro h
    obtain ⟨i, ne, v⟩ := List.mem_eraseIdx_iff_getElem?.mp h
    obtain ⟨hi, eq⟩ := _root_.List.getElem?_eq_some_iff.mp v
    exact ⟨i, hi, ne, eq⟩
  · intro ⟨i, hi, ne, eq⟩
    exact List.mem_eraseIdx_iff_getElem?.mpr ⟨i, ne, _root_.List.getElem?_eq_some_iff.mpr ⟨hi, eq⟩⟩

public theorem Array.getElem?_eraseIdx : type_of% @_root_.Array.getElem?_eraseIdx := by
  intros
  simp only [← _root_.Array.getElem?_toList, _root_.Array.toList_eraseIdx, _root_.List.getElem?_eraseIdx]

public theorem Array.getElem?_eraseIdx_of_lt : type_of% @_root_.Array.getElem?_eraseIdx_of_lt := by
  intro α xs i hi j lt
  rw [Array.getElem?_eraseIdx, ite_eq_left lt]

public theorem Array.getElem?_eraseIdx_of_ge : type_of% @_root_.Array.getElem?_eraseIdx_of_ge := by
  intro α xs i hi j le
  rw [Array.getElem?_eraseIdx, ite_eq_right (Nat.not_lt_of_ge le)]

public theorem Array.getElem_eraseIdx : type_of% @_root_.Array.getElem_eraseIdx := by
  intro α xs i hi j hj
  apply Option.some.inj
  rw [← _root_.getElem?_pos (xs.eraseIdx i hi) j hj, Array.getElem?_eraseIdx]
  by_cases lt : j < i
  · rw [ite_eq_left lt, dite_eq_left lt]
    exact _root_.getElem?_pos xs j (Nat.lt_trans lt hi)
  · rw [ite_eq_right lt, dite_eq_right lt]
    apply _root_.getElem?_pos

public theorem Array.eraseIdx_set_eq : type_of% @_root_.Array.eraseIdx_set_eq := by
  intros
  apply _root_.Array.ext'
  simp only [_root_.Array.toList_eraseIdx, _root_.Array.toList_set, _root_.List.eraseIdx_set_eq]

public theorem Array.eraseIdx_set_lt : type_of% @_root_.Array.eraseIdx_set_lt := by
  intro α xs i hi j a lt
  apply _root_.Array.ext'
  simpa only [_root_.Array.toList_eraseIdx, _root_.Array.toList_set] using
    (_root_.List.eraseIdx_set_lt (l := xs.toList) (a := a) lt)

public theorem Array.eraseIdx_set_gt : type_of% @_root_.Array.eraseIdx_set_gt := by
  intro α xs i j a lt hj
  apply _root_.Array.ext'
  simpa only [_root_.Array.toList_eraseIdx, _root_.Array.toList_set] using
    (_root_.List.eraseIdx_set_gt (l := xs.toList) (a := a) lt)

public theorem Array.set_eraseIdx_le : type_of% @_root_.Array.set_eraseIdx_le := by
  intro α xs i hi j a le hj
  apply _root_.Array.ext'
  simpa only [_root_.Array.toList_eraseIdx, _root_.Array.toList_set] using
    (_root_.List.set_eraseIdx_le (xs := xs.toList) (a := a) le)

public theorem Array.set_eraseIdx_gt : type_of% @_root_.Array.set_eraseIdx_gt := by
  intro α xs i hi j a lt hj
  apply _root_.Array.ext'
  simpa only [_root_.Array.toList_eraseIdx, _root_.Array.toList_set] using
    (_root_.List.set_eraseIdx_gt (xs := xs.toList) (a := a) lt)

public theorem Array.mem_eraseIdx_iff_getElem? : type_of% @_root_.Array.mem_eraseIdx_iff_getElem? := by
  intro α x xs k h
  have erase := _root_.Array.toList_eraseIdx (xs := xs) (i := k) (h := h)
  constructor
  · intro member
    obtain ⟨i, ne, val⟩ := List.mem_eraseIdx_iff_getElem?.mp (erase ▸ _root_.Array.mem_def.mp member)
    exact ⟨i, ne, _root_.Array.getElem?_toList.symm.trans val⟩
  · intro ⟨i, ne, val⟩
    apply _root_.Array.mem_def.mpr
    exact erase.symm ▸ List.mem_eraseIdx_iff_getElem?.mpr ⟨i, ne, _root_.Array.getElem?_toList.trans val⟩

public theorem Array.mem_eraseIdx_iff_getElem : type_of% @_root_.Array.mem_eraseIdx_iff_getElem := by
  intro α x xs k h
  have erase := _root_.Array.toList_eraseIdx (xs := xs) (i := k) (h := h)
  exact _root_.Array.mem_def.trans ((Iff.of_eq (congrArg (fun ys => x ∈ ys) erase)).trans
    List.mem_eraseIdx_iff_getElem)

public theorem List.getElem?_eraseIdx_of_ge : type_of% @_root_.List.getElem?_eraseIdx_of_ge := by
  intro α xs i j h
  rw [List.getElem?_eraseIdx, ite_eq_right (Nat.not_lt_of_ge h)]

public theorem List.getElem_eraseIdx_of_lt : type_of% @_root_.List.getElem_eraseIdx_of_lt := by
  intro α xs i j inBounds h
  rw [List.getElem_eraseIdx, dite_eq_left h]

public theorem List.set_getElem_succ_eraseIdx_succ : type_of% @_root_.List.set_getElem_succ_eraseIdx_succ := by
  intro α xs i h
  induction xs generalizing i with
  | nil => exact (Nat.not_lt_zero _ h).elim
  | cons a xs ih =>
    cases i with
    | zero => cases xs with
      | nil => exact (Nat.lt_irrefl 1 h).elim
      | cons _ _ => rfl
    | succ i =>
      rw [List.eraseIdx_cons_succ, List.eraseIdx_cons_succ, List.set_cons_succ]
      exact congrArg (a :: ·) (ih (Nat.lt_of_succ_lt_succ h))

public theorem List.eraseIdx_length_sub_one : type_of% @_root_.List.eraseIdx_length_sub_one := by
  intro α xs
  induction xs with
  | nil => rfl
  | cons a xs ih => cases xs with
    | nil => rfl
    | cons b ys =>
      rw [List.dropLast_cons_cons]
      exact congrArg (a :: ·) ih

public theorem Vector.getElem?_eraseIdx_of_ge : type_of% @_root_.Vector.getElem?_eraseIdx_of_ge := by
  intro α n xs i hi j h
  rw [Vector.getElem?_eraseIdx, ite_eq_right (Nat.not_lt_of_ge h)]

public theorem Vector.getElem_eraseIdx_of_lt : type_of% @_root_.Vector.getElem_eraseIdx_of_lt := by
  intro α n xs i hi j hj h
  rw [Vector.getElem_eraseIdx, dite_eq_left h]

public theorem Vector.set_getElem_succ_eraseIdx_succ : type_of% @_root_.Vector.set_getElem_succ_eraseIdx_succ := by
  intro α n xs i hi
  rcases xs with ⟨xs, rfl⟩
  apply Vector.toArray_inj.mp
  exact Array.set_getElem_succ_eraseIdx_succ hi

public theorem Array.size_erase : type_of% @_root_.Array.size_erase := by
  intro α _ _ a xs
  by_cases h : a ∈ xs
  · rw [ite_eq_left h]
    exact Array.size_erase_of_mem h
  · rw [ite_eq_right h, Array.erase_of_not_mem h]

public theorem Array.eraseIdxIfInBounds_eq : type_of% @_root_.Array.eraseIdxIfInBounds_eq := by
  intro α xs i
  by_cases h : i < xs.size
  · rw [dite_eq_left h]
    exact (_root_.Array.eraseIdx_eq_eraseIdxIfInBounds h).symm
  · rw [dite_eq_right h]
    apply _root_.Array.toList_inj.mp
    rw [_root_.Array.toList_eraseIdxIfInBounds]
    exact _root_.List.eraseIdx_of_length_le (Nat.le_of_not_gt h)

public theorem Array.eraseIdx_ne_empty_iff : type_of% @_root_.Array.eraseIdx_ne_empty_iff := by
  intro α xs i h
  rw [← Array.size_pos_iff, Array.size_eraseIdx]
  omega

public theorem Array.size_eq_countP_add_countP : type_of% @_root_.Array.size_eq_countP_add_countP := by
  intro α p xs
  rw [← Array.countP_toList, ← Array.countP_toList]
  exact List.length_eq_countP_add_countP p

public theorem Array.filter_eq : type_of% @_root_.Array.filter_eq := by
  intro α beq law dec xs a
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_replicate, ← Array.count_toList]
  exact List.filter_eq a

public theorem Array.count_replace : type_of% @_root_.Array.count_replace := by
  intro α beq law a b c xs
  simp only [Array.count_eq_countP, Array.countP_replace]

public theorem List.length_filter_lt_length_iff_exists : type_of% @_root_.List.length_filter_lt_length_iff_exists := by
  intro α p l
  rw [← List.countP_eq_length_filter]
  have total := List.length_eq_countP_add_countP p (l := l)
  have countPos := @List.countP_pos_iff α l (fun x => decide (¬p x))
  constructor
  · intro lt
    have positive : 0 < l.countP (fun x => decide (¬p x)) := by omega
    obtain ⟨x, mem, h⟩ := countPos.mp positive
    exact ⟨x, mem, of_decide_eq_true h⟩
  · rintro ⟨x, mem, h⟩
    have positive := countPos.mpr ⟨x, mem, decide_eq_true h⟩
    omega

public theorem Array.size_filter_lt_size_iff_exists : type_of% @_root_.Array.size_filter_lt_size_iff_exists := by
  intro α xs p
  cases xs with
  | mk l =>
    rw [List.filter_toArray, List.size_toArray, List.size_toArray, List.length_filter_lt_length_iff_exists]
    exact ⟨fun ⟨x, mem, h⟩ => ⟨x, List.mem_toArray.mpr mem, h⟩,
      fun ⟨x, mem, h⟩ => ⟨x, List.mem_toArray.mp mem, h⟩⟩

public theorem Array.flatten_filter_ne_empty : type_of% @_root_.Array.flatten_filter_ne_empty := by
  intro α dec xss
  have same : (xss.filter fun xs => xs ≠ #[]) = (xss.filter fun xs => !xs.isEmpty) := by
    apply Array.toList_inj.mp
    rw [Array.toList_filter, Array.toList_filter]
    apply List.filter_congr
    intro x _
    cases x with
    | mk l =>
      cases l with
      | nil => exact decide_eq_false (fun h => h rfl)
      | cons x xs => exact decide_eq_true (fun e => List.cons_ne_nil x xs (congrArg Array.toList e))
  exact (congrArg Array.flatten same).trans Array.flatten_filter_not_isEmpty

public theorem Array.flatten_eq_push_iff : type_of% @_root_.Array.flatten_eq_push_iff := by
  intro α xss ys y
  constructor
  · intro eq
    induction len : xss.size using Nat.strongRecOn generalizing xss with
    | ind n ih =>
      by_cases zero : xss.size = 0
      · have empty := Array.eq_empty_of_size_eq_zero zero
        rw [empty, Array.flatten_empty] at eq
        exact (Array.push_ne_empty eq.symm).elim
      · obtain ⟨pre, last, rfl⟩ := Array.eq_push_of_size_ne_zero zero
        rw [Array.flatten_push] at eq
        by_cases empty : last.size = 0
        · have smaller : pre.size < n := by rw [←len, Array.size_push]; exact Nat.lt_succ_self _
          obtain rfl := Array.eq_empty_of_size_eq_zero empty
          rw [Array.append_empty] at eq
          obtain ⟨as, bs, cs, shape, emptyTail, prefixEq⟩ := ih _ smaller eq rfl
          refine ⟨as, bs, cs.push #[], ?_, ?_, prefixEq⟩
          · rw [shape, Array.push_append]
          · intro xs mem
            exact (Array.mem_push.mp mem).elim (emptyTail _) id
        · obtain ⟨bs, c, rfl⟩ := Array.eq_push_of_size_ne_zero empty
          rw [Array.append_push] at eq
          have cEq := Array.back_eq_of_push_eq eq
          cases cEq
          exact ⟨pre, bs, #[], Array.append_empty.symm,
            fun xs mem => (Array.not_mem_empty _ mem).elim, (Array.pop_eq_of_push_eq eq).symm⟩
  · rintro ⟨as, bs, cs, rfl, emptyTail, rfl⟩
    rw [Array.flatten_append, Array.flatten_eq_empty_iff.mpr emptyTail, Array.append_empty,
      Array.flatten_push, Array.append_push]

end OmegaChecks.InitPort.Alternatives

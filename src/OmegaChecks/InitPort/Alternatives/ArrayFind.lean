module
import all Init.Data.Array.Basic
public import Init.Data.Array.Lemmas
public import Init.Data.Array.Find
public import Init.Data.List.Find

namespace OmegaChecks.InitPort.Alternatives

private theorem findRevPrefix (f : α → Option β) (xs : List α) (i : Nat) (h : i ≤ xs.toArray.size) :
    (Array.findSomeRevM?.find (m := Id) f xs.toArray i h).run = (xs.take i).reverse.findSome? f := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have bound : i < xs.length := List.size_toArray (as := xs) ▸ h
    rw [Array.findSomeRevM?.find, List.take_succ_eq_append_getElem bound, List.reverse_append]
    simp only [Id.run, Bind.bind, Id.instMonad, Pure.pure, List.reverse_singleton,
      List.singleton_append, List.getElem_toArray, List.findSome?_cons]
    cases f xs[i] with
    | some b => rfl
    | none => exact ih _

private theorem findRevArray (f : α → Option β) (xs : List α) :
    xs.toArray.findSomeRev? f = xs.reverse.findSome? f := by
  have result := findRevPrefix f xs xs.length (List.size_toArray.symm ▸ Nat.le_refl _)
  rw [List.take_length] at result
  exact result

public theorem Array.findSomeRev?_eq_findSome?_reverse : type_of% @_root_.Array.findSomeRev?_eq_findSome?_reverse := by
  intro α β f xs
  cases xs with
  | mk xs =>
    rw [findRevArray, List.reverse_toArray, _root_.List.findSome?_toArray]

public theorem Array.findRev?_eq_find?_reverse : type_of% @_root_.Array.findRev?_eq_find?_reverse := by
  intro α p xs
  cases xs with
  | mk xs =>
    change xs.toArray.findSomeRev? (Option.guard p) = _
    rw [findRevArray, List.reverse_toArray, _root_.List.find?_toArray, List.findSome?_guard]

public theorem Array.findFinIdx?_congr : type_of% @_root_.Array.findFinIdx?_congr := by
  intro α p xs ys eq
  subst ys
  cases xs.findFinIdx? p <;> rfl

public theorem Array.findFinIdx?_eq_none_iff : type_of% @_root_.Array.findFinIdx?_eq_none_iff := by
  intro α xs p
  have missing : xs.findFinIdx? p = none ↔ xs.findIdx? p = none := by
    rw [Array.findIdx?_eq_map_findFinIdx?_val]
    exact Option.map_eq_none_iff.symm
  exact ⟨fun h x mem => Bool.eq_false_iff.mp (Array.findIdx?_eq_none_iff.mp (missing.mp h) x mem),
    fun h => missing.mpr (Array.findIdx?_eq_none_iff.mpr (fun x mem => Bool.eq_false_iff.mpr (h x mem)))⟩

public theorem Array.findFinIdx?_eq_some_iff : type_of% @_root_.Array.findFinIdx?_eq_some_iff := by
  intro α xs p i
  have atIndex : xs.findFinIdx? p = some i ↔ xs.findIdx? p = some i.val := by
    rw [Array.findIdx?_eq_map_findFinIdx?_val]
    exact (Option.map_inj_right (o' := some i) (f := Fin.val) (fun _ _ => Fin.eq_of_val_eq)).symm
  constructor
  · intro hit
    obtain ⟨_, here, before⟩ := Array.findIdx?_eq_some_iff_getElem.mp (atIndex.mp hit)
    exact ⟨here, fun j hj => before j.val hj⟩
  · rintro ⟨here, before⟩
    exact atIndex.mpr (Array.findIdx?_eq_some_iff_getElem.mpr
      ⟨i.isLt, here, fun j hj => before ⟨j, Nat.lt_trans hj i.isLt⟩ hj⟩)

public theorem Array.findIdx?_append : type_of% @_root_.Array.findIdx?_append := by
  intro α xs ys p
  cases xs with
  | mk as =>
    cases ys with
    | mk bs =>
      rw [List.append_toArray, List.findIdx?_toArray, List.findIdx?_toArray, List.findIdx?_toArray,
        List.size_toArray]
      exact List.findIdx?_append

public theorem List.head?_filter : type_of% @_root_.List.head?_filter := by
  intro α p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, List.find?_cons]
    cases p x with
    | true => rfl
    | false => exact ih

public theorem List.find?_eq_bind_findIdx?_getElem? : type_of% @_root_.List.find?_eq_bind_findIdx?_getElem? := by
  intro α xs p
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.find?_cons, List.findIdx?_cons]
    cases h : p x with
    | true => rfl
    | false =>
      change xs.find? p = ((xs.findIdx? p).map Nat.succ).bind _
      rw [ih]
      cases xs.findIdx? p <;> rfl

public theorem Array.find?_eq_bind_findIdx?_getElem? : type_of% @_root_.Array.find?_eq_bind_findIdx?_getElem? := by
  intro α xs p
  cases xs with
  | mk xs =>
    rw [_root_.List.find?_toArray, _root_.List.findIdx?_toArray, _root_.List.find?_eq_bind_findIdx?_getElem?]
    cases xs.findIdx? p with
    | none => rfl
    | some i => exact List.getElem?_toArray.symm

private theorem findSomePointwise {xs : List α} {f g : α → Option β} (h : ∀ x, f x = g x) :
    xs.findSome? f = xs.findSome? g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.findSome?_cons, List.findSome?_cons, h]; cases g x <;> first | rfl | exact ih

public theorem Array.getElem?_zero_flatten : type_of% @_root_.Array.getElem?_zero_flatten := by
  intro α xss
  rw [← Array.getElem?_toList, Array.toList_flatten, ← List.head?_eq_getElem?, List.head?_flatten,
    List.findSome?_map, ← Array.findSome?_toList]
  apply findSomePointwise
  intro xs
  exact List.head?_eq_getElem?.trans Array.getElem?_toList

public theorem Array.getElem_zero_flatten.proof : type_of% @_root_.Array.getElem_zero_flatten.proof := by
  intro α xss h
  rw [← _root_.Array.getElem?_zero_flatten, _root_.Array.getElem?_eq_getElem h]
  rfl

public theorem Array.getElem_zero_flatten : type_of% @_root_.Array.getElem_zero_flatten := by
  intro α xss h
  apply Option.some.inj
  exact (_root_.Array.getElem?_eq_getElem h).symm.trans ((_root_.Array.getElem?_zero_flatten xss).trans (Option.some_get _).symm)

public theorem Array.find?_flatten : type_of% @_root_.Array.find?_flatten := by
  intro α xss p
  rw [← Array.find?_toList, Array.toList_flatten, List.find?_flatten, List.findSome?_map, ← Array.findSome?_toList]
  exact findSomePointwise (fun xs => _root_.Array.find?_toList (xs := xs))

public theorem Array.find?_flatMap : type_of% @_root_.Array.find?_flatMap := by
  intro α β xs f p
  rw [← Array.find?_toList, Array.toList_flatMap, List.find?_flatMap, ← Array.findSome?_toList]
  exact findSomePointwise (fun x => _root_.Array.find?_toList (xs := f x))

private theorem flipped {b : Bool} : (!b = true) ↔ ¬ (b = true) := by
  cases b <;> decide

public theorem Array.find?_flatten_eq_none_iff : type_of% @_root_.Array.find?_flatten_eq_none_iff := by
  intro α xss p
  rw [_root_.Array.find?_flatten, _root_.Array.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Array.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Array.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Array.find?_flatMap_eq_none_iff : type_of% @_root_.Array.find?_flatMap_eq_none_iff := by
  intro α β xs f p
  rw [_root_.Array.find?_flatMap, _root_.Array.findSome?_eq_none_iff]
  exact ⟨fun h a m y hy => flipped.mpr (_root_.Array.find?_eq_none.mp (h a m) y hy),
    fun h a m => _root_.Array.find?_eq_none.mpr (fun y hy => flipped.mp (h a m y hy))⟩

public theorem Array.findIdx_push : type_of% @_root_.Array.findIdx_push := by
  intro α xs a p
  rw [Array.push_eq_append, Array.findIdx_append, Array.findIdx_singleton]
  split
  · rfl
  · exact Nat.add_comm ..

public theorem Array.findIdx?_push : type_of% @_root_.Array.findIdx?_push := by
  intro α xs a p
  rw [Array.push_eq_append, Array.findIdx?_append, Array.findIdx?_singleton]
  cases p a <;> simp only [ite_true, Bool.false_eq_true, ite_false, Option.map_some, Option.map_none, Nat.zero_add]

public theorem Array.findIdx?_eq_guard_findIdx_lt : type_of% @_root_.Array.findIdx?_eq_guard_findIdx_lt := by
  intro α xs p
  cases hit : xs.findIdx? p with
  | none =>
    have eq := _root_.Array.findIdx?_eq_none_iff_findIdx_eq.mp hit
    rw [eq]; simp only [Option.guard, decide_eq_false (Nat.lt_irrefl _), Bool.false_eq_true, ite_false]
  | some i =>
    have ⟨hi, eq⟩ := _root_.Array.findIdx?_eq_some_iff_findIdx_eq.mp hit
    subst i
    simp only [Option.guard, decide_eq_true hi, ite_true]

public theorem Array.of_findIdx?_eq_some : type_of% @_root_.Array.of_findIdx?_eq_some := by
  intro i α xs p hit
  obtain ⟨hi, pass, _⟩ := _root_.Array.findIdx?_eq_some_iff_getElem.mp hit
  rw [Array.getElem?_eq_getElem hi]
  exact pass

public theorem Array.of_findIdx?_eq_none : type_of% @_root_.Array.of_findIdx?_eq_none := by
  intro α xs p empty i
  by_cases hi : i < xs.size
  · rw [Array.getElem?_eq_getElem hi]
    exact fun pass => Bool.noConfusion ((_root_.Array.findIdx?_eq_none_iff.mp empty _ (Array.getElem_mem hi)).symm.trans pass)
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hi)]

public theorem List.findIdx?_take : type_of% @_root_.List.findIdx?_take := by
  intro α xs i p
  induction xs generalizing i with
  | nil => rw [List.take_nil]; rfl
  | cons x xs ih =>
    cases i with
    | zero => cases (x :: xs).findIdx? p with
      | none => rfl
      | some n => simp only [List.take_zero, List.findIdx?_nil, Option.bind_some, Option.guard, decide_eq_false (Nat.not_lt_zero n), Bool.false_eq_true, ite_false]
    | succ i =>
      rw [List.take_succ_cons, List.findIdx?_cons, List.findIdx?_cons]
      cases test : p x with
      | true => simp only [ite_true, Option.bind_some, Option.guard, decide_eq_true (Nat.zero_lt_succ i)]
      | false =>
        change (List.findIdx? p (xs.take i)).map Nat.succ = ((xs.findIdx? p).map Nat.succ).bind _
        rw [ih]
        cases xs.findIdx? p with
        | none => rfl
        | some n =>
          by_cases inside : n < i
          · have next := Nat.succ_lt_succ inside
            simp only [Option.bind_some, Option.map_some, Option.guard, decide_eq_true inside, decide_eq_true next, ite_true]
          · have outside : ¬ n.succ < i.succ := fun h => inside (Nat.lt_of_succ_lt_succ h)
            simp only [Option.bind_some, Option.map_some, Option.guard, decide_eq_false inside, decide_eq_false outside, Bool.false_eq_true, ite_false, Option.map_none]

public theorem Array.findIdx?_take : type_of% @_root_.Array.findIdx?_take := by
  intro α xs i p
  cases xs with
  | mk xs => rw [List.take_toArray, List.findIdx?_toArray, List.findIdx?_toArray]; exact List.findIdx?_take

end OmegaChecks.InitPort.Alternatives

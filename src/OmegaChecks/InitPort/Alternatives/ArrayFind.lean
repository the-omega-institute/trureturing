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

end OmegaChecks.InitPort.Alternatives

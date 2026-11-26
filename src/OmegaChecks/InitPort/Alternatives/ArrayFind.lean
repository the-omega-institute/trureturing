module
import all Init.Data.Array.Basic
public import Init.Data.Array.Lemmas
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

end OmegaChecks.InitPort.Alternatives

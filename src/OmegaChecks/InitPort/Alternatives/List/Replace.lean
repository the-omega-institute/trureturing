module
import all Init.Data.List.Lemmas
import all Init.Data.List.Basic

/-! The first matching element in a list determines every subsequent lookup. -/
namespace OmegaChecks.InitPort.Alternatives
namespace List
open _root_.List

public theorem replace_append_left : type_of% @_root_.List.replace_append_left := by
  intro α _ a b _ xs ys mem
  letI : DecidableEq α := _root_.instDecidableEqOfLawfulBEq
  induction xs with
  | nil => exact nomatch mem
  | cons x xs ih =>
    by_cases eq : a = x
    · cases eq
      rw [cons_append, replace_cons_self, replace_cons_self, cons_append]
    · have miss := beq_false_of_ne eq
      rw [cons_append, replace_cons, replace_cons, miss]
      exact congrArg (x :: ·) (ih ((mem_cons.mp mem).resolve_left eq))

public theorem replace_append_right : type_of% @_root_.List.replace_append_right := by
  intro α _ a b _ xs ys absent
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ne : a ≠ x := fun eq => absent (mem_cons.mpr (.inl eq))
    rw [cons_append, replace_cons, beq_false_of_ne ne]
    exact congrArg (x :: ·) (ih (fun mem => absent (.tail _ mem)))

public theorem replace_append : type_of% @_root_.List.replace_append := by
  intro α _ a b _ xs ys
  by_cases mem : a ∈ xs
  · exact (_root_.List.replace_append_left mem).trans (ite_eq_left mem).symm
  · exact (_root_.List.replace_append_right mem).trans (ite_eq_right mem).symm

public theorem getElem?_replace : type_of% @_root_.List.getElem?_replace := by
  intro α _ a b _ xs i
  letI : DecidableEq α := _root_.instDecidableEqOfLawfulBEq
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero =>
      by_cases eq : a = x
      · cases eq
        rw [replace_cons_self]
        change some b = if (some a == some a) then (if a ∈ ([] : List α) then _ else _) else _
        rw [ite_eq_left (BEq.rfl), ite_eq_right (not_mem_nil (a := a))]
      · rw [replace_cons, beq_false_of_ne eq]
        change some x = if (some x == some a) then _ else some x
        exact (ite_eq_right (fun same => eq (Option.some.inj (eq_of_beq same)).symm)).symm
    | succ i =>
      rw [getElem?_cons_succ, take_succ_cons]
      by_cases eq : a = x
      · cases eq
        rw [replace_cons_self, getElem?_cons_succ, ite_eq_left mem_cons_self]
        by_cases hit : xs[i]? == some a
        · exact (eq_of_beq hit).trans (ite_eq_left hit).symm
        · exact (ite_eq_right hit).symm
      · rw [replace_cons, beq_false_of_ne eq]
        refine (ih (i := i)).trans ?_
        by_cases hit : xs[i]? == some a
        · rw [ite_eq_left hit, ite_eq_left hit]
          by_cases old : a ∈ xs.take i
          · rw [ite_eq_left old, ite_eq_left (mem_cons_of_mem x old)]
          · rw [ite_eq_right old, ite_eq_right (not_mem_cons_of_ne_of_not_mem eq old)]
        · rw [ite_eq_right hit, ite_eq_right hit]

public theorem getElem?_replace_of_ne : type_of% @_root_.List.getElem?_replace_of_ne := by
  intro α _ a b _ xs i ne
  exact (_root_.List.getElem?_replace (a := a) (b := b)).trans
    (ite_eq_right (fun hit => ne (eq_of_beq hit)))

public theorem getElem_replace : type_of% @_root_.List.getElem_replace := by
  intro α _ a b _ xs i hi
  letI : DecidableEq α := _root_.instDecidableEqOfLawfulBEq
  apply Option.some.inj
  rw [← getElem?_eq_getElem (show i < (xs.replace a b).length from (length_replace (l := xs) (a := a) (b := b)).symm ▸ hi),
    _root_.List.getElem?_replace, getElem?_eq_getElem hi]
  by_cases hit : xs[i] = a
  · rw [ite_eq_left (beq_iff_eq.mpr (congrArg some hit)), ite_eq_left (beq_iff_eq.mpr hit)]
    by_cases old : a ∈ xs.take i
    · rw [ite_eq_left old, ite_eq_left old]
    · rw [ite_eq_right old, ite_eq_right old]
  · rw [ite_eq_right (fun h => hit (Option.some.inj (eq_of_beq h))),
      ite_eq_right (fun h => hit (eq_of_beq h))]

public theorem getElem_replace_of_ne : type_of% @_root_.List.getElem_replace_of_ne := by
  intro α _ a b _ xs i hi ne
  exact (_root_.List.getElem_replace hi).trans (ite_eq_right (fun hit => ne (eq_of_beq hit)))

public theorem contains_iff_exists_mem_beq : type_of% @_root_.List.contains_iff_exists_mem_beq := by
  intros
  rw [_root_.List.contains_eq_any_beq]
  exact _root_.List.any_eq_true

public theorem contains_replicate : type_of% @_root_.List.contains_replicate := by
  intro α _ n a b
  induction n with
  | zero => cases a == b <;> rfl
  | succ n ih =>
    rw [replicate_succ]
    change elem a (b :: replicate n b) = _
    rw [elem_cons]
    cases hit : a == b with
    | true => rfl
    | false =>
      rw [hit] at ih
      exact ih

end List
end OmegaChecks.InitPort.Alternatives

module
import all Init.Data.List.Find
import all Init.Data.List.Lemmas
import all Init.Data.List.Basic

/-! Endpoints of lists under mapping, filtering, repetition and concatenation. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.one_lt_length_of_tail_ne_nil : type_of% @_root_.List.one_lt_length_of_tail_ne_nil := by
  intro α xs ne
  cases xs with
  | nil => exact (ne rfl).elim
  | cons x xs =>
    cases xs with
    | nil => exact (ne rfl).elim
    | cons y ys => exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

public theorem List.head_tail : type_of% @_root_.List.head_tail := by
  intro α xs ne
  cases xs with
  | nil => exact (ne rfl).elim
  | cons x xs => cases xs with
    | nil => exact (ne rfl).elim
    | cons => rfl

public theorem List.head_dropLast : type_of% @_root_.List.head_dropLast := by
  intro α xs h
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs => cases xs with
    | nil => exact (h rfl).elim
    | cons => rfl

public theorem List.head_append._proof_1 :
    type_of% (private_decl% @_root_.List.head_append._proof_1) := by
  intro α left right ne empty
  cases _root_.List.isEmpty_iff.mp empty
  exact ne

public theorem List.head_append._proof_2 :
    type_of% (private_decl% @_root_.List.head_append._proof_2) := by
  intro α xs h nil
  cases nil
  exact h rfl

public theorem List.getLast_append._proof_1 :
    type_of% (private_decl% @_root_.List.getLast_append._proof_1) := by
  intro α right left ne empty nil
  cases _root_.List.isEmpty_iff.mp empty
  cases nil
  exact ne rfl

public theorem List.head_append : type_of% @_root_.List.head_append := by
  intro α xs ys ne
  cases xs <;> rfl

public theorem List.head_append_right : type_of% @_root_.List.head_append_right := by
  intro α xs ys ne eq
  cases eq
  rfl

public theorem List.head_replicate : type_of% @_root_.List.head_replicate := by
  intros
  apply _root_.List.eq_of_mem_replicate
  apply _root_.List.head_mem

public theorem List.getLast_replicate : type_of% @_root_.List.getLast_replicate := by
  intros
  apply _root_.List.eq_of_mem_replicate
  apply _root_.List.getLast_mem

public theorem List.getLast_map : type_of% @_root_.List.getLast_map := by
  intro α β f xs ne
  induction xs with
  | nil => exact (ne rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => exact ih (_root_.List.cons_ne_nil (f y) (ys.map f))

public theorem List.getLast?_map : type_of% @_root_.List.getLast?_map := by
  intro α β f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons => exact ih

public theorem List.getLastD_map : type_of% @_root_.List.getLastD_map := by
  intro α β f xs x
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    rw [_root_.List.map_cons, _root_.List.getLastD_cons, _root_.List.getLastD_cons]
    exact ih (x := y)

public theorem List.getLast_append_right : type_of% @_root_.List.getLast_append_right := by
  intro α ys xs ne
  exact _root_.List.getLast_append_of_ne_nil _ ne

public theorem List.getLast_append_left : type_of% @_root_.List.getLast_append_left := by
  intro α ys xs ne eq
  cases eq
  simp only [_root_.List.append_nil]

public theorem List.getLast_append : type_of% @_root_.List.getLast_append := by
  intro α ys xs ne
  cases ys with
  | nil => exact _root_.List.getLast_append_left ne rfl
  | cons y ys => exact _root_.List.getLast_append_of_ne_nil ne (_root_.List.cons_ne_nil y ys)

public theorem List.flatten_ne_nil_iff : type_of% @_root_.List.flatten_ne_nil_iff := by
  intro α xss
  constructor
  · intro nonempty
    obtain ⟨xs, mem, h⟩ := _root_.List.mem_flatten.mp (_root_.List.head_mem nonempty)
    exact ⟨xs, mem, _root_.List.ne_nil_of_mem h⟩
  · intro ⟨xs, mem, ne⟩
    exact _root_.List.ne_nil_of_mem (_root_.List.mem_flatten.mpr ⟨xs, mem, _root_.List.head_mem ne⟩)

public theorem List.filter_filterMap : type_of% @_root_.List.filter_filterMap := by
  intro α β f p xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases fx : f x with
    | none =>
      rw [_root_.List.filterMap_cons_none fx, _root_.List.filterMap_cons_none (by simp only [fx]; rfl)]
      exact ih
    | some y =>
      rw [_root_.List.filterMap_cons_some fx]
      cases keep : p y with
      | true =>
        rw [_root_.List.filter_cons_of_pos keep, _root_.List.filterMap_cons_some
          (by simp only [fx, Option.filter, keep]; rfl)]
        exact congrArg (y :: ·) ih
      | false =>
        rw [_root_.List.filter_cons_of_neg (by rw [keep]; decide),
          _root_.List.filterMap_cons_none (by simp only [fx, Option.filter, keep]; rfl)]
        exact ih

public theorem List.filterMap_filter : type_of% @_root_.List.filterMap_filter := by
  intro α β p f xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases keep : p x with
    | false =>
      rw [_root_.List.filter_cons_of_neg (by rw [keep]; decide),
        _root_.List.filterMap_cons_none (by simp only [keep]; rfl)]
      exact ih
    | true =>
      rw [_root_.List.filter_cons_of_pos keep]
      cases fx : f x with
      | none =>
        rw [_root_.List.filterMap_cons_none fx, _root_.List.filterMap_cons_none (f := fun z => if p z then f z else none) ((ite_eq_left keep).trans fx)]
        exact ih
      | some y =>
        rw [_root_.List.filterMap_cons_some fx, _root_.List.filterMap_cons_some (f := fun z => if p z then f z else none) (b := y) ((ite_eq_left keep).trans fx)]
        exact congrArg (y :: ·) ih

public theorem List.map_filterMap_of_inv : type_of% @_root_.List.map_filterMap_of_inv := by
  intro α β f g inv xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have eq := inv x
    cases fx : f x with
    | none => rw [fx] at eq; contradiction
    | some y =>
      rw [fx] at eq
      rw [_root_.List.filterMap_cons_some fx, _root_.List.map_cons, ih, Option.some.inj eq]

public theorem List.head_filterMap_of_eq_some : type_of% @_root_.List.head_filterMap_of_eq_some := by
  intro α β f xs ne b found
  apply (_root_.List.head_eq_iff_head?_eq_some _).mpr
  cases xs with
  | nil => exact (ne rfl).elim
  | cons x xs =>
    rw [_root_.List.filterMap_cons_some (show f x = some b from found)]
    rfl

public theorem List.getLast_filterMap_of_eq_some : type_of% @_root_.List.getLast_filterMap_of_eq_some := by
  intro α β f xs ne b found
  apply (_root_.List.getLast_eq_iff_getLast?_eq_some _).mpr
  rw [_root_.List.getLast?_eq_head?_reverse, ← _root_.List.filterMap_reverse]
  have rev := _root_.List.reverse_ne_nil_iff.mpr ne
  rw [_root_.List.getLast_eq_head_reverse ne] at found
  have h := _root_.List.head_filterMap_of_eq_some rev found
  exact (_root_.List.head?_eq_some_head _).trans (congrArg some h)

public theorem List.getLast_filterMap._proof_1 :
    type_of% (private_decl% @_root_.List.getLast_filterMap._proof_1) := by
  intro α β f xs h
  rw [← _root_.List.getLast?_filterMap, _root_.List.getLast?_eq_some_getLast h]
  rfl

public theorem List.getLast_filterMap : type_of% @_root_.List.getLast_filterMap := by
  intro α β f xs h
  apply (_root_.List.getLast_eq_iff_getLast?_eq_some h).mpr
  exact _root_.List.getLast?_filterMap.trans (Option.some_get _).symm

public theorem List.head_flatten._proof_1 :
    type_of% (private_decl% @_root_.List.head_flatten._proof_1) := by
  intros
  exact _root_.List.flatten_ne_nil_iff.mpr ‹_›

public theorem List.head_flatten._proof_2 :
    type_of% (private_decl% @_root_.List.head_flatten._proof_2) := by
  intro α xss h
  rw [← _root_.List.head?_flatten, _root_.List.head?_eq_some_head (_root_.List.flatten_ne_nil_iff.mpr h)]
  rfl

public theorem List.getLast_flatten._proof_1 :
    type_of% (private_decl% @_root_.List.getLast_flatten._proof_1) := by
  intro α xss h
  rw [← _root_.List.getLast?_flatten, _root_.List.getLast?_eq_some_getLast (_root_.List.flatten_ne_nil_iff.mpr h)]
  rfl

public theorem List.head_flatten : type_of% @_root_.List.head_flatten := by
  intro α xss h
  apply (_root_.List.head_eq_iff_head?_eq_some _).mpr
  exact _root_.List.head?_flatten.trans (Option.some_get _).symm

public theorem List.getLast_flatten : type_of% @_root_.List.getLast_flatten := by
  intro α xss h
  apply (_root_.List.getLast_eq_iff_getLast?_eq_some _).mpr
  exact _root_.List.getLast?_flatten.trans (Option.some_get _).symm

public theorem List.head!_eq_getElem! : type_of% @_root_.List.head!_eq_getElem! := by
  intro α _ xs
  cases xs with
  | nil => exact _root_.List.getElem!_nil.symm
  | cons a as => exact _root_.List.getElem!_cons_zero.symm

end OmegaChecks.InitPort.Alternatives

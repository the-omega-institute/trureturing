module
import all Init.Data.List.Lemmas
import Init.Data.Option.Lemmas

/-! Pointwise filters and their folds preserve the original order of the list. -/
namespace OmegaChecks.InitPort.Alternatives.List
open _root_.List

public theorem mem_dite_nil_left : type_of% @_root_.List.mem_dite_nil_left := by
  intro α p x _ l
  by_cases h : p
  · rw [dite_eq_left h]
    exact ⟨(fun m => nomatch m), fun ⟨hn, _⟩ => (hn h).elim⟩
  · rw [dite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, fun ⟨_, m⟩ => m⟩

public theorem mem_ite_nil_left : type_of% @_root_.List.mem_ite_nil_left := by
  intro α p x _ l
  by_cases h : p
  · rw [ite_eq_left h]
    exact ⟨(fun m => nomatch m), fun m => (m.1 h).elim⟩
  · rw [ite_eq_right h]
    exact ⟨fun m => ⟨h, m⟩, And.right⟩

public theorem all_eq_false : type_of% @_root_.List.all_eq_false := by
  intro α p xs
  induction xs with
  | nil =>
    exact ⟨(fun h => nomatch h), fun ⟨_, hm, _⟩ => nomatch hm⟩
  | cons x xs ih =>
    rw [all_cons]
    cases h : p x with
    | false => exact ⟨fun _ => ⟨x, mem_cons_self, by rw [h]; decide⟩, fun _ => rfl⟩
    | true =>
      constructor
      · intro fail
        obtain ⟨y, mem, hy⟩ := ih.mp fail
        exact ⟨y, .tail x mem, hy⟩
      · rintro ⟨y, mem, hy⟩
        cases mem with
        | head => exact (hy h).elim
        | tail _ m => exact ih.mpr ⟨y, m, hy⟩

public theorem map_inj : type_of% @_root_.List.map_inj := by
  intro α β f g
  exact ⟨fun eq => congrArg (fun k x => (k [x]).headD (f x)) eq, congrArg _root_.List.map⟩

public theorem replicate_beq_replicate : type_of% @_root_.List.replicate_beq_replicate := by
  intro α _ a b n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ, replicate_succ, cons_beq_cons, ih]
    change ((a == b) && (n == 0 || a == b)) = (a == b)
    cases a == b <;> cases n == 0 <;> rfl

public theorem foldl_ite_left : type_of% @_root_.List.foldl_ite_left := by
  intro α β p _ xs f init
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x
    · rw [foldl_cons, ite_eq_left h, filter_cons_of_pos (p := fun a => decide (p a)) (decide_eq_true h), foldl_cons]
      apply ih
    · rw [foldl_cons, ite_eq_right h, filter_cons_of_neg (p := fun a => decide (p a)) (fun e => h (of_decide_eq_true e))]
      apply ih

public theorem foldl_ite_right : type_of% @_root_.List.foldl_ite_right := by
  intro α β p _ xs f init
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x
    · rw [foldl_cons, ite_eq_left h, filter_cons_of_neg (p := fun a => decide (¬ p a)) (fun e => (of_decide_eq_true e) h)]
      apply ih
    · rw [foldl_cons, ite_eq_right h, filter_cons_of_pos (p := fun a => decide (¬ p a)) (decide_eq_true h), foldl_cons]
      apply ih

private theorem filterGuard (p : α → Bool) (xs : List α) :
    xs.filterMap (Option.guard p) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p a with
    | false =>
      rw [filterMap_cons_none (Option.guard_eq_none_iff.mpr h), filter_cons_of_neg (by rw [h]; decide)]
      exact ih
    | true =>
      rw [filterMap_cons_some (Option.guard_eq_some_iff.mpr ⟨rfl, h⟩), filter_cons_of_pos h]
      exact congrArg (a :: ·) ih

public theorem filter_eq_append_iff : type_of% @_root_.List.filter_eq_append_iff := by
  intro α xs left right p
  constructor
  · intro eq
    obtain ⟨a, b, split, ha, hb⟩ := _root_.List.filterMap_eq_append_iff.mp ((filterGuard p xs).trans eq)
    exact ⟨a, b, split, (filterGuard p a).symm.trans ha, (filterGuard p b).symm.trans hb⟩
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact filter_append a b

public theorem append_eq_filter_iff : type_of% @_root_.List.append_eq_filter_iff := by
  intros
  exact ⟨fun eq => _root_.List.filter_eq_append_iff.mp eq.symm,
    fun parts => (_root_.List.filter_eq_append_iff.mpr parts).symm⟩

end OmegaChecks.InitPort.Alternatives.List

module
import all Init.Data.Array.Basic
import Init.Data.Array.Lemmas

/-! Constructive interval specifications for short-circuit array predicates. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem anyPast {α : Type u} (p : α → Bool) (xs : _root_.Array α)
    {stop start} (limit : stop ≤ xs.size) (done : ¬start < stop) :
    (_root_.Array.anyM.loop (m := Id) (pure <| p ·) xs stop limit start).run = true ↔
      ∃ (i : Nat) (hi : i < xs.size), start ≤ i ∧ i < stop ∧ p xs[i] = true := by
  rw [_root_.Array.anyM.loop.eq_def, dite_eq_right done]
  exact ⟨fun e => (Bool.false_ne_true e).elim,
    fun ⟨i, _, lo, hi, _⟩ => (done (Nat.lt_of_le_of_lt lo hi)).elim⟩

private theorem anyFrom {α : Type u} (p : α → Bool) (xs : _root_.Array α)
    {stop} (limit : stop ≤ xs.size) (fuel start : Nat) (room : stop ≤ fuel + start) :
    (_root_.Array.anyM.loop (m := Id) (pure <| p ·) xs stop limit start).run = true ↔
      ∃ (i : Nat) (hi : i < xs.size), start ≤ i ∧ i < stop ∧ p xs[i] = true := by
  induction fuel generalizing start with
  | zero => exact anyPast p xs limit (Nat.not_lt_of_ge ((Nat.zero_add start) ▸ room))
  | succ n ih =>
    by_cases valid : start < stop
    · have bound := Nat.lt_of_lt_of_le valid limit
      rw [_root_.Array.anyM.loop.eq_def, dite_eq_left valid]
      change (if p xs[start] then true else _) = true ↔ _
      by_cases hit : p xs[start] = true
      · rw [ite_eq_left hit]
        exact ⟨fun _ => ⟨start, bound, Nat.le_refl _, valid, hit⟩, fun _ => rfl⟩
      · rw [ite_eq_right hit]
        have nextRoom : stop ≤ n + (start + 1) := Eq.subst (motive := (stop ≤ ·)) (Nat.succ_add n start) room
        have next := ih (start + 1) nextRoom
        constructor
        · intro h
          obtain ⟨i, hi, lo, top, witness⟩ := next.mp h
          exact ⟨i, hi, Nat.le_trans (Nat.le_succ _) lo, top, witness⟩
        · intro ⟨i, hi, lo, top, witness⟩
          have ne : start ≠ i := by
            intro e
            cases e
            exact hit witness
          exact next.mpr ⟨i, hi, Nat.lt_of_le_of_ne lo ne, top, witness⟩
    · exact anyPast p xs limit valid

public theorem Array.anyM_loop_iff_exists : type_of% @_root_.Array.anyM_loop_iff_exists := by
  intro α p xs start stop limit
  exact anyFrom p xs limit stop start (Nat.le_add_right _ _)

public theorem Array.anyM_loop_iff_exists._unary : type_of% @_root_.Array.anyM_loop_iff_exists._unary := by
  intro α p xs stop h start
  exact Array.anyM_loop_iff_exists (p := p) (start := start) h

public theorem Array.any_iff_exists : type_of% @_root_.Array.any_iff_exists := by
  intro α p xs start stop
  unfold _root_.Array.any _root_.Array.anyM
  by_cases fits : stop ≤ xs.size
  · rw [dite_eq_left fits]
    exact Array.anyM_loop_iff_exists fits
  · rw [dite_eq_right fits]
    have h := Array.anyM_loop_iff_exists (p := p) (as := xs) (start := start) (Nat.le_refl xs.size)
    constructor
    · intro found
      obtain ⟨i, hi, lo, _, witness⟩ := h.mp found
      exact ⟨i, hi, lo, Nat.lt_trans hi (Nat.lt_of_not_ge fits), witness⟩
    · exact fun ⟨i, hi, lo, _, witness⟩ => h.mpr ⟨i, hi, lo, hi, witness⟩

public theorem Array.any_eq_true : type_of% @_root_.Array.any_eq_true := by
  intro α p xs
  constructor
  · intro h
    obtain ⟨i, hi, _, _, witness⟩ := Array.any_iff_exists.mp h
    exact ⟨i, hi, witness⟩
  · exact fun ⟨i, hi, witness⟩ => Array.any_iff_exists.mpr ⟨i, hi, Nat.zero_le _, hi, witness⟩

public theorem Array.any_eq_false : type_of% @_root_.Array.any_eq_false := by
  intro α p xs
  constructor
  · exact fun h i hi t => Bool.eq_false_iff.mp h (Array.any_eq_true.mpr ⟨i, hi, t⟩)
  · intro h
    apply Bool.eq_false_iff.mpr
    intro any
    obtain ⟨i, hi, hit⟩ := Array.any_eq_true.mp any
    exact h i hi hit

public theorem Array.any_toList : type_of% @_root_.Array.any_toList := by
  intro α p xs
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨x, m, hit⟩ := List.any_eq_true.mp h
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp m
    exact Array.any_eq_true.mpr ⟨i, hi, eq.symm ▸ hit⟩
  · intro h
    obtain ⟨i, hi, hit⟩ := Array.any_eq_true.mp h
    exact List.any_eq_true.mpr ⟨xs[i], List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩, hit⟩

public theorem Array.all_iff_forall : type_of% @_root_.Array.all_iff_forall := by
  intro α p xs start stop
  rw [_root_.Array.all_eq_not_any_not]
  constructor
  · intro ok i hi within
    by_cases good : p xs[i] = true
    · exact good
    · exact (Bool.not_eq.mp ok (Array.any_iff_exists.mpr
        ⟨i, hi, within.1, within.2, Bool.not_eq.mpr good⟩)).elim
  · intro every
    apply Bool.not_eq.mpr
    intro any
    obtain ⟨i, hi, lo, top, hit⟩ := Array.any_iff_exists.mp any
    exact Bool.not_eq.mp hit (every i hi ⟨lo, top⟩)

public theorem Array.all_eq_true : type_of% @_root_.Array.all_eq_true := by
  intro α p xs
  exact ⟨fun h i hi => Array.all_iff_forall.mp h i hi ⟨Nat.zero_le _, hi⟩,
    fun h => Array.all_iff_forall.mpr fun i hi _ => h i hi⟩

public theorem Array.all_toList : type_of% @_root_.Array.all_toList := by
  intro α p xs
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    exact Array.all_eq_true.mpr fun i hi => List.all_eq_true.mp h xs[i]
      (List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩)
  · intro h
    apply List.all_eq_true.mpr
    intro x m
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp m
    exact eq ▸ Array.all_eq_true.mp h i hi

public theorem Array.mem_filter : type_of% @_root_.Array.mem_filter := by
  intro α p xs a
  have lists := _root_.Array.toList_filter (p := p) (xs := xs)
  constructor
  · intro m
    have h := List.mem_filter.mp (Eq.subst (motive := (a ∈ ·)) lists (_root_.Array.mem_def.mp m))
    exact ⟨_root_.Array.mem_def.mpr h.1, h.2⟩
  · intro ⟨m, hit⟩
    exact _root_.Array.mem_def.mpr (Eq.subst (motive := (a ∈ ·)) lists.symm
      (List.mem_filter.mpr ⟨_root_.Array.mem_def.mp m, hit⟩))

public theorem Array.mem_filterMap : type_of% @_root_.Array.mem_filterMap := by
  intro α β f xs b
  have lists := _root_.Array.toList_filterMap (f := f) (xs := xs)
  constructor
  · intro m
    obtain ⟨x, t, h⟩ := List.mem_filterMap.mp
      (Eq.subst (motive := (b ∈ ·)) lists (_root_.Array.mem_def.mp m))
    exact ⟨x, _root_.Array.mem_def.mpr t, h⟩
  · intro ⟨x, m, hit⟩
    exact _root_.Array.mem_def.mpr (Eq.subst (motive := (b ∈ ·)) lists.symm
      (List.mem_filterMap.mpr ⟨x, _root_.Array.mem_def.mp m, hit⟩))

public theorem Array.all_eq_false : type_of% @_root_.Array.all_eq_false := by
  intro α p xs
  rw [_root_.Array.all_eq_not_any_not]
  constructor
  · intro none
    obtain ⟨i, hi, h⟩ := Array.any_eq_true.mp (Bool.ne_false_iff.mp (Bool.not_eq.mp none))
    exact ⟨i, hi, Bool.not_eq.mp h⟩
  · intro ⟨i, hi, h⟩
    exact Bool.not_eq.mpr (Bool.ne_false_iff.mpr (Array.any_eq_true.mpr ⟨i, hi, Bool.not_eq.mpr h⟩))

public theorem Array.any_eq_false' : type_of% @_root_.Array.any_eq_false' := by
  intro α p xs
  constructor
  · intro none x member witness
    exact Bool.eq_false_iff.mp none (_root_.Array.any_eq_true'.mpr ⟨x, member, witness⟩)
  · intro every
    apply Bool.eq_false_iff.mpr
    intro found
    obtain ⟨x, m, hit⟩ := _root_.Array.any_eq_true'.mp found
    exact every x m hit

public theorem Array.all_eq_false' : type_of% @_root_.Array.all_eq_false' := by
  intro α p xs
  constructor
  · intro some
    obtain ⟨i, hi, fail⟩ := Array.all_eq_false.mp some
    exact ⟨xs[i], _root_.Array.mem_def.mpr (List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩), fail⟩
  · intro ⟨x, m, fail⟩
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp (_root_.Array.mem_def.mp m)
    exact Array.all_eq_false.mpr ⟨i, hi, eq.symm ▸ fail⟩

private theorem shortCircuitCongr {m : Type → Type w} [Monad m] {a b c d : m Bool}
    (first : a = b) (rest : c = d) :
    (a >>= fun test => if test then pure true else c) = (b >>= fun test => if test then pure true else d) := by
  cases first
  cases rest
  rfl

private theorem sameAnyLoop {α : Type u} {m : Type → Type w} [Monad m]
    (p q : α → m Bool) (agree : ∀ a, p a = q a) (xs : _root_.Array α) (stop : Nat)
    (limit : stop ≤ xs.size) (fuel start : Nat) (space : stop ≤ fuel + start) :
    _root_.Array.anyM.loop p xs stop limit start = _root_.Array.anyM.loop q xs stop limit start := by
  induction fuel generalizing start with
  | zero =>
    have done : ¬start < stop := Nat.not_lt_of_ge ((Nat.zero_add start) ▸ space)
    rw [_root_.Array.anyM.loop.eq_def, _root_.Array.anyM.loop.eq_def (p := q) (j := start)]
    rw [dite_eq_right done, dite_eq_right done]
  | succ n ih =>
    rw [_root_.Array.anyM.loop.eq_def, _root_.Array.anyM.loop.eq_def (p := q) (j := start)]
    by_cases valid : start < stop
    · rw [dite_eq_left valid, dite_eq_left valid]
      have room : stop ≤ n + (start + 1) := Eq.subst (motive := (stop ≤ ·)) (Nat.succ_add n start) space
      exact shortCircuitCongr (agree (xs[start]'(Nat.lt_of_lt_of_le valid limit))) (ih (start+1) room)
    · rw [dite_eq_right valid, dite_eq_right valid]

public theorem Array.anyM_congr : type_of% @_root_.Array.anyM_congr := by
  intro m α a b c d inst xs ys eq p q point lo hi
  cases eq
  cases lo
  cases hi
  unfold _root_.Array.anyM
  split
  · exact sameAnyLoop p q point xs _ _ _ _ (Nat.le_add_right _ _)
  · exact sameAnyLoop p q point xs _ _ _ _ (Nat.le_add_right _ _)

public theorem Array.allM_congr : type_of% @_root_.Array.allM_congr := by
  intro m α a b c d inst xs ys eq p q point lo hi
  cases eq
  cases lo
  cases hi
  let neg (value : m Bool) : m Bool := do return !(← value)
  exact congrArg neg (Array.anyM_congr rfl (p := fun x => neg (p x)) (q := fun x => neg (q x))
    (fun x => congrArg neg (point x)) rfl rfl)

public theorem Array.any_eq' : type_of% @_root_.Array.any_eq' := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.Array.any_eq_true'.trans decide_eq_true_iff.symm)

public theorem Array.all_eq : type_of% @_root_.Array.all_eq := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.Array.all_eq_true.trans decide_eq_true_iff.symm)

public theorem Array.all_eq' : type_of% @_root_.Array.all_eq' := by
  intros
  exact Bool.eq_iff_iff.mpr (_root_.Array.all_eq_true'.trans decide_eq_true_iff.symm)

public theorem Array.decide_exists_mem : type_of% @_root_.Array.decide_exists_mem := by
  intro α xs p _
  apply Bool.eq_iff_iff.mpr
  refine decide_eq_true_iff.trans (Iff.trans ?_ _root_.Array.any_eq_true'.symm)
  exact ⟨fun ⟨x, mem, h⟩ => ⟨x, mem, decide_eq_true h⟩,
    fun ⟨x, mem, h⟩ => ⟨x, mem, of_decide_eq_true h⟩⟩

public theorem Array.decide_forall_mem : type_of% @_root_.Array.decide_forall_mem := by
  intro α xs p _
  apply Bool.eq_iff_iff.mpr
  refine decide_eq_true_iff.trans (Iff.trans ?_ _root_.Array.all_eq_true'.symm)
  exact ⟨fun h x mem => decide_eq_true (h x mem), fun h x mem => of_decide_eq_true (h x mem)⟩

public theorem Array.any_beq' : type_of% @_root_.Array.any_beq' := by
  intro α a _ _ xs
  exact (_root_.Array.any_congr (xs := xs) rfl (fun x => BEq.comm (a := x) (b := a)) rfl rfl).trans
    _root_.Array.any_beq

public theorem Array.all_bne' : type_of% @_root_.Array.all_bne' := by
  intro α a _ _ xs
  exact (_root_.Array.all_congr (xs := xs) rfl (fun x => bne_comm (a := x) (b := a)) rfl rfl).trans
    _root_.Array.all_bne

public theorem Array.any_eq_not_all_not : type_of% @_root_.Array.any_eq_not_all_not := by
  intro α xs p
  rw [_root_.Array.all_eq_not_any_not, Bool.not_not]
  exact _root_.Array.any_congr rfl (fun x => (Bool.not_not (p x)).symm) rfl rfl

public theorem List.length_filter_lt_length_iff_exists :
    type_of% @_root_.List.length_filter_lt_length_iff_exists := by
  intro α p xs
  induction xs with
  | nil =>
    exact ⟨fun h => (Nat.lt_irrefl 0 h).elim, fun ⟨_, mem, _⟩ => nomatch mem⟩
  | cons x xs ih =>
    cases hit : p x with
    | false =>
      rw [_root_.List.filter_cons_of_neg (by rw [hit]; decide)]
      exact ⟨fun _ => ⟨x, .head _, fun eq => Bool.false_ne_true (hit.symm.trans eq)⟩,
        fun _ => Nat.lt_succ_of_le (_root_.List.length_filter_le p xs)⟩
    | true =>
      rw [_root_.List.filter_cons_of_pos hit]
      constructor
      · intro lt
        obtain ⟨a, mem, miss⟩ := ih.mp (Nat.lt_of_succ_lt_succ lt)
        exact ⟨a, .tail _ mem, miss⟩
      · rintro ⟨a, mem, miss⟩
        rcases _root_.List.mem_cons.mp mem with rfl | tail
        · exact (miss hit).elim
        · exact Nat.succ_lt_succ (ih.mpr ⟨a, tail, miss⟩)

public theorem Array.size_filter_lt_size_iff_exists : type_of% @_root_.Array.size_filter_lt_size_iff_exists := by
  intro α xs p
  change (xs.filter p).toList.length < xs.toList.length ↔ _
  rw [_root_.Array.toList_filter]
  constructor
  · intro h
    obtain ⟨x, hx, miss⟩ := _root_.List.length_filter_lt_length_iff_exists.mp h
    exact ⟨x, _root_.Array.mem_def.mpr hx, miss⟩
  · rintro ⟨x, hx, miss⟩
    exact _root_.List.length_filter_lt_length_iff_exists.mpr ⟨x, _root_.Array.mem_def.mp hx, miss⟩

public theorem Array.flatten_filter_ne_empty : type_of% @_root_.Array.flatten_filter_ne_empty := by
  intro α dec xss
  apply Eq.trans (congrArg _root_.Array.flatten (_root_.Array.ext' ?_)) _root_.Array.flatten_filter_not_isEmpty
  rw [_root_.Array.toList_filter, _root_.Array.toList_filter]
  apply _root_.List.filter_congr
  intro xs _
  by_cases h : xs.isEmpty = true
  · rw [h, decide_eq_false (fun ne => ne (_root_.Array.isEmpty_iff.mp h))]
    rfl
  · rw [decide_eq_true (fun eq => h (_root_.Array.isEmpty_iff.mpr eq))]
    cases e : xs.isEmpty
    · rfl
    · exact (h e).elim

end OmegaChecks.InitPort.Alternatives

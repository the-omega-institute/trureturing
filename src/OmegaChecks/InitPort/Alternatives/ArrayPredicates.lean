module
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

end OmegaChecks.InitPort.Alternatives

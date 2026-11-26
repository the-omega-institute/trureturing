module
public import Init.Data.List.Lex

/-! Constructor proofs for lexicographic comparison of finite lists. -/
namespace OmegaChecks.InitPort.Alternatives

public theorem List.cons_lt_cons_self : type_of% @_root_.List.cons_lt_cons_self := by
  intro α a lt irrefl xs ys
  constructor
  · intro h
    cases h with
    | rel r => exact (irrefl.irrefl _ r).elim
    | cons r => exact r
  · exact _root_.List.Lex.cons

public theorem List.le_of_cons_le_cons : type_of% @_root_.List.le_of_cons_le_cons := by
  intros
  exact fun r => ‹_root_.List.le _ _› (_root_.List.Lex.cons r)

public theorem List.le_of_lt : type_of% @_root_.List.le_of_lt := by
  intros
  exact _root_.List.lt_asymm ‹_›

private theorem removePrefix {α : Type u} [LT α] [irrefl : Std.Irrefl (α := α) (· < ·)]
    (pre : _root_.List α) {xs ys : _root_.List α}
    (h : pre ++ xs < pre ++ ys) : xs < ys := by
  induction pre with
  | nil => exact h
  | cons a pre ih => exact ih (List.cons_lt_cons_self.mp h)

public theorem List.append_left_le : type_of% @_root_.List.append_left_le := by
  intros
  exact fun r => ‹_root_.List.le _ _› (removePrefix _ r)

public theorem List.le_append_left : type_of% @_root_.List.le_append_left := by
  intro α lt irrefl xs ys r
  exact _root_.List.not_lex_nil (removePrefix (xs := ys) (ys := []) xs
    (by rw [_root_.List.append_nil]; exact r))

public theorem List.map_lt : type_of% @_root_.List.map_lt := by
  intro α β lt₁ lt₂ xs ys f monotone h
  induction h with
  | nil => exact _root_.List.Lex.nil
  | rel h => exact _root_.List.Lex.rel (monotone _ _ h)
  | cons _ ih => exact _root_.List.Lex.cons ih

private theorem lexRelation {r s : α → α → Prop} (imp : ∀ a b, r a b → s a b)
    {xs ys : _root_.List α} (h : _root_.List.Lex r xs ys) : _root_.List.Lex s xs ys := by
  induction h with
  | nil => exact _root_.List.Lex.nil
  | rel h => exact _root_.List.Lex.rel (imp _ _ h)
  | cons _ ih => exact _root_.List.Lex.cons ih

public theorem List.lex_eq_true_iff_lt : type_of% @_root_.List.lex_eq_true_iff_lt := by
  intros
  apply (_root_.List.lex_eq_true_iff_lex _).trans
  exact ⟨lexRelation (fun _ _ => of_decide_eq_true), lexRelation (fun _ _ => decide_eq_true)⟩

public theorem List.lex_eq_false_iff_ge : type_of% @_root_.List.lex_eq_false_iff_ge := by
  intros
  exact Bool.eq_false_iff.trans (not_congr List.lex_eq_true_iff_lt)

public theorem List.lt_iff_exists : type_of% @_root_.List.lt_iff_exists := by
  intro α lt xs ys
  constructor
  · intro h
    induction h with
    | nil => exact .inl ⟨rfl, Nat.zero_lt_succ _⟩
    | rel h => exact .inr ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, fun _ hj => (Nat.not_lt_zero _ hj).elim, h⟩
    | @cons a xs ys h ih =>
      obtain (⟨eq, less⟩ | ⟨i, hx, hy, pre, atIndex⟩) := ih
      · exact .inl ⟨congrArg (a :: ·) eq, Nat.succ_lt_succ less⟩
      · refine .inr ⟨i+1, Nat.succ_lt_succ hx, Nat.succ_lt_succ hy, ?_, atIndex⟩
        intro j hj
        cases j with
        | zero => rfl
        | succ j => exact pre j (Nat.lt_of_succ_lt_succ hj)
  · induction xs generalizing ys with
    | nil =>
      rintro (⟨_, less⟩ | ⟨i, hi, _⟩)
      · cases ys with
        | nil => exact (Nat.lt_irrefl _ less).elim
        | cons => exact _root_.List.Lex.nil
      · exact (Nat.not_lt_zero _ hi).elim
    | cons x xs ih =>
      intro spec
      cases ys with
      | nil =>
        obtain (⟨_, less⟩ | ⟨i, _, hi, _⟩) := spec
        · exact (Nat.not_lt_zero _ less).elim
        · exact (Nat.not_lt_zero _ hi).elim
      | cons y ys =>
        obtain (⟨eq, less⟩ | ⟨i, hx, hy, pre, atIndex⟩) := spec
        · obtain ⟨rfl, rest⟩ := _root_.List.cons.inj eq
          exact _root_.List.Lex.cons (ih (.inl ⟨rest, Nat.lt_of_succ_lt_succ less⟩))
        · cases i with
          | zero => exact _root_.List.Lex.rel atIndex
          | succ i =>
            have heads : x = y := pre 0 (Nat.zero_lt_succ i)
            cases heads
            exact _root_.List.Lex.cons (ih (.inr ⟨i, Nat.lt_of_succ_lt_succ hx,
              Nat.lt_of_succ_lt_succ hy, fun j hj => pre (j+1) (Nat.succ_lt_succ hj), atIndex⟩))

private def DiffAt [BEq α] (lt : α → α → Bool) (xs ys : _root_.List α) :=
  ∃ (i : Nat) (hx : i < xs.length) (hy : i < ys.length),
    (∀ j, (h : j < i) → xs[j]'(Nat.lt_trans h hx) == ys[j]'(Nat.lt_trans h hy)) ∧ lt xs[i] ys[i]

private theorem diffAtCons [BEq α] {lt : α → α → Bool} {x y : α} {xs ys : _root_.List α} :
    DiffAt lt (x :: xs) (y :: ys) ↔ lt x y ∨ ((x == y) ∧ DiffAt lt xs ys) := by
  constructor
  · rintro ⟨i, hx, hy, pre, cmp⟩
    cases i with
    | zero => exact .inl cmp
    | succ i => exact .inr ⟨pre 0 (Nat.zero_lt_succ i), i, Nat.lt_of_succ_lt_succ hx,
        Nat.lt_of_succ_lt_succ hy, fun j hj => pre (j+1) (Nat.succ_lt_succ hj), cmp⟩
  · rintro (head | ⟨head, i, hx, hy, pre, cmp⟩)
    · exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, fun _ hj => (Nat.not_lt_zero _ hj).elim, head⟩
    · refine ⟨i+1, Nat.succ_lt_succ hx, Nat.succ_lt_succ hy, ?_, cmp⟩
      intro j hj
      cases j with
      | zero => exact head
      | succ j => exact pre j (Nat.lt_of_succ_lt_succ hj)

public theorem List.lex_eq_true_iff_exists : type_of% @_root_.List.lex_eq_true_iff_exists := by
  intro α xs ys eq lt
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro h; cases h
      · rintro (⟨_, h⟩ | ⟨_, h, _⟩) <;> exact (Nat.not_lt_zero _ h).elim
    | cons => exact ⟨fun _ => .inl ⟨rfl, Nat.zero_lt_succ _⟩, fun _ => rfl⟩
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h; cases h
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> exact (Nat.not_lt_zero _ h).elim
    | cons y ys =>
      constructor
      · intro h
        obtain (head | tail) := Bool.or_eq_true_iff.mp h
        · exact .inr (diffAtCons.mpr (.inl head))
        obtain ⟨eq, tail⟩ := Bool.and_eq_true_iff.mp tail
        obtain (⟨pre, len⟩ | diff) := (ih (ys := ys)).mp tail
        · exact .inl ⟨Bool.and_eq_true_iff.mpr ⟨eq, pre⟩, Nat.succ_lt_succ len⟩
        · exact .inr (diffAtCons.mpr (.inr ⟨eq, diff⟩))
      · rintro (⟨pre, len⟩ | diff)
        · obtain ⟨eq, pre⟩ := Bool.and_eq_true_iff.mp pre
          exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
            ⟨eq, (ih (ys := ys)).mpr (.inl ⟨pre, Nat.lt_of_succ_lt_succ len⟩)⟩))
        · obtain (head | ⟨eq, diff⟩) := diffAtCons.mp diff
          · exact Bool.or_eq_true_iff.mpr (.inl head)
          · exact Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
              ⟨eq, (ih (ys := ys)).mpr (.inr diff)⟩))

public theorem List.lex_eq_false_iff_exists : type_of% @_root_.List.lex_eq_false_iff_exists := by
  intro α xs ys eq sym lt irrefl asymm antisymm
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨fun _ => .inl rfl, fun _ => rfl⟩
    | cons =>
      constructor
      · intro h; cases h
      · rintro (h | ⟨_, hi, _⟩)
        · cases h
        · exact (Nat.not_lt_zero _ hi).elim
  | cons x xs ih =>
    cases ys with
    | nil => exact ⟨fun _ => .inl rfl, fun _ => rfl⟩
    | cons y ys =>
      constructor
      · intro h
        obtain ⟨xy, rest⟩ := Bool.or_eq_false_iff.mp h
        cases eqHead : x == y with
        | false =>
          cases rev : lt y x with
          | false => exact (Bool.noConfusion (eqHead.symm.trans (antisymm x y xy rev)))
          | true => exact .inr ((diffAtCons (lt := fun a b => lt b a)).mpr (.inl rev))
        | true =>
          rw [eqHead] at rest
          obtain (pre | diff) := (ih (ys := ys)).mp rest
          · exact .inl (Bool.and_eq_true_iff.mpr ⟨BEq.symm eqHead, pre⟩)
          · exact .inr ((diffAtCons (lt := fun a b => lt b a)).mpr (.inr ⟨eqHead, diff⟩))
      · rintro (pre | diff)
        · obtain ⟨eqHead, pre⟩ := Bool.and_eq_true_iff.mp pre
          have tail := (ih (ys := ys)).mpr (.inl pre)
          rw [_root_.List.cons_lex_cons, irrefl _ _ (BEq.symm eqHead), tail, Bool.and_false]
          rfl
        · obtain (rev | ⟨eqHead, diff⟩) := (diffAtCons (lt := fun a b => lt b a)).mp diff
          · have ne : (x == y) = false := by
              cases h : x == y with
              | false => rfl
              | true => exact Bool.noConfusion (rev.symm.trans (irrefl _ _ (BEq.symm h)))
            rw [_root_.List.cons_lex_cons, asymm _ _ rev, ne]; rfl
          · rw [_root_.List.cons_lex_cons, irrefl _ _ eqHead, eqHead, (ih (ys := ys)).mpr (.inr diff)]
            rfl

public theorem List.le_antisymm : type_of% @_root_.List.le_antisymm := by
  intro α _ law xs ys xy yx
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => exact False.elim (yx _root_.List.Lex.nil)
  | cons x xs ih =>
    cases ys with
    | nil => exact False.elim (xy _root_.List.Lex.nil)
    | cons y ys =>
      have head := law.trichotomous x y
        (fun lt => yx (_root_.List.Lex.rel lt)) (fun gt => xy (_root_.List.Lex.rel gt))
      cases head
      exact congrArg (x :: ·) (ih (fun lt => xy (_root_.List.Lex.cons lt)) (fun lt => yx (_root_.List.Lex.cons lt)))

open Std in
private theorem compareHeads [LE α] [LT α] [IsLinearOrder α] [LawfulOrderLT α] (a b : α) :
    ¬ ¬ (a < b ∨ a = b ∨ b < a) := by
  intro deny
  have ne : a ≠ b := fun e => deny (.inr (.inl e))
  cases (le_total : a ≤ b ∨ b ≤ a) with
  | inl le => exact deny (.inl (lt_of_le_of_ne le ne))
  | inr le => exact deny (.inr (.inr (lt_of_le_of_ne le ne.symm)))

open Std in
private theorem compareLists [LT α]
    (heads : ∀ x y : α, ¬ ¬ (x < y ∨ x = y ∨ y < x)) (xs ys : List α) :
    ¬ ¬ (xs < ys ∨ xs = ys ∨ ys < xs) := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact fun deny => deny (.inr (.inl rfl))
    | cons y ys => exact fun deny => deny (.inl (List.Lex.nil ..))
  | cons x xs ih =>
    cases ys with
    | nil => exact fun deny => deny (.inr (.inr (List.Lex.nil ..)))
    | cons y ys =>
      intro deny
      apply heads x y
      rintro (lt | rfl | gt)
      · exact deny (.inl (List.Lex.rel lt))
      · apply ih ys
        rintro (lt | rfl | gt)
        · exact deny (.inl (List.Lex.cons lt))
        · exact deny (.inr (.inl rfl))
        · exact deny (.inr (.inr (List.Lex.cons gt)))
      · exact deny (.inr (.inr (List.Lex.rel gt)))

public theorem List.le_trans : type_of% @_root_.List.le_trans := by
  intro α _ _ _ _ xs ys zs xy yz zx
  apply compareLists compareHeads xs ys
  rintro (lt | rfl | gt)
  · exact yz (_root_.List.lt_trans zx lt)
  · exact yz zx
  · exact xy gt

public theorem List.map_le : type_of% @_root_.List.map_le := by
  intro α β _ _ _ tri _ _ xs ys f monotone xy backwards
  apply compareLists (xs := xs) (ys := ys)
  · intro a b deny
    exact deny (.inr (.inl (tri.trichotomous a b
      (fun lt => deny (.inl lt)) (fun gt => deny (.inr (.inr gt))))))
  · rintro (lt | rfl | gt)
    · exact _root_.List.lt_asymm (List.map_lt monotone lt) backwards
    · exact _root_.List.lt_irrefl _ backwards
    · exact xy gt

end OmegaChecks.InitPort.Alternatives

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

end OmegaChecks.InitPort.Alternatives

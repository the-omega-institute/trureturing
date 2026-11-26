module
public import Init.Data.Vector.Lex

/-! The list, array and vector comparators inspect the same elements in order. -/
namespace OmegaChecks.InitPort.Alternatives

@[expose] public def Array.lex {α : Type u} [BEq α] (xs ys : _root_.Array α) (lt : α → α → Bool) : Bool :=
  xs.toList.lex ys.toList lt

@[expose] public def Vector.lex {α : Type u} {n : Nat} [BEq α] (xs ys : _root_.Vector α n)
    (lt : α → α → Bool) : Bool := Array.lex xs.toArray ys.toArray lt

public theorem List.lex_toArray {α : Type u} [BEq α] {lt : α → α → Bool} {xs ys : _root_.List α} :
    Array.lex xs.toArray ys.toArray lt = xs.lex ys lt := rfl

public theorem Array.lex_empty {α : Type u} [BEq α] {lt : α → α → Bool} {xs : _root_.Array α} :
    Array.lex xs #[] lt = false := _root_.List.lex_nil

public theorem Vector.mk_lex_mk {α : Type u} {n : Nat} [BEq α] {lt : α → α → Bool}
    {xs ys : _root_.Array α} {hx : xs.size = n} {hy : ys.size = n} :
    Vector.lex ⟨xs, hx⟩ ⟨ys, hy⟩ lt = Array.lex xs ys lt := rfl


public theorem Array.lex_eq_true_iff_lt : type_of% @_root_.Array.lex_eq_true_iff_lt := by
  intros
  rw [← _root_.Array.lex_toList]
  exact _root_.List.lex_eq_true_iff_lt

public theorem Array.lex_eq_false_iff_ge : type_of% @_root_.Array.lex_eq_false_iff_ge := by
  intros
  rw [← _root_.Array.lex_toList]
  exact _root_.List.lex_eq_false_iff_ge

public theorem Vector.lex_eq_true_iff_lt : type_of% @_root_.Vector.lex_eq_true_iff_lt := by
  intros
  rw [← _root_.Vector.lex_toArray]
  exact Array.lex_eq_true_iff_lt

public theorem Vector.lex_eq_false_iff_ge : type_of% @_root_.Vector.lex_eq_false_iff_ge := by
  intros
  rw [← _root_.Vector.lex_toArray]
  exact Array.lex_eq_false_iff_ge

public theorem Array.le_trans : type_of% @_root_.Array.le_trans := by
  intros
  apply _root_.List.le_trans <;> assumption

public theorem Vector.le_trans : type_of% @_root_.Vector.le_trans := by
  intros
  apply _root_.Array.le_trans <;> assumption

end OmegaChecks.InitPort.Alternatives

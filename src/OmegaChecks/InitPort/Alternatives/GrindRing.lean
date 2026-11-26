module
import all Init.Grind.Ring.CommSolver

/-! Structural decrease in reverse lexicographic comparison of monomials. -/

open Lean.Grind.CommRing
namespace OmegaChecks.InitPort.Alternatives

private theorem smallerTail (p : Power) (m : Mon) : sizeOf m < sizeOf (Mon.mult p m) :=
  Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (sizeOf p)))

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_2 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_2 := by
  intro p m q n
  apply Prod.Lex.left
  exact smallerTail p m

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_3 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_3 := by
  intro p m q n
  apply Prod.Lex.left
  exact smallerTail p m

public theorem Lean.Grind.CommRing.Mon.revlexWF._unary._proof_4 :
    type_of% @_root_.Lean.Grind.CommRing.Mon.revlexWF._unary._proof_4 := by
  intro p m q n
  apply Prod.Lex.right
  exact smallerTail q n

end OmegaChecks.InitPort.Alternatives

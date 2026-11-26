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

private theorem tailSize (k : Int) (m : Mon) (p : Poly) : sizeOf p < sizeOf (Poly.add k m p) :=
  Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (sizeOf k)))
    (Nat.le_add_right _ (sizeOf m)))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_1 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_1 :=
  fun k m p l n q => Nat.add_lt_add_of_lt_of_le (tailSize k m p) (Nat.le_of_lt (tailSize l n q))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_2 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_2 :=
  fun k m p l n q => Nat.add_lt_add_right (tailSize k m p) (sizeOf (Poly.add l n q))

public theorem Lean.Grind.CommRing.Poly.combineC._unary._proof_3 :
    type_of% @_root_.Lean.Grind.CommRing.Poly.combineC._unary._proof_3 :=
  fun k m p l n q => Nat.add_lt_add_left (tailSize l n q) (sizeOf (Poly.add k m p))

end OmegaChecks.InitPort.Alternatives

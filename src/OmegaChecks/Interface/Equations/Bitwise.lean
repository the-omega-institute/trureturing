module

public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.BitVec.Lemmas
public import OmegaChecks.InitPort.Alternatives.Word.BitwiseEquation
import all Init.Data.Nat.Bitwise.Basic

namespace OmegaChecks.Interface.Equations

public theorem BitVec.flattenListFast {n : Nat} (xs : List (BitVec n)) :
    _root_.BitVec.flattenList xs = _root_.BitVec.flattenListFast xs :=
  congrArg (fun k => @k n xs) _root_.BitVec.flattenList_eq_flattenListFast

public abbrev bitwiseSteps := OmegaChecks.InitPort.bitwiseSteps

private theorem steps_eq (f : Bool → Bool → Bool) (fuel n m : Nat) (h : n < fuel) :
    bitwiseSteps f fuel n m = _root_.Nat.bitwise f n m := by
  induction fuel generalizing n m with
  | zero => exact False.elim ((Nat.not_lt_zero n) h)
  | succ fuel ih =>
    cases n with
    | zero =>
      rw [_root_.Nat.bitwise]
      change Bool.casesOn (motive := fun _ => Nat) (f false true) 0 m = _
      cases hbit : f false true <;> simp
    | succ i =>
      cases m with
      | zero =>
        rw [_root_.Nat.bitwise]
        change Bool.casesOn (motive := fun _ => Nat) (f true false) 0 i.succ = _
        cases hbit : f true false <;> simp
      | succ j =>
        rw [_root_.Nat.bitwise]
        have smaller := ih (i.succ / 2) (j.succ / 2)
          (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.succ_pos i) (by decide)) (Nat.le_of_lt_succ h))
        change (Bool.casesOn (motive := fun _ => Nat) (f (decide (i.succ % 2 = 1)) (decide (j.succ % 2 = 1)))
          (bitwiseSteps f fuel (i.succ / 2) (j.succ / 2) + bitwiseSteps f fuel (i.succ / 2) (j.succ / 2))
          ((bitwiseSteps f fuel (i.succ / 2) (j.succ / 2) + bitwiseSteps f fuel (i.succ / 2) (j.succ / 2)).succ)) = _
        rw [smaller]
        cases hbit : f (decide (i.succ % 2 = 1)) (decide (j.succ % 2 = 1)) <;> simp [hbit]

public theorem Nat.bitwise (f : Bool → Bool → Bool) (n m : Nat) :
    bitwiseSteps f n.succ n m = _root_.Nat.bitwise f n m :=
  steps_eq f _ n m (Nat.lt_succ_self n)

public theorem Nat.xor (a b : Nat) :
    _root_.Nat.bitwise (@bne Bool (@instBEqOfDecidableEq Bool instDecidableEqBool)) a b = _root_.Nat.xor a b := by
  unfold _root_.Nat.xor
  rfl

end OmegaChecks.Interface.Equations

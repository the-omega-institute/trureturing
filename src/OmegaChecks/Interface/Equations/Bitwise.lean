module

public import Init.Data.Nat.Bitwise.Lemmas
import all Init.Data.Nat.Bitwise.Basic

namespace OmegaChecks.Interface.Equations

@[expose] public def bitwiseSteps (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => Nat.zero)
    (fun _ prev a b => Nat.casesOn (motive := fun _ => Nat) a
      (Bool.casesOn (motive := fun _ => Nat) (f Bool.false Bool.true) Nat.zero b)
      (fun i => Nat.casesOn (motive := fun _ => Nat) b
        (Bool.casesOn (motive := fun _ => Nat) (f Bool.true Bool.false) Nat.zero (Nat.succ i))
        (fun j =>
          let x := Nat.succ i
          let y := Nat.succ j
          let one := Nat.succ Nat.zero
          let two := Nat.succ one
          let r := prev (Nat.div x two) (Nat.div y two)
          let bit := f (Nat.beq (Nat.mod x two) one) (Nat.beq (Nat.mod y two) one)
          Bool.casesOn (motive := fun _ => Nat) bit (Nat.add r r) (Nat.succ (Nat.add r r)))))

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

end OmegaChecks.Interface.Equations

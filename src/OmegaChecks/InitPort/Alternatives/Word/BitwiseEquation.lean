module
public meta import Lean
public import Init.Data.Nat.Bitwise.Lemmas
import all Init.Data.Nat.Bitwise.Basic

/-! The first natural argument bounds the number of recursive bit comparisons. -/

namespace OmegaChecks.InitPort

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

namespace Alternatives

private def bitwiseSteps := value_of% OmegaChecks.InitPort.bitwiseSteps

public def Nat.bitwise (f : Bool → Bool → Bool) (n m : Nat) :=
  bitwiseSteps f n.succ n m

private theorem steps_stable (f : Bool → Bool → Bool) (fuel other n m : Nat)
    (h : n < fuel) (g : n < other) :
    bitwiseSteps f fuel n m = bitwiseSteps f other n m := by
  induction fuel generalizing other n m with
  | zero => exact False.elim (Nat.not_lt_zero n h)
  | succ fuel ih =>
    cases other with
    | zero => exact False.elim (Nat.not_lt_zero n g)
    | succ other =>
      cases n with
      | zero => rfl
      | succ i =>
        cases m with
        | zero => rfl
        | succ j =>
          have smaller := Nat.div_lt_self (Nat.succ_pos i) (by decide : 1 < 2)
          have recurse := ih other (i.succ / 2) (j.succ / 2)
            (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ h))
            (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ g))
          exact congrArg (fun r => Bool.casesOn (motive := fun _ => Nat)
            (f (Nat.beq (i.succ % 2) 1) (Nat.beq (j.succ % 2) 1)) (r + r) (r + r).succ) recurse

open Lean Elab Term in
local elab "bitwise_type% " t:term : term => do
  let ty ← elabTerm t none
  return ty.replace fun e => if e.isConstOf ``_root_.Nat.bitwise then some (mkConst ``Nat.bitwise) else none

public theorem _root_.OmegaChecks.InitPort.AlternativeEquations.Nat.bitwise.eq_def :
    bitwise_type% (type_of% (private_decl% @_root_.Nat.bitwise.eq_def)) := by
  intro f n m
  cases n with
  | zero =>
    change Bool.casesOn (motive := fun _ => Nat) (f false true) 0 m = _
    cases f false true <;> simp
  | succ i =>
    cases m with
    | zero =>
      change Bool.casesOn (motive := fun _ => Nat) (f true false) 0 i.succ = _
      cases f true false <;> simp
    | succ j =>
      have smaller := Nat.div_lt_self (Nat.succ_pos i) (by decide : 1 < 2)
      have recurse := steps_stable f i.succ (i.succ / 2).succ (i.succ / 2) (j.succ / 2)
        smaller (Nat.lt_succ_self _)
      change Bool.casesOn (motive := fun _ => Nat)
        (f (Nat.beq (i.succ % 2) 1) (Nat.beq (j.succ % 2) 1))
        (bitwiseSteps f i.succ (i.succ / 2) (j.succ / 2) + bitwiseSteps f i.succ (i.succ / 2) (j.succ / 2))
        (bitwiseSteps f i.succ (i.succ / 2) (j.succ / 2) + bitwiseSteps f i.succ (i.succ / 2) (j.succ / 2)).succ = _
      rw [recurse]
      change Bool.casesOn (motive := fun _ => Nat)
        (f (decide (i.succ % 2 = 1)) (decide (j.succ % 2 = 1))) _ _ = _
      cases bit : f (decide (i.succ % 2 = 1)) (decide (j.succ % 2 = 1)) <;> simp [bit, Nat.bitwise]

end Alternatives
end OmegaChecks.InitPort

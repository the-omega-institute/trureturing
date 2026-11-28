module
import all Init.Prelude
public import OmegaChecks.Interface.Equations
/-! The isolated arithmetic and the pinned native natural operations agree on each binary digit. -/

open OmegaChecks.Interface.Equations

namespace OmegaChecks.InitPort.HostedBitwise

private theorem divGo (d fuel x : Nat) (h : x < fuel) :
    divisionSteps d fuel x = Nat.div.go d.succ (Nat.succ_pos _) fuel x h := by
  induction fuel generalizing x with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ fuel ih =>
    change @Bool.rec (fun _ => Nat) 0 ((divisionSteps d fuel (x - d.succ)).succ)
      (Nat.ble d.succ x) = _
    unfold Nat.div.go
    cases lt : Nat.ble d.succ x with
    | false =>
      have no : ¬d.succ ≤ x := fun le =>
        Bool.noConfusion (lt.symm.trans (Nat.ble_eq_true_of_le le))
      rw [dite_eq_right no]
    | true =>
      have le := Nat.le_of_ble_eq_true lt
      rw [dite_eq_left le]
      exact congrArg Nat.succ (ih _ _)

private theorem modGo (d fuel x : Nat) (h : x < fuel) :
    remainderSteps d fuel x = Nat.modCore.go d.succ (Nat.succ_pos _) fuel x h := by
  induction fuel generalizing x with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ fuel ih =>
    change @Bool.rec (fun _ => Nat) x (remainderSteps d fuel (x - d.succ)) (Nat.ble d.succ x) = _
    unfold Nat.modCore.go
    cases lt : Nat.ble d.succ x with
    | false =>
      have no : ¬d.succ ≤ x := fun le =>
        Bool.noConfusion (lt.symm.trans (Nat.ble_eq_true_of_le le))
      rw [dite_eq_right no]
    | true =>
      have le := Nat.le_of_ble_eq_true lt
      rw [dite_eq_left le]
      exact ih _ _

@[expose] public noncomputable def slowDiv (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun d _ => divisionSteps d x.succ x) y
@[expose] public noncomputable def slowMod (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k _ =>
    Nat.rec (motive := fun _ => Nat) k.succ (fun d _ => remainderSteps d k.succ.succ k.succ) y) x

private theorem slowDiv_two (x : Nat) : slowDiv x 2 = Nat.div x 2 := by
  unfold Nat.div
  rw [dite_eq_left (show 0 < 2 from Nat.zero_lt_succ _)]
  exact divGo 1 x.succ x (Nat.lt_succ_self _)

private theorem slowMod_two (x : Nat) : slowMod x 2 = Nat.mod x 2 := by
  cases x with
  | zero => rfl
  | succ x =>
    cases x with
    | zero => rfl
    | succ x =>
      have le : 2 ≤ x.succ.succ := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
      unfold Nat.mod
      change remainderSteps 1 x.succ.succ.succ x.succ.succ =
        if 2 ≤ x.succ.succ then Nat.modCore x.succ.succ 2 else x.succ.succ
      rw [ite_eq_left le]
      unfold Nat.modCore
      rw [dite_eq_left (show 0 < 2 from Nat.zero_lt_succ _)]
      exact modGo 1 x.succ.succ.succ x.succ.succ (Nat.lt_succ_self _)

@[expose] public def steps (div mod : Nat → Nat → Nat) (f : Bool → Bool → Bool) :
    Nat → Nat → Nat → Nat :=
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
          let r := prev (div x two) (div y two)
          let bit := f (Nat.beq (mod x two) one) (Nat.beq (mod y two) one)
          Bool.casesOn (motive := fun _ => Nat) bit (Nat.add r r) (Nat.succ (Nat.add r r)))))

public theorem sameSteps (f : Bool → Bool → Bool) (fuel x y : Nat) :
    steps slowDiv slowMod f fuel x y = steps Nat.div Nat.mod f fuel x y := by
  induction fuel generalizing x y with
  | zero => rfl
  | succ fuel ih =>
    cases x with
    | zero => rfl
    | succ x => cases y with
      | zero => rfl
      | succ y =>
        let form (bit : Bool) (r : Nat) := @Bool.casesOn (fun _ => Nat) bit (r+r) (r+r).succ
        let sx := x.succ
        let sy := y.succ
        change form (f (Nat.beq (slowMod sx 2) 1) (Nat.beq (slowMod sy 2) 1))
          (steps slowDiv slowMod f fuel (slowDiv sx 2) (slowDiv sy 2)) =
          form (f (Nat.beq (Nat.mod sx 2) 1) (Nat.beq (Nat.mod sy 2) 1))
          (steps Nat.div Nat.mod f fuel (Nat.div sx 2) (Nat.div sy 2))
        rw [slowMod_two, slowMod_two, slowDiv_two, slowDiv_two, ih]

end OmegaChecks.InitPort.HostedBitwise

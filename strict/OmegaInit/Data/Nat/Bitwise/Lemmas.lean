module
prelude
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Nat

attribute [local semireducible] Nat.pow Nat.add Nat.mul Nat.bitwise

private def steps (f : Bool → Bool → Bool) : Nat → Nat → Nat → Nat :=
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

private theorem choose_lt (b : Bool) {u v limit : Nat} (hu : Nat.lt u limit) (hv : Nat.lt v limit) :
    Nat.lt (Bool.casesOn (motive := fun _ => Nat) b u v) limit :=
  Bool.casesOn (motive := fun t => Nat.lt (Bool.casesOn (motive := fun _ => Nat) t u v) limit) b hu hv

private theorem zero_lt_bound {x lim : Nat} (h : Nat.lt x lim) : Nat.lt zero lim :=
  Nat.le_trans (succ_le_succ (zero_le x)) h

private theorem half_lt {x n : Nat} (h : Nat.lt x (Nat.pow (succ (succ zero)) (succ n))) :
    Nat.lt (Nat.div x (succ (succ zero))) (Nat.pow (succ (succ zero)) n) :=
  (div_lt_iff_lt_mul (succ_le_succ (zero_le (succ zero)))).mpr h

private theorem doubled_lt {r limit : Nat} (h : Nat.lt r limit) :
    Nat.lt (succ (Nat.add r r)) (Nat.mul limit (succ (succ zero))) :=
  Eq.subst (motive := fun k => Nat.lt (succ (Nat.add r r)) k) (Nat.mul_two limit).symm
    (Eq.subst (motive := fun k => Nat.le k (Nat.add limit limit)) (succ_add r (succ r))
      (add_le_add h h))

/-- The bound on the left operand is needed only when the operation can return that operand at a zero right argument. -/
private def left_bound (f : Bool → Bool → Bool) (x limit : Nat) : Prop :=
  Eq (f Bool.true Bool.false) Bool.true → Nat.lt x limit

private theorem steps_small (f : Bool → Bool → Bool) (fuel : Nat) :
    ∀ n x y, left_bound f x (Nat.pow (succ (succ zero)) n) → Nat.lt y (Nat.pow (succ (succ zero)) n) →
      Nat.lt (steps f fuel x y) (Nat.pow (succ (succ zero)) n) :=
  Nat.rec (motive := fun fuel => ∀ n x y, left_bound f x (Nat.pow (succ (succ zero)) n) →
      Nat.lt y (Nat.pow (succ (succ zero)) n) → Nat.lt (steps f fuel x y) (Nat.pow (succ (succ zero)) n))
    (fun _ _ _ _ hy => zero_lt_bound hy)
    (fun fuel previous n x y =>
      let two := succ (succ zero)
      let limit := Nat.pow two n
      Nat.casesOn (motive := fun x => left_bound f x limit → Nat.lt y limit →
          Nat.lt (steps f (succ fuel) x y) limit) x
        (fun _ hy => choose_lt (f Bool.false Bool.true) (zero_lt_bound hy) hy)
        (fun i => Nat.casesOn (motive := fun y => left_bound f (succ i) limit → Nat.lt y limit →
            Nat.lt (steps f (succ fuel) (succ i) y) limit) y
          (fun hx hy =>
            Bool.casesOn (motive := fun b => Eq (f Bool.true Bool.false) b →
                Nat.lt (Bool.casesOn (motive := fun _ => Nat) b zero (succ i)) limit)
              (f Bool.true Bool.false) (fun _ => hy) hx Omega.rfl)
          (fun j =>
            Nat.casesOn (motive := fun n => left_bound f (succ i) (Nat.pow two n) → Nat.lt (succ j) (Nat.pow two n) →
                Nat.lt (steps f (succ fuel) (succ i) (succ j)) (Nat.pow two n)) n
              (fun _ hy => False.elim (not_succ_le_zero j (le_of_succ_le_succ hy)))
              (fun k hx hy =>
                let x := succ i
                let y := succ j
                let r := steps f fuel (Nat.div x two) (Nat.div y two)
                let bit := f (Nat.beq (Nat.mod x two) (succ zero)) (Nat.beq (Nat.mod y two) (succ zero))
                have recursive := previous k (Nat.div x two) (Nat.div y two) (fun e => half_lt (hx e)) (half_lt hy)
                have hi := doubled_lt recursive
                choose_lt bit (Nat.le_trans (Nat.le.step (Nat.le_refl (succ (Nat.add r r)))) hi) hi)))) fuel

theorem bitwise_lt_two_pow {x n y : Nat} {f : Bool → Bool → Bool}
    (left : Nat.lt x (Nat.pow (succ (succ zero)) n)) (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) :
    Nat.lt (bitwise f x y) (Nat.pow (succ (succ zero)) n) :=
  steps_small f (succ x) n x y (fun _ => left) right

theorem and_lt_two_pow (x : Nat) {y n : Nat} (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) :
    Nat.lt (Nat.land x y) (Nat.pow (succ (succ zero)) n) :=
  steps_small Bool.and (succ x) n x y (fun e => False.elim (Bool.ne_false_of_eq_true e Omega.rfl)) right

theorem or_lt_two_pow {x y n : Nat} (left : Nat.lt x (Nat.pow (succ (succ zero)) n))
    (right : Nat.lt y (Nat.pow (succ (succ zero)) n)) : Nat.lt (Nat.lor x y) (Nat.pow (succ (succ zero)) n) :=
  bitwise_lt_two_pow left right

end Omega.Nat

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Prelude
import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Nat

private def euclideanSteps : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ smaller a b => Nat.rec b (fun d _ => smaller (Nat.mod b (succ d)) (succ d)) a)

/-- A Euclidean step strictly decreases the first positive argument, so its successor
bounds the number of calls, including the final zero case. -/
@[extern "lean_nat_gcd", no_expose] def _root_.Nat.gcd (m n : @& Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ smaller a b => Nat.rec b (fun d _ => smaller (Nat.mod b (succ d)) (succ d)) a)
    (succ m) m n

export _root_.Nat (gcd)

theorem gcd_zero_right (n : Nat) : Eq (gcd n zero) n :=
  Nat.rec (motive := fun m => Eq (gcd m zero) m) Omega.rfl (fun _ _ => Omega.rfl) n

theorem gcd_one_left (n : Nat) : Eq (gcd (succ zero) n) (succ zero) :=
  (congrArg (fun m => Nat.rec (motive := fun _ => Nat)
    (succ zero) (fun d _ => succ d) m) (mod_one n)).trans Omega.rfl

private theorem steps_agree (fuel : Nat) : ∀ other a b, Nat.lt a fuel → Nat.lt a other →
    Eq (euclideanSteps fuel a b) (euclideanSteps other a b) :=
  Nat.rec (motive := fun f => ∀ g a b, Nat.lt a f → Nat.lt a g →
      Eq (euclideanSteps f a b) (euclideanSteps g a b))
    (fun _ a _ h _ => False.elim (not_succ_le_zero a h))
    (fun f ih g => Nat.casesOn (motive := fun g => ∀ a b, Nat.lt a (succ f) → Nat.lt a g →
        Eq (euclideanSteps (succ f) a b) (euclideanSteps g a b)) g
      (fun a _ _ h => False.elim (not_succ_le_zero a h))
      (fun g a => Nat.casesOn (motive := fun a => ∀ b, Nat.lt a (succ f) → Nat.lt a (succ g) →
          Eq (euclideanSteps (succ f) a b) (euclideanSteps (succ g) a b)) a
        (fun _ _ _ => Omega.rfl)
        (fun d b hf hg =>
          have smaller := Nat.mod_lt b (succ_le_succ (zero_le d))
          ih g (Nat.mod b (succ d)) (succ d)
            (Nat.le_trans smaller (le_of_succ_le_succ hf))
            (Nat.le_trans smaller (le_of_succ_le_succ hg))))) fuel

theorem gcd_zero_left (y : Nat) : Eq (gcd zero y) y := Omega.rfl

theorem gcd_succ (x y : Nat) : Eq (gcd (succ x) y) (gcd (Nat.mod y (succ x)) (succ x)) :=
  steps_agree (succ x) (succ (Nat.mod y (succ x))) (Nat.mod y (succ x)) (succ x)
    (Nat.mod_lt y (succ_le_succ (zero_le x))) (Nat.le_refl _)

theorem gcd_add_one (x y : Nat) : Eq (gcd (Nat.add x (succ zero)) y)
    (gcd (Nat.mod y (Nat.add x (succ zero))) (Nat.add x (succ zero))) := gcd_succ x y

theorem gcd_rec (m n : Nat) : Eq (gcd m n) (gcd (Nat.mod n m) m) :=
  Nat.casesOn (motive := fun m => Eq (gcd m n) (gcd (Nat.mod n m) m)) m
    ((gcd_zero_left n).trans ((gcd_zero_right n).symm.trans
      (congrArg (fun k => gcd k zero) (mod_zero n).symm)))
    (fun x => gcd_succ x n)

attribute [irreducible] gcd

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (gcd_add_one gcd_one_left gcd_rec gcd_succ gcd_zero_left gcd_zero_right)
end Nat

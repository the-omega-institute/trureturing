/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

@[expose] public section

namespace Omega.Nat

theorem zero_add (a : Nat) : Eq (add zero a) a :=
  Nat.rec (motive := fun n => Eq (add zero n) n)
    Eq.refl (fun _ h => congrArg succ h) a

theorem succ_add (a b : Nat) : Eq (add (succ a) b) (succ (add a b)) :=
  Nat.rec (motive := fun n => Eq (add (succ a) n) (succ (add a n)))
    Eq.refl (fun _ h => congrArg succ h) b

theorem add_assoc (a b c : Nat) : Eq (add (add a b) c) (add a (add b c)) :=
  Nat.rec (motive := fun n => Eq (add (add a b) n) (add a (add b n)))
    Eq.refl (fun _ h => congrArg succ h) c

theorem add_comm (a b : Nat) : Eq (add a b) (add b a) :=
  Nat.rec (motive := fun n => Eq (add a n) (add n a))
    (zero_add a).symm (fun n h => (congrArg succ h).trans (succ_add n a).symm) b

theorem add_right_comm (a b c : Nat) : Eq (add (add a b) c) (add (add a c) b) :=
  (add_assoc a b c).trans ((congrArg (add a) (add_comm b c)).trans (add_assoc a c b).symm)

theorem zero_mul (a : Nat) : Eq (mul zero a) zero :=
  Nat.rec (motive := fun n => Eq (mul zero n) zero) Eq.refl (fun _ h => h) a

theorem succ_mul (a b : Nat) : Eq (mul (succ a) b) (add (mul a b) b) :=
  Nat.rec (motive := fun n => Eq (mul (succ a) n) (add (mul a n) n))
    Eq.refl (fun n h =>
      congrArg succ ((congrArg (fun x => add x a) h).trans (add_right_comm (mul a n) n a))) b

theorem mul_comm (a b : Nat) : Eq (mul a b) (mul b a) :=
  Nat.rec (motive := fun n => Eq (mul a n) (mul n a)) (zero_mul a).symm
    (fun n h => (congrArg (fun x => add x a) h).trans (succ_mul n a).symm) b

theorem one_mul (a : Nat) : Eq (mul (succ zero) a) a :=
  (mul_comm (succ zero) a).trans (zero_add a)

theorem mul_add (a b c : Nat) : Eq (mul a (add b c)) (add (mul a b) (mul a c)) :=
  Nat.rec (motive := fun n => Eq (mul a (add b n)) (add (mul a b) (mul a n)))
    Eq.refl (fun n h => (congrArg (fun x => add x a) h).trans (add_assoc (mul a b) (mul a n) a)) c

theorem add_mul (a b c : Nat) : Eq (mul (add a b) c) (add (mul a c) (mul b c)) :=
  (mul_comm (add a b) c).trans ((mul_add c a b).trans
    ((congrArg (fun x => add x (mul c b)) (mul_comm c a)).trans
      (congrArg (add (mul a c)) (mul_comm c b))))

theorem mul_assoc (a b c : Nat) : Eq (mul (mul a b) c) (mul a (mul b c)) :=
  Nat.rec (motive := fun n => Eq (mul (mul a b) n) (mul a (mul b n))) Eq.refl
    (fun n h => (congrArg (fun x => add x (mul a b)) h).trans (mul_add a (mul b n) b).symm) c

end Omega.Nat

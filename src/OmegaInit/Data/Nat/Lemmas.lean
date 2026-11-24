/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Nat.Basic

@[expose] public section

namespace Omega.Nat

theorem mul_right_comm (a b c : Nat) : Eq (mul (mul a b) c) (mul (mul a c) b) :=
  (mul_assoc a b c).trans ((congrArg (mul a) (mul_comm b c)).trans (mul_assoc a c b).symm)

theorem mul_eq_zero {a b : Nat} : Iff (Eq (mul a b) zero) (Or (Eq a zero) (Eq b zero)) :=
  Iff.intro
    (Nat.rec (motive := fun b => Eq (mul a b) zero → Or (Eq a zero) (Eq b zero))
      (fun _ => Or.inr Eq.refl)
      (fun _ _ h => Or.inl (eq_zero_of_add_eq_zero h).right) b)
    (fun h => h.elim
      (fun ha => Eq.subst (fun a => Eq (mul a b) zero) ha.symm (zero_mul b))
      (fun hb => Eq.subst (fun b => Eq (mul a b) zero) hb.symm Eq.refl))

end Omega.Nat

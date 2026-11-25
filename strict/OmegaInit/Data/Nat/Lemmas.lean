/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Data.Nat.Basic

@[expose] public section

attribute [local semireducible] Omega.Nat.mul

namespace Omega.Nat

protected theorem mul_right_comm (n m k : Nat) : Eq (Nat.mul (Nat.mul n m) k) (Nat.mul (Nat.mul n k) m) :=
  (Nat.mul_assoc n m k).trans ((congrArg (Nat.mul n) (Nat.mul_comm m k)).trans (Nat.mul_assoc n k m).symm)

theorem mul_eq_zero {m n : Nat} : Iff (Eq (Nat.mul n m) zero) (Or (Eq n zero) (Eq m zero)) :=
  Iff.intro
    (Nat.rec (motive := fun m => Eq (Nat.mul n m) zero → Or (Eq n zero) (Eq m zero))
      (fun _ => Or.inr rfl)
      (fun _ _ h => Or.inl (eq_zero_of_add_eq_zero h).right) m)
    (fun h => h.elim
      (fun ha => Eq.subst (motive := fun n => Eq (Nat.mul n m) zero) ha.symm (Nat.zero_mul m))
      (fun hb => Eq.subst (motive := fun m => Eq (Nat.mul n m) zero) hb.symm rfl))

end Omega.Nat

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Int.Lemmas

@[expose] public section

namespace Omega.Int

theorem natAbs_negOfNat (n : Nat) : Eq (natAbs (negOfNat n)) n :=
  Nat.rec (motive := fun n => Eq (natAbs (negOfNat n)) n) Eq.refl (fun _ _ => Eq.refl) n

theorem natAbs_neg (a : Int) : Eq a.neg.natAbs a.natAbs :=
  Int.rec (motive := fun a => Eq a.neg.natAbs a.natAbs) natAbs_negOfNat (fun _ => Eq.refl) a

theorem natAbs_eq_zero {a : Int} : Iff (Eq a.natAbs Nat.zero) (Eq a (ofNat Nat.zero)) :=
  Iff.intro
    (Int.rec (motive := fun a => Eq a.natAbs Nat.zero → Eq a (ofNat Nat.zero))
      (fun _ h => congrArg ofNat h)
      (fun n h => False.elim (Nat.succ_ne_zero n h)) a)
    (congrArg natAbs)

theorem natAbs_mul (a b : Int) : Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs) :=
  Int.rec (motive := fun a => Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).mul b).natAbs (m.mul b.natAbs))
      (fun _ => Eq.refl) (fun n => natAbs_negOfNat (m.mul n.succ)) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).mul b).natAbs (m.succ.mul b.natAbs))
      (fun n => natAbs_negOfNat (m.succ.mul n)) (fun _ => Eq.refl) b) a

theorem natAbs_mul_self {a : Int} : Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a) :=
  Int.rec (motive := fun a => Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a))
    (fun _ => Eq.refl) (fun _ => Eq.refl) a

end Omega.Int

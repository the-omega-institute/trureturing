/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Int.Basic
import OmegaInit.Data.Int.Lemmas
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude

@[expose] public section

attribute [local semireducible] Omega.Nat.add Omega.Int.subNatNat

namespace Omega.Int

theorem natAbs_negOfNat (n : Nat) : Eq (natAbs (negOfNat n)) n :=
  Nat.rec (motive := fun n => Eq (natAbs (negOfNat n)) n) rfl (fun _ _ => rfl) n

theorem natAbs_neg (a : Int) : Eq a.neg.natAbs a.natAbs :=
  Int.rec (motive := fun a => Eq a.neg.natAbs a.natAbs) natAbs_negOfNat (fun _ => rfl) a

theorem natAbs_eq_zero {a : Int} : Iff (Eq a.natAbs Nat.zero) (Eq a (ofNat Nat.zero)) :=
  Iff.intro
    (Int.rec (motive := fun a => Eq a.natAbs Nat.zero → Eq a (ofNat Nat.zero))
      (fun _ h => congrArg ofNat h)
      (fun n h => False.elim (Nat.succ_ne_zero n h)) a)
    (congrArg natAbs)

theorem natAbs_mul (a b : Int) : Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs) :=
  Int.rec (motive := fun a => Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).mul b).natAbs (m.mul b.natAbs))
      (fun _ => rfl) (fun n => natAbs_negOfNat (m.mul n.succ)) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).mul b).natAbs (m.succ.mul b.natAbs))
      (fun n => natAbs_negOfNat (m.succ.mul n)) (fun _ => rfl) b) a

theorem natAbs_mul_self {a : Int} : Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a) :=
  Int.rec (motive := fun a => Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a))
    (fun _ => rfl) (fun _ => rfl) a

theorem ofNat_succ_pos (n : Nat) : (ofNat Nat.zero).lt (ofNat n.succ) :=
  Nat.rec (motive := fun k => (ofNat Nat.zero).lt (ofNat k.succ))
    (NonNeg.mk _) (fun _ _ => NonNeg.mk _) n

end Omega.Int

/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Kim Morrison, Markus Himmel
-/
module
prelude
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Nat.Div.Basic
import OmegaInit.Data.Int.Order

public section
namespace Omega.Int

theorem natAbs_tdiv (a b : Int) : Eq (a.tdiv b).natAbs (Nat.div a.natAbs b.natAbs) :=
  Int.rec (motive := fun a => Eq (a.tdiv b).natAbs (Nat.div a.natAbs b.natAbs))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).tdiv b).natAbs (Nat.div m b.natAbs))
      (fun _ => rfl) (fun n => natAbs_negOfNat (Nat.div m n.succ)) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).tdiv b).natAbs (Nat.div m.succ b.natAbs))
      (fun n => natAbs_negOfNat (Nat.div m.succ n)) (fun _ => rfl) b) a

theorem tdiv_eq_zero_iff_natAbs_lt_or_eq_zero {a b : Int} :
    Iff (Eq (a.tdiv b) (ofNat Nat.zero)) (Or (Nat.lt a.natAbs b.natAbs) (Eq b (ofNat Nat.zero))) :=
  let absolute := natAbs_tdiv a b
  Iff.intro
    (fun zero => (Nat.eq_zero_or_pos b.natAbs).elim
      (fun h => Or.inr (natAbs_eq_zero.mp h))
      (fun pos =>
        let divZero := absolute.symm.trans (natAbs_eq_zero.mpr zero)
        let small := Eq.subst (motive := fun n => Nat.lt n Nat.zero.succ) divZero.symm Nat.zero_lt_one
        Or.inl (Eq.subst (motive := Nat.lt a.natAbs) (Nat.one_mul b.natAbs)
          ((Nat.div_lt_iff_lt_mul pos).mp small))))
    (fun cases => natAbs_eq_zero.mp (absolute.trans (cases.elim Nat.div_eq_of_lt
      (fun zero => (congrArg (Nat.div a.natAbs) (natAbs_eq_zero.mpr zero)).trans (Nat.div_zero a.natAbs)))))

end Omega.Int

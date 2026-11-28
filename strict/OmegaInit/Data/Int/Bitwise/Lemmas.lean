/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Jeremy Avigad
-/
module
prelude
public import OmegaInit.Data.Int.Bitwise.Basic
import all OmegaInit.Data.Int.Bitwise.Basic
public import OmegaInit.Data.Int.DivMod.Basic
import OmegaInit.Data.Int.DivMod.Bootstrap
import OmegaInit.Data.Int.Lemmas
import OmegaInit.Data.Int.Order
import OmegaInit.Data.Nat.Lemmas
import OmegaInit.Data.Nat.Bitwise.Lemmas
import OmegaInit.Data.Nat.Div.Lemmas

namespace Omega.Int

private abbrev power (n : Nat) := Nat.pow 2 n
private abbrev factor (n : Nat) := Int.ofNat (power n)

private theorem rightAdd (a : Int) (m n : Nat) :
    Eq (Int.shiftRight a (Nat.add m n)) (Int.shiftRight (Int.shiftRight a m) n) :=
  Int.casesOn (motive := fun x => Eq (Int.shiftRight x (Nat.add m n)) (Int.shiftRight (Int.shiftRight x m) n)) a
    (fun x => congrArg ofNat (Nat.shiftRight_add x m n))
    (fun x => congrArg negSucc (Nat.shiftRight_add x m n))

private theorem edivNeg (a p : Nat) : Nat.lt 0 p →
    Eq (Int.ediv (negSucc a) (ofNat p)) (negSucc (Nat.div a p)) :=
  Nat.casesOn (motive := fun p => Nat.lt 0 p →
    Eq (Int.ediv (negSucc a) (ofNat p)) (negSucc (Nat.div a p))) p
    (fun h => False.elim (Nat.lt_irrefl 0 h)) (fun k _ => @Int.negSucc_ediv_ofNat_succ a k)

private theorem rightDiv (a : Int) (n : Nat) :
    Eq (Int.shiftRight a n) (Int.ediv a (factor n)) :=
  Int.casesOn (motive := fun z => Eq (Int.shiftRight z n) (Int.ediv z (factor n))) a
    (fun z => congrArg ofNat (Nat.shiftRight_eq_div_pow z n))
    (fun z => (congrArg negSucc (Nat.shiftRight_eq_div_pow z n)).trans (edivNeg z (power n) (Nat.two_pow_pos n)).symm)

private theorem rightZero (a : Int) : Eq (Int.shiftRight a 0) a :=
  Int.casesOn (motive := fun a => Eq (Int.shiftRight a 0) a) a (fun _ => rfl) (fun _ => rfl)

private theorem zeroRight (n : Nat) : Eq (Int.shiftRight (ofNat 0) n) (ofNat 0) :=
  congrArg ofNat (Nat.le_zero.mp (Nat.shiftRight_le 0 n))

private theorem negPred {x : Nat} : Nat.lt 0 x → Eq (negSucc (Nat.sub x 1)) (negOfNat x) :=
  Nat.casesOn (motive := fun x => Nat.lt 0 x → Eq (negSucc (Nat.sub x 1)) (negOfNat x)) x
    (fun h => False.elim (Nat.lt_irrefl 0 h)) (fun _ _ => rfl)

private theorem leftMul (a : Int) (n : Nat) : Eq (Int.shiftLeft a n) (Int.mul a (factor n)) :=
  Int.casesOn (motive := fun a => Eq (Int.shiftLeft a n) (Int.mul a (factor n))) a
    (fun x => congrArg ofNat (Nat.shiftLeft_eq x n))
    (fun x => (congrArg (fun t => negSucc (Nat.sub t 1)) (Nat.shiftLeft_eq x.succ n)).trans
      (negPred (Nat.mul_pos (Nat.zero_lt_succ x) (Nat.two_pow_pos n))))

private theorem leftZero (a : Int) : Eq (Int.shiftLeft a 0) a :=
  (leftMul a 0).trans (Int.mul_one a)

private theorem zeroLeft (n : Nat) : Eq (Int.shiftLeft (ofNat 0) n) (ofNat 0) :=
  (leftMul (ofNat 0) n).trans (Int.zero_mul (factor n))

private theorem factorAdd (m n : Nat) : Eq (factor (Nat.add m n)) (Int.mul (factor m) (factor n)) :=
  congrArg ofNat (Nat.pow_add 2 m n)

private theorem leftAdd (a : Int) (m n : Nat) :
    Eq (Int.shiftLeft a (Nat.add m n)) (Int.shiftLeft (Int.shiftLeft a m) n) :=
  (leftMul a (Nat.add m n)).trans ((congrArg (Int.mul a) (factorAdd m n)).trans
    ((Int.mul_assoc a (factor m) (factor n)).symm.trans
      ((congrArg (fun b => Int.mul b (factor n)) (leftMul a m).symm).trans (leftMul (Int.shiftLeft a m) n).symm)))

private theorem leftSucc (a : Int) (n : Nat) : Eq (Int.shiftLeft a (Nat.succ n)) (Int.mul (Int.shiftLeft a n) (ofNat 2)) :=
  (leftAdd a n 1).trans (leftMul (Int.shiftLeft a n) 1)

private theorem negativeOrder {m k : Nat} (h : Nat.le k m) : (negSucc m).le (negSucc k) :=
  Eq.subst (motive := NonNeg) (Int.add_comm (ofNat m.succ) (negSucc k))
    (ofNat_le.mpr (Nat.succ_le_succ h))

private theorem nonposBelowRight {a : Int} {s : Nat} : a.le (ofNat 0) → a.le (Int.shiftRight a s) :=
  Int.casesOn (motive := fun x => x.le (ofNat 0) → x.le (Int.shiftRight x s)) a
    (fun _ h => ofNat_le.mpr (Nat.le_trans (ofNat_le.mp h) (Nat.zero_le _)))
    (fun n _ => negativeOrder (Nat.shiftRight_le n s))

private theorem rightBelowNonneg {a : Int} {s : Nat} : (ofNat 0).le a → (Int.shiftRight a s).le a :=
  Int.casesOn (motive := fun x => (ofNat 0).le x → (Int.shiftRight x s).le x) a
    (fun n _ => ofNat_le.mpr (Nat.shiftRight_le n s))
    (fun n h => False.elim ((negSucc_not_nonneg n).mp h))

private theorem rightNonneg {a : Int} {s : Nat} : (ofNat 0).le a → (ofNat 0).le (Int.shiftRight a s) :=
  Int.casesOn (motive := fun x => (ofNat 0).le x → (ofNat 0).le (Int.shiftRight x s)) a
    (fun n _ => ofNat_zero_le (Nat.shiftRight n s))
    (fun n h => False.elim ((negSucc_not_nonneg n).mp h))

private theorem rightNonpos {a : Int} {s : Nat} : a.le (ofNat 0) → (Int.shiftRight a s).le (ofNat 0) :=
  Int.casesOn (motive := fun x => x.le (ofNat 0) → (Int.shiftRight x s).le (ofNat 0)) a
    (fun n h => ofNat_le.mpr (Nat.le_trans (Nat.shiftRight_le n s) (ofNat_le.mp h)))
    (fun n _ => Int.le_of_lt (negSucc_lt_zero (Nat.shiftRight n s)))

private theorem leftRight (a : Int) (n : Nat) : Eq (Int.shiftRight (Int.shiftLeft a n) n) a :=
  (rightDiv (Int.shiftLeft a n) n).trans
    ((congrArg (fun x => Int.ediv x (factor n)) (leftMul a n)).trans
      (Int.mul_ediv_cancel a (fun e => Nat.ne_of_gt (Nat.two_pow_pos n) (ofNat_inj.mp e))))

private theorem leftRightLe {b c : Nat} (h : Nat.le c b) (a : Int) :
    Eq (Int.shiftRight (Int.shiftLeft a b) c) (Int.shiftLeft a (Nat.sub b c)) :=
  let shifted := (congrArg (Int.shiftLeft a) (Nat.sub_add_cancel h).symm).trans (leftAdd a (Nat.sub b c) c)
  (congrArg (fun x => Int.shiftRight x c) shifted).trans (leftRight (Int.shiftLeft a (Nat.sub b c)) c)

private theorem leftZeroIff {a : Int} {n : Nat} : Iff (Eq (Int.shiftLeft a n) (ofNat 0)) (Eq a (ofNat 0)) :=
  Iff.intro
    (fun h => (leftRight a n).symm.trans ((congrArg (fun x => Int.shiftRight x n) h).trans (zeroRight n)))
    (fun h => (congrArg (fun x => Int.shiftLeft x n) h).trans (zeroLeft n))

end Omega.Int

port_proof Int.shiftLeft.eq_1 by_reflexivity
port_proof Int.shiftLeft.eq_2 by_reflexivity
port_proof Int.shiftRight.eq_1 by_reflexivity
port_proof Int.shiftRight.eq_2 by_reflexivity
port_proof Int.shiftRight_eq by_reflexivity
port_proof Int.natCast_shiftRight by_reflexivity
port_proof Int.negSucc_shiftRight by_reflexivity
port_proof Int.shiftRight_add using Omega.Int.rightAdd
port_proof Int.shiftRight_eq_div_pow using Omega.Int.rightDiv
port_proof Int.zero_shiftRight using Omega.Int.zeroRight
port_proof Int.shiftRight_zero using Omega.Int.rightZero
port_proof Int.le_shiftRight_of_nonpos using Omega.Int.nonposBelowRight
port_proof Int.shiftRight_le_of_nonneg using Omega.Int.rightBelowNonneg
port_proof Int.le_shiftRight_of_nonneg using Omega.Int.rightNonneg
port_proof Int.shiftRight_le_of_nonpos using Omega.Int.rightNonpos
port_proof Int.natCast_shiftLeft by_reflexivity
port_proof Int.zero_shiftLeft using Omega.Int.zeroLeft
port_proof Int.shiftLeft_zero using Omega.Int.leftZero
port_proof Int.shiftLeft_succ using Omega.Int.leftSucc
port_proof Int.shiftLeft_succ'
port_proof Int.shiftLeft_eq using Omega.Int.leftMul
port_proof Int.shiftLeft_eq' using Omega.Int.leftMul
port_proof Int.shiftLeft_add using Omega.Int.leftAdd
port_proof Int.shiftLeft_shiftRight_cancel using Omega.Int.leftRight
port_proof Int.shiftLeft_shiftRight_eq_shiftLeft_of_le using Omega.Int.leftRightLe
port_proof Int.shiftLeft_shiftRight_eq_shiftRight_of_le by_constructive_casts
port_proof Int.shiftLeft_shiftRight_eq by_constructive_casts
port_proof Int.shiftRight_shiftLeft_cancel by_constructive_casts
port_proof Int.add_shiftLeft by_constructive_casts
port_proof Int.neg_shiftLeft by_constructive_casts
port_proof Int.shiftLeft_mul by_constructive_casts
port_proof Int.mul_shiftLeft by_constructive_casts
port_proof Int.shiftLeft_mul_shiftLeft by_constructive_casts
port_proof Int.shiftLeft_eq_zero_iff using Omega.Int.leftZeroIff
port_proof Int.instNeZeroHShiftLeftNat
attribute [instance] Omega.Int.instNeZeroHShiftLeftNat

/- The generated simp helpers ask for equalities of propositions.
Int.shiftLeft_eq_zero_iff._simp_1 turns the public equivalence above into equality by propext.
The private Int.shiftLeft_eq_zero_iff._simp_1_1 uses propext on Int.mul_eq_zero.
The private Int.shiftLeft_eq_zero_iff._simp_1_2 uses eq_false on the NeZero hypothesis. -/

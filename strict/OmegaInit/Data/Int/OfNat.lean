/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.Data.Int.Basic
public import OmegaInit.Data.Int.DivMod.Basic
public import OmegaInit.Data.Cast
public import OmegaInit.Core
import OmegaInit.Data.Int.Order
import OmegaInit.Data.Int.Lemmas
import OmegaInit.Data.Nat.Basic
import all OmegaInit.Prelude

port_definition Int.Nonneg.num_cert with_native_code
@[expose] public section
namespace Omega.Nat.ToInt

private theorem proveAddCongr {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b') :
    Eq (Int.ofNat (Nat.add a b)) (a'.add b') :=
  (congrArg (fun z => Int.add z (Int.ofNat b)) ha).trans (congrArg (Int.add a') hb)

private theorem proveMulCongr {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b') :
    Eq (Int.ofNat (Nat.mul a b)) (a'.mul b') :=
  (congrArg (fun z => Int.mul z (Int.ofNat b)) ha).trans (congrArg (Int.mul a') hb)

private theorem proveDivCongr {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b') :
    Eq (Int.ofNat (Nat.div a b)) (a'.ediv b') :=
  (Int.natCast_ediv ..).trans
    ((congrArg (fun z => Int.ediv z (Int.ofNat b)) ha).trans (congrArg (Int.ediv a') hb))

private theorem proveModCongr {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b') :
    Eq (Int.ofNat (Nat.mod a b)) (a'.emod b') :=
  (congrArg (fun z => Int.emod z (Int.ofNat b)) ha).trans (congrArg (Int.emod a') hb)

private theorem proveOfNotLe {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b')
    (h : Not (Nat.le a b)) : (b'.add (Int.ofNat Nat.zero.succ)).le a' :=
  Eq.subst (motive := fun x => (b'.add (Int.ofNat Nat.zero.succ)).le x) ha
    (Eq.subst (motive := fun y => (y.add (Int.ofNat Nat.zero.succ)).le (Int.ofNat a)) hb
      (Int.ofNat_le.mpr (Nat.lt_of_not_ge h)))

end Omega.Nat.ToInt
port_proof Nat.ToInt.add_congr using Omega.Nat.ToInt.proveAddCongr
port_proof Nat.ToInt.mul_congr using Omega.Nat.ToInt.proveMulCongr
port_proof Nat.ToInt.div_congr using Omega.Nat.ToInt.proveDivCongr
port_proof Nat.ToInt.mod_congr using Omega.Nat.ToInt.proveModCongr
port_proof Nat.ToInt.of_not_le using Omega.Nat.ToInt.proveOfNotLe
port_proof Nat.ToInt.finVal
port_proof Nat.ToInt.natCast_ofNat
namespace Omega.Nat.ToInt

private abbrev cutoff (a : Int) := @ite Int (a.le (Int.ofNat Nat.zero))
  (Int.decLe a (Int.ofNat Nat.zero)) (Int.ofNat Nat.zero) a

private theorem clampNat (a : Int) : Eq (Int.ofNat a.toNat) (cutoff a) :=
  Int.casesOn (motive := fun a => Eq (Int.ofNat a.toNat) (cutoff a)) a
    (fun n => (@Decidable.em ((Int.ofNat n).le (Int.ofNat Nat.zero))
        (Int.decLe (Int.ofNat n) (Int.ofNat Nat.zero))).elim
      (fun h => (Int.le_antisymm h (Int.natCast_nonneg n)).trans (ite_eq_left h).symm)
      (fun h => (ite_eq_right h).symm))
    (fun n => (ite_eq_left (Int.le.intro_sub n.succ (Int.zero_sub (Int.negSucc n)))).symm)

end Omega.Nat.ToInt
port_proof Nat.ToInt.ofNat_toNat using Omega.Nat.ToInt.clampNat
port_proof Nat.ToInt.of_diseq
namespace Omega.Nat.ToInt

private theorem proveOfDvd (d a : Nat) (d' a' : Int) (hd : Eq (Int.ofNat d) d') (ha : Eq (Int.ofNat a) a')
    (w : Exists (fun q : Nat => Eq a (Nat.mul d q))) : Exists (fun z : Int => Eq a' (Int.mul d' z)) :=
  w.elim fun q hq => Exists.intro (Int.ofNat q)
    ((ha.symm.trans (congrArg Int.ofNat hq)).trans (congrArg (fun z => Int.mul z (Int.ofNat q)) hd))

private theorem provePowCongr {a : Nat} (k : Nat) (a' : Int) (ha : Eq (Int.ofNat a) a') :
    Eq (Int.ofNat (Nat.pow a k)) (Int.pow a' k) := congrArg (fun z => Int.pow z k) ha

end Omega.Nat.ToInt
port_proof Nat.ToInt.of_dvd using Omega.Nat.ToInt.proveOfDvd
port_proof Nat.ToInt.pow_congr using Omega.Nat.ToInt.provePowCongr
port_proof Nat.ToInt.of_eq
port_proof Nat.ToInt.of_le
namespace Omega.Nat.ToInt

private abbrev difference (a b : Int) :=
  let value := b.add ((Int.negSucc Nat.zero).mul a)
  @ite Int (value.le (Int.ofNat Nat.zero)) (Int.decLe value (Int.ofNat Nat.zero))
    (a.sub b) (Int.ofNat Nat.zero)

private theorem onNaturals (a b : Nat) : Eq (Int.ofNat (Nat.sub a b)) (difference (Int.ofNat a) (Int.ofNat b)) :=
  let x := Int.ofNat a
  let y := Int.ofNat b
  let normalized : Eq (y.add ((Int.negSucc Nat.zero).mul x)) (y.sub x) :=
    congrArg y.add (congrArg Int.negOfNat (Nat.one_mul a))
  (@Decidable.em (Nat.le b a) (Nat.decLe b a)).elim
    (fun h =>
      have bound := Int.sub_le_sub_right (Int.ofNat_le.mpr h) x
      have accepted := Eq.subst (motive := fun t => t.le (Int.ofNat Nat.zero)) normalized.symm
        (Eq.subst (motive := (y.sub x).le) (Int.sub_self x) bound)
      (Int.ofNat_sub h).trans (ite_eq_left accepted).symm)
    (fun h =>
      have rejected : Not ((y.add ((Int.negSucc Nat.zero).mul x)).le (Int.ofNat Nat.zero)) := fun bound =>
        h (Int.ofNat_le.mp (Int.le_of_sub_le_sub_right
          (Eq.subst (motive := (y.sub x).le) (Int.sub_self x).symm
            (Eq.subst (motive := fun t => t.le (Int.ofNat Nat.zero)) normalized bound))))
      have small : Nat.le a b := Nat.le_trans (Nat.le.step (Nat.le_refl a)) (Nat.lt_of_not_ge h)
      have vanished := (Nat.le.dest small).elim (fun k e =>
        Eq.subst (motive := fun t => Eq (Nat.sub a t) Nat.zero) e (Nat.sub_self_add a k))
      (congrArg Int.ofNat vanished).trans (ite_eq_right rejected).symm)

private theorem differenceCast {a b : Nat} {a' b' : Int} (ha : Eq (Int.ofNat a) a') (hb : Eq (Int.ofNat b) b') :
    Eq (Int.ofNat (Nat.sub a b)) (difference a' b') :=
  (onNaturals a b).trans
    ((congrArg (fun z => difference z (Int.ofNat b)) ha).trans (congrArg (difference a') hb))

end Omega.Nat.ToInt
port_proof Nat.ToInt.sub_congr using Omega.Nat.ToInt.differenceCast
port_proof Int.Nonneg.num_cert.eq_1
namespace Omega.Int.Nonneg

private theorem ofNaturalArguments (f : Int → Int → Int) (g : Nat → Nat → Nat)
    (onNat : ∀ m n, Eq (f (Int.ofNat m) (Int.ofNat n)) (Int.ofNat (g m n)))
    (a b : Int) (ha : (Int.ofNat Nat.zero).le a) (hb : (Int.ofNat Nat.zero).le b) :
    (Int.ofNat Nat.zero).le (f a b) :=
  (Int.eq_ofNat_of_zero_le ha).elim fun m hm =>
    (Int.eq_ofNat_of_zero_le hb).elim fun n hn =>
      Eq.subst (motive := fun v => (Int.ofNat Nat.zero).le v)
        (((congrArg (fun z => f z b) hm).trans (congrArg (f (Int.ofNat m)) hn)).trans (onNat m n)).symm
        (Int.natCast_nonneg (g m n))

private theorem proveAdd (a b : Int) (ha : (Int.ofNat Nat.zero).le a) (hb : (Int.ofNat Nat.zero).le b) :
    (Int.ofNat Nat.zero).le (a.add b) := ofNaturalArguments Int.add Nat.add (fun _ _ => Omega.rfl) a b ha hb
private theorem proveMul (a b : Int) (ha : (Int.ofNat Nat.zero).le a) (hb : (Int.ofNat Nat.zero).le b) :
    (Int.ofNat Nat.zero).le (a.mul b) := ofNaturalArguments Int.mul Nat.mul (fun _ _ => Omega.rfl) a b ha hb
private theorem proveDiv (a b : Int) (ha : (Int.ofNat Nat.zero).le a) (hb : (Int.ofNat Nat.zero).le b) :
    (Int.ofNat Nat.zero).le (a.ediv b) := ofNaturalArguments Int.ediv Nat.div (fun m n => (Int.natCast_ediv m n).symm) a b ha hb

private theorem proveMod (a b : Int) (ha : (Int.ofNat Nat.zero).le a) : (Int.ofNat Nat.zero).le (a.emod b) :=
  (Int.eq_ofNat_of_zero_le ha).elim fun m hm =>
    Eq.subst (motive := fun z => (Int.ofNat Nat.zero).le (z.emod b)) hm.symm
      (Int.casesOn (motive := fun b => (Int.ofNat Nat.zero).le ((Int.ofNat m).emod b)) b
        (fun n => Int.natCast_nonneg (Nat.mod m n))
        (fun n => Int.natCast_nonneg (Nat.mod m n.succ)))

end Omega.Int.Nonneg
port_proof Int.Nonneg.add using Omega.Int.Nonneg.proveAdd
port_proof Int.Nonneg.mul using Omega.Int.Nonneg.proveMul
port_proof Int.Nonneg.div using Omega.Int.Nonneg.proveDiv
port_proof Int.Nonneg.mod using Omega.Int.Nonneg.proveMod
port_proof Int.Nonneg.natCast using Omega.Int.natCast_nonneg
namespace Omega.Int.Nonneg

private theorem proveNum (a : Int) (h : Eq (num_cert a) Bool.true) : (Int.ofNat Nat.zero).le a :=
  @of_decide_eq_true _ (Int.decLe (Int.ofNat Nat.zero) a) h


private theorem provePow (a : Int) (k : Nat) (ha : (Int.ofNat Nat.zero).le a) :
    (Int.ofNat Nat.zero).le (Int.pow a k) :=
  (Int.eq_ofNat_of_zero_le ha).elim fun n hn =>
    Eq.subst (motive := fun z => (Int.ofNat Nat.zero).le (Int.pow z k)) hn.symm
      (Int.natCast_nonneg (Nat.pow n k))

private theorem negLeZero (n : Nat) : ((Int.negSucc Nat.zero).mul (Int.ofNat n)).le (Int.ofNat Nat.zero) :=
  Int.le.intro n ((congrArg (fun z => Int.add z (Int.ofNat n))
    (congrArg Int.negOfNat (Nat.one_mul n))).trans (Int.add_left_neg (Int.ofNat n)))

private theorem proveToPoly (a : Int) (ha : (Int.ofNat Nat.zero).le a) :
    ((Int.negSucc Nat.zero).mul a).le (Int.ofNat Nat.zero) :=
  (Int.eq_ofNat_of_zero_le ha).elim fun n hn =>
    Eq.subst (motive := fun z => ((Int.negSucc Nat.zero).mul z).le (Int.ofNat Nat.zero)) hn.symm (negLeZero n)

end Omega.Int.Nonneg
port_proof Int.Nonneg.num using Omega.Int.Nonneg.proveNum
port_proof Int.Nonneg.pow using Omega.Int.Nonneg.provePow
port_proof Int.Nonneg.toPoly using Omega.Int.Nonneg.proveToPoly

port_proof Nat.ToInt.toNat_nonneg using Omega.Int.Nonneg.negLeZero

namespace Omega.Nat.ToInt

private theorem of_not_le._proof_1_1 {a b : Nat} (hn : Not ((Int.ofNat a).le (Int.ofNat b)))
    (hr : Not (((Int.ofNat b).add (Int.ofNat Nat.zero.succ)).le (Int.ofNat a))) : False :=
  hr (Int.ofNat_le.mpr (Nat.lt_of_not_ge (fun h => hn (Int.ofNat_le.mpr h))))

end Omega.Nat.ToInt

namespace Omega.Int.Nonneg

private theorem toPoly._proof_1_1 (e : Int) (h : (Int.ofNat Nat.zero).le e)
    (hn : Not (((Int.negSucc Nat.zero).mul e).le (Int.ofNat Nat.zero))) : False :=
  hn (proveToPoly e h)

end Omega.Int.Nonneg

/- Nat.ToInt.eq_eq requires equality between the propositions on Nat and Int.
NaturalCastComparison.eqIff identifies it with Int.ofNat.injEq.
Nat.ToInt.lt_eq requires equality between successor-indexed natural comparison
and nonnegativity of the integer difference. Nat.ToInt.le_eq also requires the
zero lower bound. The exact two conditions are proved in
NaturalCastComparison.ltIff and NaturalCastComparison.leIff.

The private Nat.ToInt.eq_eq._simp_1_1 and Nat.ToInt.lt_eq._simp_1_1 require the
reverse equalities on casts. Nat.ToInt.le_eq._simp_1_1 and
Nat.ToInt.sub_congr._simp_1_1 require the reverse non-strict comparison.
Nat.ToInt.of_dvd._simp_1_1 identifies the integer and natural divisibility
propositions as types. The public transport proof constructs the integer divisor
witness directly. These five private proposition equalities remain open. -/

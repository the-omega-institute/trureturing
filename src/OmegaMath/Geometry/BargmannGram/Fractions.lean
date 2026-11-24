module
prelude
public import OmegaMath.Geometry.BargmannGram.Coordinates

/-!
Omega original.

Common-denominator operations used for Gram and Hecke identities.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

theorem nat_mul_ne_zero {a b : Nat} (ha : Not (Eq a Nat.zero))
    (hb : Not (Eq b Nat.zero)) : Not (Eq (a.mul b) Nat.zero) :=
  fun h => (Nat.mul_eq_zero.mp h).elim ha hb

theorem value_const (a : Int) (n : Nat) (hn : Not (Eq n Nat.zero)) :
    IntRatio.Equivalent (IntRatio.ofInt a) (IntRatio.value (a.mul (Int.ofNat n)) n) :=
  let one := Nat.zero.succ
  have scale := (IntRatio.value_scale_of_ne_zero a one n hn).symm
  Eq.subst (fun d => IntRatio.Equivalent (IntRatio.ofInt a)
    (IntRatio.value (a.mul (Int.ofNat n)) d)) (Nat.one_mul n) scale

theorem value_neg (a : Int) (d : Nat) :
    Eq (IntRatio.value a d).neg (IntRatio.value a.neg d) :=
  Nat.rec (motive := fun d => Eq (IntRatio.value a d).neg (IntRatio.value a.neg d))
    Eq.refl (fun _ _ => Eq.refl) d

theorem value_sub_same (a b : Int) (d : Nat) :
    IntRatio.Equivalent ((IntRatio.value a d).sub (IntRatio.value b d))
      (IntRatio.value (a.sub b) d) :=
  Eq.subst (fun y => IntRatio.Equivalent ((IntRatio.value a d).add y)
    (IntRatio.value (a.sub b) d)) (value_neg b d).symm (IntRatio.value_add_same a b.neg d)

theorem value_mul_int (k a : Int) (d : Nat) :
    Eq ((IntRatio.ofInt k).mul (IntRatio.value a d)) (IntRatio.value (k.mul a) d) :=
  (IntRatio.value_mul k a Nat.zero.succ d).trans
    (congrArg (IntRatio.value (k.mul a)) (Nat.one_mul d))

theorem zero_le_value (a : Int) (d : Nat) (hd : Not (Eq d Nat.zero))
    (ha : Int.NonNeg a) : IntRatio.Le (IntRatio.ofInt Int.zero) (IntRatio.value a d) :=
  (Nat.rec (motive := fun d => Not (Eq d Nat.zero) →
    IntRatio.Le (IntRatio.ofInt Int.zero) (IntRatio.value a d))
    (fun h => False.elim (h Eq.refl))
    (fun k _ _ =>
      Eq.subst Int.NonNeg
        ((Int.sub_eq_add_neg (a := a.mul Int.one)
          (b := Int.zero.mul (Int.ofNat k.succ))).trans
          (Eq.map₂ Int.add (Int.mul_one a)
            (congrArg Int.neg (Int.zero_mul (Int.ofNat k.succ)))) |>.trans (Int.add_zero a)).symm ha)
    d) hd

end Omega.Geometry.BargmannGram

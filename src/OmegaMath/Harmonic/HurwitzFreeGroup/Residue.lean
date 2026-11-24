/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Matrix.Mat2.Hurwitz

/-!
Omega original.

Reduction of integer arithmetic to the five Hurwitz residues.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.Residue

def neg : Residue → Residue := Residue.rec .zero .four .three .two .one

private theorem next_prev (a : Residue) : Eq a.prev.next a :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

private theorem prev_next (a : Residue) : Eq a.next.prev a :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

private theorem neg_next (a : Residue) : Eq a.next.neg a.neg.prev :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

private theorem neg_neg (a : Residue) : Eq a.neg.neg a :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

private theorem add_next (a b : Residue) : Eq (a.add b.next) (a.add b).next :=
  Residue.rec (motive := fun b => Eq (a.add b.next) (a.add b).next)
    Eq.refl Eq.refl Eq.refl Eq.refl
    (Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a) b

private theorem add_prev (a b : Residue) : Eq (a.add b.prev) (a.add b).prev :=
  (prev_next (a.add b.prev)).symm.trans
    (congrArg prev ((add_next a b.prev).symm.trans (congrArg a.add (next_prev b))))

private theorem mul_next (a b : Residue) : Eq (a.mul b.next) ((a.mul b).add a) :=
  Residue.rec (motive := fun b => Eq (a.mul b.next) ((a.mul b).add a))
    Eq.refl Eq.refl Eq.refl Eq.refl
    (Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a) b

private theorem mul_neg (a b : Residue) : Eq (a.mul b.neg) (a.mul b).neg :=
  let check := fun (a b : Residue) => Eq (a.mul b.neg) (a.mul b).neg
  (Residue.rec (motive := fun a => ∀ b, check a b)
    (Residue.rec (motive := check .zero) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Residue.rec (motive := check .one) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Residue.rec (motive := check .two) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Residue.rec (motive := check .three) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
    (Residue.rec (motive := check .four) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl) a) b

private theorem ofInt_add_one (a : Int) : Eq (ofInt (a.add Int.one)) (ofInt a).next :=
  Int.rec (motive := fun a => Eq (ofInt (a.add Int.one)) (ofInt a).next)
    (fun _ => Eq.refl)
    (fun n => Nat.rec (motive := fun n =>
      Eq (ofInt ((Int.negSucc n).add Int.one)) (ofInt (Int.negSucc n)).next)
      Eq.refl (fun k _ => (next_prev (ofInt (Int.negSucc k))).symm) n) a

private theorem ofInt_add_neg_one (a : Int) : Eq (ofInt (a.add Int.one.neg)) (ofInt a).prev :=
  have cancel : Eq ((a.add Int.one.neg).add Int.one) a :=
    (Int.add_assoc a Int.one.neg Int.one).trans (Int.add_zero a)
  (prev_next (ofInt (a.add Int.one.neg))).symm.trans
    (congrArg prev ((ofInt_add_one (a.add Int.one.neg)).symm.trans (congrArg ofInt cancel)))

/-- Integer addition descends to the existing operations on residues. -/
theorem ofInt_add (a b : Int) : Eq (ofInt (a.add b)) ((ofInt a).add (ofInt b)) :=
  let P := fun b : Int => Eq (ofInt (a.add b)) ((ofInt a).add (ofInt b))
  Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n))
      (congrArg ofInt (Int.add_zero a))
      (fun k ih =>
        (congrArg ofInt (Int.add_assoc a (Int.ofNat k) Int.one).symm).trans
          ((ofInt_add_one _).trans
            ((congrArg next ih).trans (add_next (ofInt a) (ofInt (Int.ofNat k))).symm))) n)
    (fun n => Nat.rec (motive := fun n => P (Int.negSucc n))
      ((ofInt_add_neg_one a).trans (add_prev (ofInt a) .zero).symm)
      (fun k ih =>
        (congrArg ofInt (Int.add_assoc a (Int.negSucc k) Int.one.neg).symm).trans
          ((ofInt_add_neg_one _).trans
            ((congrArg prev ih).trans (add_prev (ofInt a) (ofInt (Int.negSucc k))).symm))) n) b

private theorem ofInt_negOfNat_succ (n : Nat) :
    Eq (ofInt (Int.negOfNat n.succ)) (ofInt (Int.negOfNat n)).prev :=
  Nat.rec Eq.refl (fun _ _ => Eq.refl) n

private theorem ofInt_negOfNat (n : Nat) :
    Eq (ofInt (Int.negOfNat n)) (ofInt (Int.ofNat n)).neg :=
  Nat.rec (motive := fun n => Eq (ofInt (Int.negOfNat n)) (ofInt (Int.ofNat n)).neg)
    Eq.refl
    (fun k ih => (ofInt_negOfNat_succ k).trans
      ((congrArg prev ih).trans (neg_next (ofInt (Int.ofNat k))).symm)) n

theorem ofInt_neg (a : Int) : Eq (ofInt a.neg) (ofInt a).neg :=
  Int.rec (motive := fun a => Eq (ofInt a.neg) (ofInt a).neg)
    ofInt_negOfNat
    (fun k => (neg_neg (ofInt (Int.ofNat k.succ))).symm.trans
      (congrArg neg (ofInt_negOfNat k.succ)).symm) a

private theorem ofInt_mul_ofNat (a : Int) (n : Nat) :
    Eq (ofInt (a.mul (Int.ofNat n))) ((ofInt a).mul (ofInt (Int.ofNat n))) :=
  Nat.rec (motive := fun n => Eq (ofInt (a.mul (Int.ofNat n)))
      ((ofInt a).mul (ofInt (Int.ofNat n))))
    (congrArg ofInt (Int.mul_zero a))
    (fun k ih =>
      (congrArg ofInt (Int.mul_add a (Int.ofNat k) Int.one)).trans
        ((ofInt_add _ _).trans
          ((Eq.map₂ add ih (congrArg ofInt (Int.mul_one a))).trans
            (mul_next (ofInt a) (ofInt (Int.ofNat k))).symm))) n

theorem ofInt_mul (a b : Int) : Eq (ofInt (a.mul b)) ((ofInt a).mul (ofInt b)) :=
  Int.rec (motive := fun b => Eq (ofInt (a.mul b)) ((ofInt a).mul (ofInt b)))
    (ofInt_mul_ofNat a)
    (fun k =>
      let b := Int.ofNat k.succ
      (congrArg ofInt (Int.mul_neg a b)).trans
        ((ofInt_neg _).trans
          ((congrArg neg (ofInt_mul_ofNat a k.succ)).trans
            ((mul_neg (ofInt a) (ofInt b)).symm.trans
              (congrArg (ofInt a).mul (ofInt_neg b).symm))))) b

private def lift (r : Residue) : Int := Int.ofNat r.toNat

private theorem ofInt_lift (r : Residue) : Eq (ofInt (lift r)) r :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl r

private theorem lift_add (a b : Residue) : Eq (ofInt ((lift a).add (lift b))) (a.add b) :=
  (ofInt_add _ _).trans (Eq.map₂ add (ofInt_lift a) (ofInt_lift b))

private theorem lift_mul (a b : Residue) : Eq (ofInt ((lift a).mul (lift b))) (a.mul b) :=
  (ofInt_mul _ _).trans (Eq.map₂ mul (ofInt_lift a) (ofInt_lift b))

theorem zero_add (a : Residue) : Eq ((.zero : Residue).add a) a :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

theorem mul_one (a : Residue) : Eq (a.mul .one) a := zero_add a

theorem one_mul (a : Residue) : Eq ((.one : Residue).mul a) a :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

theorem zero_mul (a : Residue) : Eq ((.zero : Residue).mul a) .zero :=
  Residue.rec Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl a

theorem mul_comm (a b : Residue) : Eq (a.mul b) (b.mul a) :=
  (lift_mul a b).symm.trans
    ((congrArg ofInt (Int.mul_comm (lift a) (lift b))).trans (lift_mul b a))

theorem mul_assoc (a b c : Residue) : Eq ((a.mul b).mul c) (a.mul (b.mul c)) :=
  let x := lift a
  let y := lift b
  let z := lift c
  have left : Eq (ofInt ((x.mul y).mul z)) ((a.mul b).mul c) :=
    (ofInt_mul _ _).trans (Eq.map₂ mul (lift_mul a b) (ofInt_lift c))
  have right : Eq (ofInt (x.mul (y.mul z))) (a.mul (b.mul c)) :=
    (ofInt_mul _ _).trans (Eq.map₂ mul (ofInt_lift a) (lift_mul b c))
  left.symm.trans ((congrArg ofInt (Int.mul_assoc x y z)).trans right)

theorem mul_add (a b c : Residue) : Eq (a.mul (b.add c)) ((a.mul b).add (a.mul c)) :=
  let x := lift a
  let y := lift b
  let z := lift c
  have left : Eq (ofInt (x.mul (y.add z))) (a.mul (b.add c)) :=
    (ofInt_mul _ _).trans (Eq.map₂ mul (ofInt_lift a) (lift_add b c))
  have right : Eq (ofInt ((x.mul y).add (x.mul z))) ((a.mul b).add (a.mul c)) :=
    (ofInt_add _ _).trans (Eq.map₂ add (lift_mul a b) (lift_mul a c))
  left.symm.trans ((congrArg ofInt (Int.mul_add x y z)).trans right)

theorem add_mul (a b c : Residue) : Eq ((a.add b).mul c) ((a.mul c).add (b.mul c)) :=
  (mul_comm (a.add b) c).trans
    ((mul_add c a b).trans (Eq.map₂ add (mul_comm c a) (mul_comm c b)))

theorem zero_of_isZero {a : Residue} (h : Eq a.isZero .true) : Eq a .zero :=
  Eq.subst (Bool.rec (motive := fun _ => Prop) True (Eq a .zero)) h
    (Residue.rec Eq.refl True.intro True.intro True.intro True.intro a)

theorem false_ne_true : Not (Eq Bool.false Bool.true) :=
  fun h => Eq.subst (Bool.rec (motive := fun _ => Prop) True False) h True.intro

private def inverse : Residue → Residue := Residue.rec .zero .one .three .two .four

private theorem inverse_mul {a : Residue} (h : Not (Eq a .zero)) : Eq (a.inverse.mul a) .one :=
  (Residue.rec (motive := fun a => Not (Eq a .zero) → Eq (a.inverse.mul a) .one)
    (fun h => False.elim (h Eq.refl)) (fun _ => Eq.refl) (fun _ => Eq.refl)
    (fun _ => Eq.refl) (fun _ => Eq.refl) a) h

theorem mul_ne_zero {a b : Residue} (ha : Not (Eq a .zero)) (hb : Not (Eq b .zero)) :
    Not (Eq (a.mul b) .zero) :=
  fun h => hb ((one_mul b).symm.trans
    ((congrArg (fun x : Residue => x.mul b) (inverse_mul ha).symm).trans
      ((mul_assoc a.inverse a b).trans (congrArg a.inverse.mul h))))

end Omega.Hurwitz.Residue

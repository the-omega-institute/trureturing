/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Ternion.Heap.Fidelity

/-!
Omega original.

Signed rational unit quaternions, their stereographic lift, and their two fidelities.
The denominator is represented by its natural predecessor. Equivalent representatives
give the same signed quaternion, so the two antipodes remain distinct.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A data certificate for equality of natural squared norms in the strict prelude. -/
inductive Pythagorean (n : Nat) : Nat → Type where
  | same : Pythagorean n n

structure PythSpinor where
  num : Quaternion
  radiusPred : Nat
  pythagorean : Pythagorean num.normSq (radiusPred.succ.mul radiusPred.succ)

namespace PythSpinor

open Quaternion Polynomial

def radius (p : PythSpinor) : Nat := p.radiusPred.succ

theorem radius_positive (p : PythSpinor) : Int.zero.lt (Int.ofNat p.radius) :=
  Nat.rec (motive := fun n => Int.zero.lt (Int.ofNat n.succ))
    True.intro (fun _ _ => True.intro) p.radiusPred

theorem normSq_eq (p : PythSpinor) : Eq p.num.normSq (p.radius.mul p.radius) :=
  Pythagorean.rec (motive := fun n _ => Eq p.num.normSq n) Eq.refl p.pythagorean

def ofNumerator (q : Quaternion) (r : Nat) (h : Eq q.normSq (r.succ.mul r.succ)) : PythSpinor :=
  ⟨q, r, Eq.rec (motive := fun n _ => Pythagorean q.normSq n) Pythagorean.same h⟩

def one : PythSpinor := ofNumerator Quaternion.one Nat.zero Eq.refl

def antipode : PythSpinor := ofNumerator (scalar Int.one.neg) Nat.zero Eq.refl

def conj (p : PythSpinor) : PythSpinor :=
  ofNumerator p.num.conj p.radiusPred ((normSq_conj p.num).trans p.normSq_eq)

def mul (p q : PythSpinor) : PythSpinor :=
  let r := p.radius
  let s := q.radius
  have combine : Eq ((r.mul r).mul (s.mul s)) ((r.mul s).mul (r.mul s)) :=
    (Nat.mul_assoc r r (s.mul s)).trans
      ((congrArg r.mul (((Nat.mul_assoc r s s).symm.trans
        (congrArg (fun n : Nat => n.mul s) (Nat.mul_comm r s))).trans
        (Nat.mul_assoc s r s))).trans (Nat.mul_assoc r s (r.mul s)).symm)
  ofNumerator (p.num.mul q.num) (IntRatio.mulDenPred p.radiusPred q.radiusPred)
    ((normSq_mul p.num q.num).trans ((Eq.map₂ Nat.mul p.normSq_eq q.normSq_eq).trans combine))

def triad (p q r : PythSpinor) : PythSpinor := (p.mul q.conj).mul r

/-- The usual signed equality on homogeneous coordinates with positive denominator. -/
def Equivalent (p q : PythSpinor) : Prop :=
  Eq (scale (Int.ofNat q.radius) p.num) (scale (Int.ofNat p.radius) q.num)

private theorem radius_ne_zero (p : PythSpinor) : Not (Eq p.radius Nat.zero) :=
  Nat.succ_ne_zero p.radiusPred

theorem nonzero (p : PythSpinor) : p.num.Nonzero :=
  nonzero_of_normSq_ne_zero (fun h =>
    Ternion.nat_mul_ne_zero (radius_ne_zero p) (radius_ne_zero p) (p.normSq_eq.symm.trans h))

theorem cayley_lift_identity (a s : Int) :
    Eq ((Int.square ((Int.square a).sub s)).add ((Int.two.mul Int.two).mul ((Int.square a).mul s)))
      (Int.square ((Int.square a).add s)) :=
  let A := Expr.var Nat.zero
  let S := Expr.var Nat.zero.succ
  let two := Expr.one.double
  (((A.sq.sub S).sq).add ((two.mul two).mul (A.sq.mul S))).sound
    ((A.sq.add S).sq) (.cons a (.cons s .nil)) Eq.refl

/-- The three squared imaginary coordinates factor through the sum of three squares. -/
private theorem scaled_imaginary_norm (a b c d : Int) :
    Eq ((Int.square ((Int.two.mul a).mul b)).add
      ((Int.square ((Int.two.mul a).mul c)).add (Int.square ((Int.two.mul a).mul d))))
      ((Int.two.mul Int.two).mul ((Int.square a).mul
        ((Int.square b).add ((Int.square c).add (Int.square d))))) :=
  let start := Nat.zero
  let A := Expr.var start
  let B := Expr.var start.succ
  let C := Expr.var start.succ.succ
  let D := Expr.var start.succ.succ.succ
  let two := Expr.one.double
  let square := fun t => ((two.mul A).mul t).sq
  ((square B).add ((square C).add (square D))).sound
    ((two.mul two).mul (A.sq.mul (B.sq.add (C.sq.add D.sq))))
      (.cons a (.cons b (.cons c (.cons d .nil)))) Eq.refl

def liftRadius (a b c d : Int) : Nat :=
  let sq := fun (t : Int) => t.natAbs.mul t.natAbs
  (sq a).add ((sq b).add ((sq c).add (sq d)))

def liftNum (a b c d : Int) : Quaternion :=
  let s := (Int.square b).add ((Int.square c).add (Int.square d))
  let k := Int.two.mul a
  ⟨(Int.square a).sub s, k.mul b, k.mul c, k.mul d⟩

theorem lift_normSq (a b c d : Int) :
    Eq (liftNum a b c d).normSq ((liftRadius a b c d).mul (liftRadius a b c d)) :=
  let p := liftNum a b c d
  let s := (Int.square b).add ((Int.square c).add (Int.square d))
  have r : Eq (Int.ofNat (liftRadius a b c d)) ((Int.square a).add s) :=
    Eq.map₂ Int.add Int.natAbs_mul_self
      (Eq.map₂ Int.add Int.natAbs_mul_self (Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self))
  Int.ofNat_inj.mp (p.normSq_cast.trans
    ((Int.add_assoc (Int.square p.w) (Int.square p.x)
      ((Int.square p.y).add (Int.square p.z))).trans
        ((congrArg (Int.square p.w).add (scaled_imaginary_norm a b c d)).trans
          ((cayley_lift_identity a s).trans (congrArg Int.square r.symm)))))

theorem lift_radius_ne_zero (a b c d : Int) (h : (Quaternion.mk a b c d).Nonzero) :
    Not (Eq (liftRadius a b c d) Nat.zero) :=
  fun e => normSq_ne_zero h ((Nat.add_assoc (a.natAbs.mul a.natAbs) (b.natAbs.mul b.natAbs)
    ((c.natAbs.mul c.natAbs).add (d.natAbs.mul d.natAbs))).trans e)

def ofRadius (p : Quaternion) (r : Nat) (h : Not (Eq r Nat.zero))
    (e : Eq p.normSq (r.mul r)) : PythSpinor :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → Eq p.normSq (n.mul n) → PythSpinor)
    (fun h _ => False.elim (h Eq.refl)) (fun n _ _ h => ofNumerator p n h) r) h e

/-- Homogeneous Cayley lift. Its only excluded input is the zero quadruple. -/
def Phi (a b c d : Int) (h : (Quaternion.mk a b c d).Nonzero) : PythSpinor :=
  ofRadius (liftNum a b c d) (liftRadius a b c d)
    (lift_radius_ne_zero a b c d h) (lift_normSq a b c d)

theorem phi_coordinates (a b c d : Int) (h : (Quaternion.mk a b c d).Nonzero) :
    And (Eq (Phi a b c d h).num (liftNum a b c d))
      (Eq (Phi a b c d h).radius (liftRadius a b c d)) :=
  let p := liftNum a b c d
  let r := liftRadius a b c d
  (Nat.rec (motive := fun n => ∀ (h : Not (Eq n Nat.zero)) (e : Eq p.normSq (n.mul n)),
    And (Eq (ofRadius p n h e).num p) (Eq (ofRadius p n h e).radius n))
    (fun h _ => False.elim (h Eq.refl)) (fun _ _ _ _ => And.intro Eq.refl Eq.refl) r)
    (lift_radius_ne_zero a b c d h) (lift_normSq a b c d)

/-- Signed affine fidelity, equal to one at a spinor and zero at its antipode. -/
def kappa_spin (p q : PythSpinor) : IntRatio :=
  let r := p.radius.mul q.radius
  IntRatio.value ((Int.ofNat r).add (p.num.dot q.num)) (r.mul Nat.zero.succ.succ)

def kappa_proj (p q : PythSpinor) : IntRatio := Ternion.kappa p.num q.num

private theorem affine_difference (r d : Int) :
    Eq ((Int.two.mul (r.add d)).add (r.mul Int.two).neg) (d.mul Int.two) :=
  let R := Expr.var Nat.zero
  let D := Expr.var Nat.zero.succ
  let T := Expr.one.double
  ((T.mul (R.add D)).sub (R.mul T)).sound (D.mul T) (.cons r (.cons d .nil)) Eq.refl

theorem spin_affine (p q : PythSpinor) :
    IntRatio.Equivalent
      (((IntRatio.ofInt Int.two).mul (kappa_spin p q)).sub (IntRatio.ofInt Int.one))
      (IntRatio.value (p.num.dot q.num) (p.radius.mul q.radius)) :=
  let r := p.radius.mul q.radius
  let d := p.num.dot q.num
  let two := Nat.zero.succ.succ
  let n := r.mul two
  let x := Int.two.mul ((Int.ofNat r).add d)
  have hr := Ternion.nat_mul_ne_zero (radius_ne_zero p) (radius_ne_zero q)
  have hn := Ternion.nat_mul_ne_zero hr (Nat.succ_ne_zero Nat.zero.succ)
  have twice : Eq ((IntRatio.ofInt Int.two).mul (kappa_spin p q)) (IntRatio.value x n) :=
    (IntRatio.value_mul Int.two ((Int.ofNat r).add d) Nat.zero.succ n).trans
      (congrArg (IntRatio.value x) (Nat.one_mul n))
  have compare := IntRatio.add_congr
    (Eq.subst (fun f => IntRatio.Equivalent f (IntRatio.value x n)) twice.symm
      (IntRatio.equivalent_refl (IntRatio.value x n)))
    (IntRatio.value_neg_self n hn).symm
  compare.trans ((IntRatio.value_add_same x (Int.ofNat n).neg n).trans
    (Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t n) (IntRatio.value d r))
      (affine_difference (Int.ofNat r) d).symm (IntRatio.value_scale d r Nat.zero.succ)))

theorem quadratic_kernel (p q : PythSpinor) :
    IntRatio.Equivalent (kappa_proj p q)
      (let d := ((IntRatio.ofInt Int.two).mul (kappa_spin p q)).sub (IntRatio.ofInt Int.one)
       d.mul d) :=
  let r := p.radius
  let s := q.radius
  let d := p.num.dot q.num
  let f := IntRatio.value d (r.mul s)
  have e : Eq (p.num.normSq.mul q.num.normSq) ((r.mul s).mul (r.mul s)) :=
    (Eq.map₂ Nat.mul p.normSq_eq q.normSq_eq).trans
      ((Nat.mul_assoc r r (s.mul s)).trans
        ((congrArg r.mul (((Nat.mul_assoc r s s).symm.trans
          (congrArg (fun n : Nat => n.mul s) (Nat.mul_comm r s))).trans
          (Nat.mul_assoc s r s))).trans (Nat.mul_assoc r s (r.mul s)).symm))
  have id : Eq (kappa_proj p q) (f.mul f) :=
    (congrArg (IntRatio.value (Int.square d)) e).trans
      (IntRatio.value_mul d d (r.mul s) (r.mul s)).symm
  Eq.subst (fun x => IntRatio.Equivalent x _) id.symm
    (IntRatio.mul_congr (spin_affine p q).symm (spin_affine p q).symm)

def g120_spin : PythSpinor :=
  ofNumerator ⟨Int.one, Int.one, Int.one, Int.one⟩ Nat.zero.succ Eq.refl

def pow (p : PythSpinor) (n : Nat) : PythSpinor :=
  Nat.rec one (fun _ t => t.mul p) n

theorem g120_third_beat :
    let beat := g120_spin.pow Nat.zero.succ.succ.succ
    And (Equivalent beat antipode)
      (IntRatio.Equivalent (kappa_spin one beat) (IntRatio.ofInt Int.zero)) :=
  And.intro Eq.refl (IntRatio.value_zero _ (Nat.succ_ne_zero _))

theorem g120_sixth_beat :
    let beat := g120_spin.pow Nat.zero.succ.succ.succ.succ.succ.succ
    And (Equivalent beat one)
      (IntRatio.Equivalent (kappa_spin one beat) (IntRatio.ofInt Int.one)) :=
  And.intro Eq.refl (IntRatio.value_self _ (Nat.succ_ne_zero _))

end PythSpinor
end Omega

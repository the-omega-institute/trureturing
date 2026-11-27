module
prelude
import all OmegaInit.Prelude
public import OmegaMath.Harmonic.AllDegreeHaar.Characters
import OmegaMath.Calculus.Jet2.Scalar

/-!
Omega original.

Linearity of the factorial moment functional on integer coefficient lists,
including invariance under padding with zero coefficients.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.AllDegreeHaar

open PiFreeHaar
open IntRatio (Equivalent)

namespace Integration

private def zero : IntRatio := IntRatio.ofInt Int.zero

private theorem finite_equiv {x y : IntRatio} (h : Equivalent x y) (hy : IntRatio.Finite y) : IntRatio.Finite x :=
  (IntRatio.rec (motive := fun x => Equivalent x y → IntRatio.Finite x)
    ((IntRatio.rec (motive := fun y => IntRatio.Finite y → Equivalent .undefined y → IntRatio.Finite .undefined)
      (fun h _ => h) (fun _ _ _ h => h) y) hy)
    (fun _ _ _ => True.intro) x) h

private theorem moment_finite (k : Nat) : IntRatio.Finite (haarKappaMoment k) :=
  Nat.rec (motive := fun k => IntRatio.Finite (haarKappaMoment k))
    (finite_equiv haarKappaMoment_0 True.intro)
    (fun k ih =>
      let two := PiFreeHaar.Numerals.two
      have hd := (Nat.mul_succ two k.succ).trans (Nat.add_succ _ Nat.one)
      have finite := Eq.subst (motive := fun n =>
        IntRatio.Finite (IntRatio.value (Int.ofNat (two.mul k).succ) n)) hd.symm True.intro
      finite_equiv (haarKappaMoment_succ k) (IntRatio.finite_mul ih finite)) k

private theorem ofInt_add (a b : Int) :
    Equivalent (IntRatio.ofInt (a.add b)) ((IntRatio.ofInt a).add (IntRatio.ofInt b)) :=
  (IntRatio.value_add_same a b Nat.one).symm

private theorem ofInt_mul (a b : Int) :
    Equivalent (IntRatio.ofInt (a.mul b)) ((IntRatio.ofInt a).mul (IntRatio.ofInt b)) :=
  Eq.subst (motive := fun n => Equivalent (IntRatio.ofInt (a.mul b)) (IntRatio.fraction (a.mul b) n))
    ((Nat.add_zero _).trans (Nat.mul_zero Nat.one)).symm (IntRatio.equivalent_refl _)

private theorem neg_one_mul (x : IntRatio) :
    Equivalent ((IntRatio.ofInt Int.one.neg).mul x) x.neg :=
  (IntRatio.neg_mul IntRatio.one x).trans (IntRatio.neg_congr (IntRatio.one_mul x))

def integral (k : Nat) (p : Poly) : IntRatio := haarKappaPolyFrom k p.ratios

private theorem integral_zero (p : Poly) (h : p.Same .nil) (k : Nat) :
    Equivalent (integral k p) zero :=
  (Poly.rec (motive := fun p => p.Same .nil → ∀ k, Equivalent (integral k p) zero)
    (fun _ _ => IntRatio.equivalent_refl zero)
    (fun _ _ ih h k => (IntRatio.add_congr
      ((IntRatio.mul_congr_left (IntRatio.ofInt_congr (h Nat.zero)) (haarKappaMoment k)).trans
        (IntRatio.zero_mul (moment_finite k)))
      (ih (fun j => h j.succ) k.succ)).trans (IntRatio.add_zero zero)) p) h k

theorem integral_congr {p q : Poly} (h : p.Same q) (k : Nat) :
    Equivalent (integral k p) (integral k q) :=
  (Poly.rec (motive := fun p => ∀ q, p.Same q → ∀ k, Equivalent (integral k p) (integral k q))
    (fun q h k => (integral_zero q h.symm k).symm)
    (fun a p ih q => Poly.rec
      (motive := fun q => (Poly.cons a p).Same q → ∀ k,
        Equivalent (integral k (.cons a p)) (integral k q))
      (fun h k => integral_zero (.cons a p) h k)
      (fun _ q _ h k => IntRatio.add_congr
        (IntRatio.mul_congr_left (IntRatio.ofInt_congr (h Nat.zero)) (haarKappaMoment k))
        (ih q (fun j => h j.succ) k.succ)) q) p) q h k

theorem integral_add (k : Nat) (p q : Poly) :
    Equivalent (integral k (p.add q)) ((integral k p).add (integral k q)) :=
  (Poly.rec (motive := fun p => ∀ q k,
    Equivalent (integral k (p.add q)) ((integral k p).add (integral k q)))
    (fun q k => (IntRatio.zero_add (integral k q)).symm)
    (fun a p ih q => Poly.rec (motive := fun q => ∀ k,
      Equivalent (integral k ((Poly.cons a p).add q))
        ((integral k (.cons a p)).add (integral k q)))
      (fun k => (IntRatio.add_zero (integral k (.cons a p))).symm)
      (fun b q _ k =>
        let t := haarKappaMoment k
        let x := IntRatio.ofInt a
        let y := IntRatio.ofInt b
        let head := (IntRatio.mul_congr_left (ofInt_add a b) t).trans
          ((IntRatio.mul_comm (x.add y) t).trans
            ((IntRatio.mul_add t x y).trans
              (IntRatio.add_congr (IntRatio.mul_comm t x) (IntRatio.mul_comm t y))))
        (IntRatio.add_congr head (ih q k.succ)).trans
          (IntRatio.add_add_add_comm (x.mul t) (y.mul t) (integral k.succ p) (integral k.succ q))) q) p) q k

theorem integral_scale (k : Nat) (a : Int) (p : Poly) :
    Equivalent (integral k (p.scale a)) ((IntRatio.ofInt a).mul (integral k p)) :=
  let x := IntRatio.ofInt a
  (Poly.rec (motive := fun p => ∀ k,
    Equivalent (integral k (p.scale a)) (x.mul (integral k p)))
    (fun _ => (IntRatio.mul_zero (x := x) True.intro).symm)
    (fun b p ih k =>
      let t := haarKappaMoment k
      let y := IntRatio.ofInt b
      let head := (IntRatio.mul_congr_left (ofInt_mul a b) t).trans (IntRatio.mul_assoc x y t)
      (IntRatio.add_congr head (ih k.succ)).trans
        (IntRatio.mul_add x (y.mul t) (integral k.succ p)).symm) p) k

theorem integral_sub (k : Nat) (p q : Poly) :
    Equivalent (integral k (p.sub q)) ((integral k p).sub (integral k q)) :=
  (integral_add k p q.neg).trans (IntRatio.add_congr (IntRatio.equivalent_refl _)
    ((integral_scale k Int.one.neg q).trans (neg_one_mul (integral k q))))

theorem integral_shift (k : Nat) (p : Poly) :
    Equivalent (integral k p.shift) (integral k.succ p) :=
  (IntRatio.add_congr (IntRatio.zero_mul (moment_finite k))
    (IntRatio.equivalent_refl (integral k.succ p))).trans (IntRatio.zero_add (integral k.succ p))

theorem integral_term (k : Nat) (a : Int) :
    Equivalent (integral k (.cons a .nil)) ((IntRatio.ofInt a).mul (haarKappaMoment k)) :=
  IntRatio.add_zero _

theorem integral_recurrence (k : Nat) (p : Poly) :
    Equivalent (integral k (Characters.recurrence p))
      (((IntRatio.ofInt Characters.four).mul (integral k.succ p)).sub
        ((IntRatio.ofInt Int.two).mul (integral k p))) :=
  let x := integral k p
  have negTwo : Equivalent ((IntRatio.ofInt Int.two.neg).mul x)
      ((IntRatio.ofInt Int.two).mul x).neg :=
    have coeff := (Int.neg_mul Int.one Int.two).trans (congrArg Int.neg (Int.one_mul Int.two))
    (IntRatio.mul_congr_left ((IntRatio.ofInt_congr coeff.symm).trans (ofInt_mul Int.one.neg Int.two)) x).trans
      ((IntRatio.mul_assoc (IntRatio.ofInt Int.one.neg) (IntRatio.ofInt Int.two) x).trans
        (neg_one_mul ((IntRatio.ofInt Int.two).mul x)))
  (integral_add k (Characters.shiftFour p) (p.scale Int.two.neg)).trans
    (IntRatio.add_congr ((integral_shift k (p.scale Characters.four)).trans
      (integral_scale k.succ Characters.four p)) ((integral_scale k Int.two.neg p).trans negTwo))

theorem integral_first (k : Nat) :
    Equivalent (integral k Characters.first)
      (((IntRatio.ofInt Characters.four).mul (haarKappaMoment k.succ)).sub (haarKappaMoment k)) :=
  let next := (IntRatio.ofInt Characters.four).mul (haarKappaMoment k.succ)
  let prev := (haarKappaMoment k).neg
  (IntRatio.add_congr (neg_one_mul (haarKappaMoment k)) (integral_term k.succ Characters.four)).trans
    (IntRatio.add_comm prev next)

theorem integral_one (k : Nat) : Equivalent (integral k Characters.one) (haarKappaMoment k) :=
  (integral_term k Int.one).trans
    ((IntRatio.mul_comm (IntRatio.ofInt Int.one) (haarKappaMoment k)).trans
      (IntRatio.mul_one (haarKappaMoment k)))

end Integration
end Omega.Harmonic.AllDegreeHaar

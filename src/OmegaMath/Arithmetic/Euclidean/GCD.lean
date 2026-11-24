module
prelude
public import OmegaMath.Arithmetic.Euclidean.Division
public import OmegaMath.Data.Int

/-! Omega original.

The Euclidean algorithm with signed Bézout coefficients.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

open Omega

structure ExtendedGcd where
  divisor : Nat
  leftCoeff : Int
  rightCoeff : Int

/-- Euclidean descent with at most `b` strict decreases from the initial divisor. -/
def extendedGcdAux (fuel a b : Nat) : ExtendedGcd :=
  Nat.rec (motive := fun _ => Nat → Nat → ExtendedGcd)
    (fun a _ => ⟨a, Int.one, Int.zero⟩)
    (fun _ ih a b =>
      Bool.rec (motive := fun _ => ExtendedGcd)
        (let qr := divMod a b
         let s := ih b qr.remainder
         ⟨s.divisor, s.rightCoeff, s.leftCoeff.sub ((Int.ofNat qr.quotient).mul s.rightCoeff)⟩)
        ⟨a, Int.one, Int.zero⟩ (natEq b Nat.zero)) fuel a b

def extendedGcd (a b : Nat) : ExtendedGcd := extendedGcdAux b a b

def gcd (a b : Nat) : Nat := (extendedGcd a b).divisor

private theorem dvd_mul_right {d a : Nat} (h : Dvd d a) (k : Nat) : Dvd d (a.mul k) :=
  dvd_trans h (Exists.intro k Eq.refl)

private theorem dvd_add {d a b : Nat} (ha : Dvd d a) (hb : Dvd d b) : Dvd d (a.add b) :=
  ha.elim (fun x hx => hb.elim (fun y hy =>
    Exists.intro (x.add y) ((Eq.map₂ Nat.add hx hy).trans (Nat.mul_add d x y).symm)))

private theorem dvd_remainder {d a b r : Nat} (ha : Dvd d a) (hb : Dvd d b)
    (he : Eq a (b.add r)) : Dvd d r :=
  ha.elim (fun x hx => hb.elim (fun y hy =>
    have sub : Eq (Int.ofNat r) (Int.subNatNat a b) :=
      (Int.subNatNat_add_left b r).symm.trans (congrArg (fun n => Int.subNatNat n b) he.symm)
    have factor : Eq (Int.ofNat r) ((Int.ofNat d).mul (Int.subNatNat x y)) :=
      sub.trans ((Eq.map₂ Int.subNatNat hx hy).trans (Int.ofNat_mul_subNatNat d x y).symm)
    Exists.intro ((Int.subNatNat x y).natAbs)
      ((congrArg Int.natAbs factor).trans (Int.natAbs_mul _ _))))

private theorem bezout_step (a b q r : Nat) (x y : Int)
    (h : Eq a ((b.mul q).add r)) :
    Eq (((Int.ofNat a).mul y).add
      ((Int.ofNat b).mul (x.sub ((Int.ofNat q).mul y))))
      (((Int.ofNat b).mul x).add ((Int.ofNat r).mul y)) :=
  let B := Int.ofNat b
  let Q := Int.ofNat q
  let R := Int.ofNat r
  let t := (B.mul Q).mul y
  let u := R.mul y
  let v := B.mul x
  have expandA : Eq ((Int.ofNat a).mul y) (t.add u) :=
    (congrArg (fun n => (Int.ofNat n).mul y) h).trans (Int.add_mul (B.mul Q) R y)
  have expandB : Eq (B.mul (x.sub (Q.mul y))) (v.add t.neg) :=
    (Int.mul_sub B x (Q.mul y)).trans (congrArg (fun z : Int => v.add z.neg) (Int.mul_assoc B Q y).symm)
  (Eq.map₂ Int.add expandA (expandB.trans (Int.add_comm v t.neg))).trans
    ((Int.add_add_add_comm t u t.neg v).trans
      ((congrArg (fun z : Int => z.add (u.add v)) (Int.add_right_neg t)).trans
        ((Int.zero_add (u.add v)).trans (Int.add_comm u v))))

private def GcdSpec (a b : Nat) (s : ExtendedGcd) : Prop :=
  And (Dvd s.divisor a) (And (Dvd s.divisor b)
    (And (∀ d, Dvd d a → Dvd d b → Dvd d s.divisor)
      (Eq (((Int.ofNat a).mul s.leftCoeff).add ((Int.ofNat b).mul s.rightCoeff))
        (Int.ofNat s.divisor))))

private theorem gcd_zero_spec (a b : Nat) (hb : Eq b Nat.zero) :
    GcdSpec a b ⟨a, Int.one, Int.zero⟩ :=
  And.intro (dvd_refl a)
    (And.intro (Eq.subst (Dvd a) hb.symm (dvd_zero a))
      (And.intro (fun _ ha _ => ha)
        ((Eq.map₂ Int.add (Int.mul_one (Int.ofNat a)) (Int.mul_zero (Int.ofNat b))).trans
          (Int.add_zero (Int.ofNat a)))))

private theorem extendedGcdAux_spec (fuel a b : Nat) (h : Nat.le b fuel) :
    GcdSpec a b (extendedGcdAux fuel a b) :=
  (Nat.rec (motive := fun fuel => ∀ a b, Nat.le b fuel → GcdSpec a b (extendedGcdAux fuel a b))
    (fun a b hb => gcd_zero_spec a b (Nat.le_antisymm hb (Nat.zero_le b)))
    (fun fuel ih a b hb =>
      let qr := divMod a b
      let s := extendedGcdAux fuel b qr.remainder
      natEq_cases b Nat.zero (fun test =>
        GcdSpec a b (Bool.rec (motive := fun _ => ExtendedGcd)
          ⟨s.divisor, s.rightCoeff, s.leftCoeff.sub ((Int.ofNat qr.quotient).mul s.rightCoeff)⟩
          ⟨a, Int.one, Int.zero⟩ test))
        (gcd_zero_spec a b)
        (fun nonzero =>
          let division := divMod_spec a b (pos_of_ne_zero nonzero)
          let prior := ih b qr.remainder (Nat.le_of_succ_le_succ (Nat.le_trans division.right hb))
          have da : Dvd s.divisor a := Eq.subst (Dvd s.divisor) division.left.symm
            (dvd_add (dvd_mul_right prior.left qr.quotient) prior.right.left)
          have greatest : ∀ d, Dvd d a → Dvd d b → Dvd d s.divisor := fun d ha hb =>
            prior.right.right.left d hb (dvd_remainder ha (dvd_mul_right hb qr.quotient) division.left)
          have linear := (bezout_step a b qr.quotient qr.remainder s.leftCoeff s.rightCoeff
            division.left).trans prior.right.right.right
          And.intro da (And.intro prior.left (And.intro greatest linear)))) fuel) a b h

private theorem extendedGcd_spec (a b : Nat) : GcdSpec a b (extendedGcd a b) :=
  extendedGcdAux_spec b a b (Nat.le.refl b)

theorem gcd_dvd_left (a b : Nat) : Dvd (gcd a b) a := (extendedGcd_spec a b).left

theorem gcd_dvd_right (a b : Nat) : Dvd (gcd a b) b := (extendedGcd_spec a b).right.left

theorem dvd_gcd {a b d : Nat} (ha : Dvd d a) (hb : Dvd d b) : Dvd d (gcd a b) :=
  (extendedGcd_spec a b).right.right.left d ha hb

/-- The computed coefficients solve Bézout's equation, including at `(0, 0)`. -/
theorem bezout_coefficients (a b : Nat) :
    Eq (((Int.ofNat a).mul (extendedGcd a b).leftCoeff).add
      ((Int.ofNat b).mul (extendedGcd a b).rightCoeff)) (Int.ofNat (gcd a b)) :=
  (extendedGcd_spec a b).right.right.right

theorem bezout_identity (a b : Nat) :
    Exists (fun x : Int => Exists (fun y : Int =>
      Eq (((Int.ofNat a).mul x).add ((Int.ofNat b).mul y)) (Int.ofNat (gcd a b)))) :=
  Exists.intro (extendedGcd a b).leftCoeff
    (Exists.intro (extendedGcd a b).rightCoeff (bezout_coefficients a b))

end Omega.Arithmetic

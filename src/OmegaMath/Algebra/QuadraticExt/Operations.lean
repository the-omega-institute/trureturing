module
prelude
public import OmegaMath.Algebra.QuadraticExt.Basic

/-!
Omega original.

The quadratic coefficient pair inherits commutative ring operations and powers.
-/

noncomputable section
@[expose] public section

namespace Omega.QuadPoly

variable {A : Type} {rel : A → A → Prop} {b c : A}

def ring (r : CommRingOps A rel) : CommRingOps (QuadPoly A b c) (Equivalent r) where
  constant := fun flag => ofScalar r (r.constant flag)
  add := add r
  mul := mul r
  neg := neg r

theorem ringLaws {r : CommRingOps A rel} (law : r.Laws) :
    (ring (b := b) (c := c) r).Laws :=
  CommRingOps.Laws.intro (r := ring r) (refl law) (symm law) (trans law) (add_congr law)
    (mul_congr law) (neg_congr law) (add_comm law) (add_assoc law) (add_zero law)
    (add_neg law) (mul_comm law) (mul_assoc law) (mul_one law) (mul_zero law) (mul_add law)

theorem pow_add {r : CommRingOps A rel} (law : r.Laws)
    (z : QuadPoly A b c) (m n : Nat) :
    Equivalent r (pow r z (m.add n)) (mul r (pow r z m) (pow r z n)) :=
  let l := ringLaws (b := b) (c := c) law
  Nat.rec (motive := fun n =>
    Equivalent r (pow r z (m.add n)) (mul r (pow r z m) (pow r z n)))
    (symm law (mul_one law (pow r z m)))
    (fun n ih =>
      l.trans (l.mul_congr (l.refl z) ih)
        (l.trans (l.symm (l.mul_assoc z (pow r z m) (pow r z n)))
          (l.trans (l.mul_congr (l.mul_comm z (pow r z m)) (l.refl (pow r z n)))
            (l.mul_assoc (pow r z m) z (pow r z n))))) n

theorem alpha_sq {r : CommRingOps A rel} (law : r.Laws) :
    Equivalent r (square r (alpha (b := b) (c := c) r)) (pair c b) :=
  let vars := Polynomial.Variables.cons b
    (Polynomial.Variables.cons c (Polynomial.Variables.nil r))
  let y := Polynomial.e0
  let x := Polynomial.e1
  let o := Polynomial.Expr.one
  let z := Polynomial.Expr.zero
  And.intro
    (Polynomial.prove r law vars ((z.mul z).add (x.mul (o.mul o))) x Eq.refl)
    (Polynomial.prove r law vars (((z.mul o).add (o.mul z)).add (y.mul (o.mul o))) y Eq.refl)

theorem norm_alpha {r : CommRingOps A rel} (law : r.Laws) :
    r.eqv (norm r (alpha (b := b) (c := c) r)) (r.neg c) :=
  let vars := Polynomial.Variables.cons b
    (Polynomial.Variables.cons c (Polynomial.Variables.nil r))
  let z := Polynomial.Expr.zero
  let o := Polynomial.Expr.one
  Polynomial.prove r law vars
    ((z.square.add (Polynomial.e0.mul (z.mul o))).sub (Polynomial.e1.mul o.square))
    Polynomial.e1.neg Eq.refl

theorem norm_one {r : CommRingOps A rel} (law : r.Laws) :
    r.eqv (norm r (one (b := b) (c := c) r)) r.one :=
  let vars := Polynomial.Variables.cons b
    (Polynomial.Variables.cons c (Polynomial.Variables.nil r))
  let z := Polynomial.Expr.zero
  let o := Polynomial.Expr.one
  Polynomial.prove r law vars
    ((o.square.add (Polynomial.e0.mul (o.mul z))).sub (Polynomial.e1.mul z.square)) o Eq.refl

end Omega.QuadPoly

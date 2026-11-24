module
prelude
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

The rank-two algebra with basis one and alpha and relation alpha squared
equals b times alpha plus c. The scalar ring determines equality on coordinates.
-/

noncomputable section
@[expose] public section

namespace Omega

structure QuadPoly (A : Type) (b c : A) where
  coefficients : Bool → A

abbrev IntQuadPoly (b c : Int) := QuadPoly Int b c
abbrev RatQuadPoly (b c : Int) := QuadPoly FiniteRatio (FiniteRatio.ofInt b) (FiniteRatio.ofInt c)

namespace QuadPoly

variable {A : Type} {rel : A → A → Prop} {b c : A}

def pair (x y : A) : QuadPoly A b c := ⟨fun i => Bool.rec (motive := fun _ => A) x y i⟩
def scalar (z : QuadPoly A b c) : A := z.coefficients .false
def linear (z : QuadPoly A b c) : A := z.coefficients .true

variable (r : CommRingOps A rel)

def Equivalent (z w : QuadPoly A b c) : Prop :=
  And (r.eqv z.scalar w.scalar) (r.eqv z.linear w.linear)

def ofScalar (x : A) : QuadPoly A b c := pair x r.zero
def zero : QuadPoly A b c := ofScalar r r.zero
def one : QuadPoly A b c := ofScalar r r.one
def alpha : QuadPoly A b c := pair r.zero r.one

def add (z w : QuadPoly A b c) : QuadPoly A b c :=
  pair (r.add z.scalar w.scalar) (r.add z.linear w.linear)

def neg (z : QuadPoly A b c) : QuadPoly A b c := pair (r.neg z.scalar) (r.neg z.linear)
def sub (z w : QuadPoly A b c) : QuadPoly A b c := add r z (neg r w)

def scale (a : A) (z : QuadPoly A b c) : QuadPoly A b c :=
  pair (r.mul a z.scalar) (r.mul a z.linear)

def mul (z w : QuadPoly A b c) : QuadPoly A b c :=
  let ys := r.mul z.linear w.linear
  pair
    (r.add (r.mul z.scalar w.scalar) (r.mul c ys))
    (r.add (r.add (r.mul z.scalar w.linear) (r.mul z.linear w.scalar)) (r.mul b ys))

def square (z : QuadPoly A b c) : QuadPoly A b c := mul r z z

def conj (z : QuadPoly A b c) : QuadPoly A b c :=
  pair (r.add z.scalar (r.mul b z.linear)) (r.neg z.linear)

def trace (z : QuadPoly A b c) : A := r.add (r.add z.scalar z.scalar) (r.mul b z.linear)

def norm (z : QuadPoly A b c) : A :=
  r.sub (r.add (r.square z.scalar) (r.mul b (r.mul z.scalar z.linear)))
    (r.mul c (r.square z.linear))

def pow (z : QuadPoly A b c) (n : Nat) : QuadPoly A b c :=
  Nat.rec (one r) (fun _ prev => mul r z prev) n

variable {r} (law : r.Laws)
include law

theorem refl (z : QuadPoly A b c) : Equivalent r z z :=
  And.intro (law.refl z.scalar) (law.refl z.linear)

theorem symm {z w : QuadPoly A b c} (h : Equivalent r z w) : Equivalent r w z :=
  And.intro (law.symm h.left) (law.symm h.right)

theorem trans {z w u : QuadPoly A b c} (h : Equivalent r z w) (g : Equivalent r w u) :
    Equivalent r z u :=
  And.intro (law.trans h.left g.left) (law.trans h.right g.right)

theorem add_congr {z w u v : QuadPoly A b c} (h : Equivalent r z w) (g : Equivalent r u v) :
    Equivalent r (add r z u) (add r w v) :=
  And.intro (law.add_congr h.left g.left) (law.add_congr h.right g.right)

theorem neg_congr {z w : QuadPoly A b c} (h : Equivalent r z w) :
    Equivalent r (neg r z) (neg r w) :=
  And.intro (law.neg_congr h.left) (law.neg_congr h.right)

theorem mul_congr {z w u v : QuadPoly A b c} (h : Equivalent r z w) (g : Equivalent r u v) :
    Equivalent r (mul r z u) (mul r w v) :=
  have cross := law.mul_congr h.right g.right
  And.intro (law.add_congr (law.mul_congr h.left g.left) (law.mul_congr (law.refl c) cross))
    (law.add_congr (law.add_congr (law.mul_congr h.left g.right) (law.mul_congr h.right g.left))
      (law.mul_congr (law.refl b) cross))

theorem add_comm (z w : QuadPoly A b c) : Equivalent r (add r z w) (add r w z) :=
  And.intro (law.add_comm z.scalar w.scalar) (law.add_comm z.linear w.linear)

theorem add_assoc (z w u : QuadPoly A b c) :
    Equivalent r (add r (add r z w) u) (add r z (add r w u)) :=
  And.intro (law.add_assoc z.scalar w.scalar u.scalar) (law.add_assoc z.linear w.linear u.linear)

theorem add_zero (z : QuadPoly A b c) : Equivalent r (add r z (zero r)) z :=
  And.intro (law.add_zero z.scalar) (law.add_zero z.linear)

theorem add_neg (z : QuadPoly A b c) : Equivalent r (add r z (neg r z)) (zero r) :=
  And.intro (law.add_neg z.scalar) (law.add_neg z.linear)

open Polynomial

private def mulScalar (c x y u v : Expr) : Expr := (x.mul u).add (c.mul (y.mul v))
private def mulLinear (b x y u v : Expr) : Expr :=
  ((x.mul v).add (y.mul u)).add (b.mul (y.mul v))

theorem mul_comm (z w : QuadPoly A b c) : Equivalent r (mul r z w) (mul r w z) :=
  let vars := Variables.cons z.scalar (Variables.cons z.linear
    (Variables.cons w.scalar (Variables.cons w.linear (Variables.cons b
      (Variables.cons c (Variables.nil r))))))
  And.intro
    (prove r law vars (mulScalar e5 e0 e1 e2 e3) (mulScalar e5 e2 e3 e0 e1) Eq.refl)
    (prove r law vars (mulLinear e4 e0 e1 e2 e3) (mulLinear e4 e2 e3 e0 e1) Eq.refl)

theorem mul_assoc (z w u : QuadPoly A b c) :
    Equivalent r (mul r (mul r z w) u) (mul r z (mul r w u)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.cons w.scalar (Variables.cons w.linear
      (Variables.cons u.scalar (Variables.cons u.linear (Variables.nil r))))))))
  let leftScalar := mulScalar e1 e2 e3 e4 e5
  let leftLinear := mulLinear e0 e2 e3 e4 e5
  let rightScalar := mulScalar e1 e4 e5 e6 e7
  let rightLinear := mulLinear e0 e4 e5 e6 e7
  And.intro
    (prove r law vars (mulScalar e1 leftScalar leftLinear e6 e7)
      (mulScalar e1 e2 e3 rightScalar rightLinear) Eq.refl)
    (prove r law vars (mulLinear e0 leftScalar leftLinear e6 e7)
      (mulLinear e0 e2 e3 rightScalar rightLinear) Eq.refl)

theorem mul_add (z w u : QuadPoly A b c) :
    Equivalent r (mul r z (add r w u)) (add r (mul r z w) (mul r z u)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.cons w.scalar (Variables.cons w.linear
      (Variables.cons u.scalar (Variables.cons u.linear (Variables.nil r))))))))
  And.intro
    (prove r law vars (mulScalar e1 e2 e3 (e4.add e6) (e5.add e7))
      ((mulScalar e1 e2 e3 e4 e5).add (mulScalar e1 e2 e3 e6 e7)) Eq.refl)
    (prove r law vars (mulLinear e0 e2 e3 (e4.add e6) (e5.add e7))
      ((mulLinear e0 e2 e3 e4 e5).add (mulLinear e0 e2 e3 e6 e7)) Eq.refl)

theorem mul_one (z : QuadPoly A b c) : Equivalent r (mul r z (one r)) z :=
  let vars := Variables.cons z.scalar (Variables.cons z.linear
    (Variables.cons b (Variables.cons c (Variables.nil r))))
  And.intro
    (prove r law vars (mulScalar e3 e0 e1 .one .zero) e0 Eq.refl)
    (prove r law vars (mulLinear e2 e0 e1 .one .zero) e1 Eq.refl)

theorem mul_zero (z : QuadPoly A b c) : Equivalent r (mul r z (zero r)) (zero r) :=
  let vars := Variables.cons z.scalar (Variables.cons z.linear
    (Variables.cons b (Variables.cons c (Variables.nil r))))
  And.intro
    (prove r law vars (mulScalar e3 e0 e1 .zero .zero) .zero Eq.refl)
    (prove r law vars (mulLinear e2 e0 e1 .zero .zero) .zero Eq.refl)

theorem conj_conj (z : QuadPoly A b c) : Equivalent r (conj r (conj r z)) z :=
  let vars := Variables.cons b (Variables.cons z.scalar (Variables.cons z.linear (Variables.nil r)))
  And.intro
    (prove r law vars ((e1.add (e0.mul e2)).add (e0.mul e2.neg)) e1 Eq.refl)
    (law.neg_neg z.linear)

/-- Conjugation preserves addition and multiplication while changing the root. -/
theorem conj_add (z w : QuadPoly A b c) :
    Equivalent r (conj r (add r z w)) (add r (conj r z) (conj r w)) :=
  let vars := Variables.cons b (Variables.cons z.scalar (Variables.cons z.linear
    (Variables.cons w.scalar (Variables.cons w.linear (Variables.nil r)))))
  And.intro
    (prove r law vars ((e1.add e3).add (e0.mul (e2.add e4)))
      ((e1.add (e0.mul e2)).add (e3.add (e0.mul e4))) Eq.refl)
    (law.neg_add z.linear w.linear)

theorem conj_mul (z w : QuadPoly A b c) :
    Equivalent r (conj r (mul r z w)) (mul r (conj r z) (conj r w)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.cons w.scalar (Variables.cons w.linear (Variables.nil r))))))
  let conjZ := e2.add (e0.mul e3)
  let conjW := e4.add (e0.mul e5)
  let linear := mulLinear e0 e2 e3 e4 e5
  And.intro
    (prove r law vars ((mulScalar e1 e2 e3 e4 e5).add (e0.mul linear))
      (mulScalar e1 conjZ e3.neg conjW e5.neg) Eq.refl)
    (prove r law vars linear.neg (mulLinear e0 conjZ e3.neg conjW e5.neg) Eq.refl)

theorem add_conj (z : QuadPoly A b c) :
    Equivalent r (add r z (conj r z)) (ofScalar r (trace r z)) :=
  let vars := Variables.cons b (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.nil r)))
  And.intro
    (prove r law vars (e1.add (e1.add (e0.mul e2))) ((e1.add e1).add (e0.mul e2)) Eq.refl)
    (law.add_neg z.linear)

private def normExpr (b c x y : Expr) : Expr :=
  (x.square.add (b.mul (x.mul y))).sub (c.mul y.square)

theorem mul_conj (z : QuadPoly A b c) :
    Equivalent r (mul r z (conj r z)) (ofScalar r (norm r z)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.nil r))))
  let conjScalar := e2.add (e0.mul e3)
  And.intro
    (prove r law vars (mulScalar e1 e2 e3 conjScalar e3.neg) (normExpr e0 e1 e2 e3) Eq.refl)
    (prove r law vars (mulLinear e0 e2 e3 conjScalar e3.neg) .zero Eq.refl)

theorem norm_mul (z w : QuadPoly A b c) :
    r.eqv (norm r (mul r z w)) (r.mul (norm r z) (norm r w)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.cons w.scalar (Variables.cons w.linear (Variables.nil r))))))
  prove r law vars
    (normExpr e0 e1 (mulScalar e1 e2 e3 e4 e5) (mulLinear e0 e2 e3 e4 e5))
    ((normExpr e0 e1 e2 e3).mul (normExpr e0 e1 e4 e5)) Eq.refl

theorem mul_scale (a : A) (z w : QuadPoly A b c) :
    Equivalent r (mul r z (scale r a w)) (scale r a (mul r z w)) :=
  let vars := Variables.cons b (Variables.cons c (Variables.cons a (Variables.cons z.scalar
    (Variables.cons z.linear (Variables.cons w.scalar (Variables.cons w.linear (Variables.nil r)))))))
  And.intro
    (prove r law vars (mulScalar e1 e3 e4 (e2.mul e5) (e2.mul e6))
      (e2.mul (mulScalar e1 e3 e4 e5 e6)) Eq.refl)
    (prove r law vars (mulLinear e0 e3 e4 (e2.mul e5) (e2.mul e6))
      (e2.mul (mulLinear e0 e3 e4 e5 e6)) Eq.refl)

theorem scale_congr (a : A) {z w : QuadPoly A b c} (h : Equivalent r z w) :
    Equivalent r (scale r a z) (scale r a w) :=
  And.intro (law.mul_congr (law.refl a) h.left) (law.mul_congr (law.refl a) h.right)

end QuadPoly

namespace RatQuadPoly

open QuadPoly

def inv {b c : Int} (z : RatQuadPoly b c) : RatQuadPoly b c :=
  scale rationalRing (norm rationalRing z).inv (conj rationalRing z)

/-- In every quadratic algebra, nonzero norm gives a two-sided unit. -/
theorem mul_inv {b c : Int} (z : RatQuadPoly b c)
    (h : Not (Eq (norm rationalRing z).num Int.zero)) :
    Equivalent rationalRing (mul rationalRing z z.inv) (one rationalRing) :=
  let normZ := norm rationalRing z
  let law := rationalRingLaws
  have step := mul_scale law normZ.inv z (conj rationalRing z)
  have product := scale_congr law normZ.inv (mul_conj law z)
  have cancel := And.intro
    (law.trans (law.mul_comm normZ.inv normZ) (normZ.mul_inv_cancel h))
    (law.mul_zero normZ.inv)
  trans law step (trans law product cancel)

end RatQuadPoly
end Omega

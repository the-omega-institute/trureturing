/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Geometry.Cayley3D.Adjoint

/-!
Omega original.

Rational Cayley matrices for all rational three-vectors, with the exact forward
identity, orthogonality, determinant and norm preservation under iteration.
-/

noncomputable section

@[expose] public section

namespace Omega

/-- A three-by-three integer matrix stored by rows. -/
structure Mat3 where
  row1 : Vec3
  row2 : Vec3
  row3 : Vec3

namespace Mat3

def diagonal (k : Int) : Mat3 :=
  ⟨⟨k, Int.zero, Int.zero⟩, ⟨Int.zero, k, Int.zero⟩, ⟨Int.zero, Int.zero, k⟩⟩

def one : Mat3 := diagonal Int.one

def transpose (a : Mat3) : Mat3 :=
  ⟨⟨a.row1.x, a.row2.x, a.row3.x⟩, ⟨a.row1.y, a.row2.y, a.row3.y⟩,
   ⟨a.row1.z, a.row2.z, a.row3.z⟩⟩

def apply (a : Mat3) (v : Vec3) : Vec3 := ⟨a.row1.dot3 v, a.row2.dot3 v, a.row3.dot3 v⟩

def mul (a b : Mat3) : Mat3 :=
  let t := b.transpose
  let row := fun v : Vec3 => ⟨v.dot3 t.row1, v.dot3 t.row2, v.dot3 t.row3⟩
  ⟨row a.row1, row a.row2, row a.row3⟩

def scale (k : Int) (a : Mat3) : Mat3 :=
  ⟨Vec3.scale k a.row1, Vec3.scale k a.row2, Vec3.scale k a.row3⟩

def det (a : Mat3) : Int :=
  let b := a.row2
  let c := a.row3
  a.row1.dot3 ⟨(b.y.mul c.z).sub (b.z.mul c.y),
    (b.z.mul c.x).sub (b.x.mul c.z), (b.x.mul c.y).sub (b.y.mul c.x)⟩

theorem ext {a b : Mat3} (h1 : Eq a.row1 b.row1) (h2 : Eq a.row2 b.row2) (h3 : Eq a.row3 b.row3) :
    Eq a b :=
  (congrArg (fun r => Mat3.mk r a.row2 a.row3) h1).trans (Eq.map₂ (Mat3.mk b.row1) h2 h3)

theorem scale_one (a : Mat3) : Eq (scale Int.one a) a :=
  ext (Vec3.scale_one a.row1) (Vec3.scale_one a.row2) (Vec3.scale_one a.row3)

end Mat3

structure RatMat3 where
  num : Mat3
  denPred : Nat

namespace RatMat3

def den (a : RatMat3) : Nat := a.denPred.succ

def one : RatMat3 := ⟨Mat3.one, Nat.zero⟩

def transpose (a : RatMat3) : RatMat3 := ⟨a.num.transpose, a.denPred⟩

def mul (a b : RatMat3) : RatMat3 := ⟨a.num.mul b.num, IntRatio.mulDenPred a.denPred b.denPred⟩

def apply (a : RatMat3) (v : RatVec3) : RatVec3 :=
  ⟨a.num.apply v.num, IntRatio.mulDenPred a.denPred v.denPred⟩

def det (a : RatMat3) : IntRatio := IntRatio.value a.num.det ((a.den.mul a.den).mul a.den)

def Equiv (a b : RatMat3) : Prop :=
  Eq (Mat3.scale (Int.ofNat b.den) a.num) (Mat3.scale (Int.ofNat a.den) b.num)

theorem equiv_scaled (a b : RatMat3) (n : Nat)
    (hn : Eq a.num (Mat3.scale (Int.ofNat n) b.num)) (hd : Eq a.den (b.den.mul n)) : Equiv a b :=
  let d := Int.ofNat b.den
  let k := Int.ofNat n
  have h : Eq (Mat3.scale d (Mat3.scale k b.num)) (Mat3.scale (d.mul k) b.num) :=
    Mat3.ext (Vec3.scale_mul b.num.row1 d k) (Vec3.scale_mul b.num.row2 d k)
      (Vec3.scale_mul b.num.row3 d k)
  (congrArg (Mat3.scale d) hn).trans (h.trans
    (congrArg (fun m => Mat3.scale (Int.ofNat m) b.num) hd.symm))

end RatMat3

namespace Geometry.Cayley3D

open Quaternion.Polynomial

def cayleyQuaternion (s : RatVec3) : Quaternion :=
  ⟨Int.ofNat s.den, s.num.x, s.num.y, s.num.z⟩

theorem cayleyQuaternion_nonzero (s : RatVec3) : (cayleyQuaternion s).Nonzero :=
  fun h => Int.ofNat_succ_ne_zero s.denPred h.left

/-- Integer numerator of the Cayley matrix for the rational parameter (x,y,z)/d.
The diagonal scalar is d²−(x²+y²+z²) and the skew term is 2d times the cross-product matrix. -/
def cayleyNum (d : Int) (v : Vec3) : Mat3 :=
  let x := v.x
  let y := v.y
  let z := v.z
  let b := (Int.square d).sub ((Int.square x).add ((Int.square y).add (Int.square z)))
  let twice := fun (a : Int) => a.add a
  ⟨⟨b.add (twice (Int.square x)), twice ((x.mul y).sub (d.mul z)),
      twice ((x.mul z).add (d.mul y))⟩,
   ⟨twice ((y.mul x).add (d.mul z)), b.add (twice (Int.square y)),
      twice ((y.mul z).sub (d.mul x))⟩,
   ⟨twice ((z.mul x).sub (d.mul y)), twice ((z.mul y).add (d.mul x)),
      b.add (twice (Int.square z))⟩⟩

/-- The exact rational Cayley transform with positive denominator d²+x²+y²+z². -/
def Cayley (s : RatVec3) : RatMat3 :=
  ⟨cayleyNum (Int.ofNat s.den) s.num, (cayleyQuaternion s).normSq.pred⟩

/-- The numerator of I+X, with X the matrix for crossing by (x,y,z)/d. -/
def skewPlusNum (d : Int) (v : Vec3) : Mat3 :=
  ⟨⟨d, v.z.neg, v.y⟩, ⟨v.z, d, v.x.neg⟩, ⟨v.y.neg, v.x, d⟩⟩

def skewPlus (s : RatVec3) : RatMat3 := ⟨skewPlusNum (Int.ofNat s.den) s.num, s.denPred⟩

def skewMinus (s : RatVec3) : RatMat3 := (skewPlus s).transpose

private structure ExprRow where
  x : Expr
  y : Expr
  z : Expr

private def ExprRow.dot (a b : ExprRow) : Expr :=
  (a.x.mul b.x).add ((a.y.mul b.y).add (a.z.mul b.z))

private def ExprRow.scale (k : Expr) (a : ExprRow) : ExprRow :=
  ⟨k.mul a.x, k.mul a.y, k.mul a.z⟩

private structure ExprMat where
  row1 : ExprRow
  row2 : ExprRow
  row3 : ExprRow

private def ExprMat.transpose (a : ExprMat) : ExprMat :=
  ⟨⟨a.row1.x, a.row2.x, a.row3.x⟩, ⟨a.row1.y, a.row2.y, a.row3.y⟩,
   ⟨a.row1.z, a.row2.z, a.row3.z⟩⟩

private def ExprMat.mul (a b : ExprMat) : ExprMat :=
  let t := b.transpose
  let row := fun v : ExprRow => ⟨v.dot t.row1, v.dot t.row2, v.dot t.row3⟩
  ⟨row a.row1, row a.row2, row a.row3⟩

private def ExprMat.det (a : ExprMat) : Expr :=
  let b := a.row2
  let c := a.row3
  a.row1.dot ⟨(b.y.mul c.z).sub (b.z.mul c.y),
    (b.z.mul c.x).sub (b.x.mul c.z), (b.x.mul c.y).sub (b.y.mul c.x)⟩

private def reifiedCayley (q : Coordinates) : ExprMat :=
  let d := q.w
  let x := q.x
  let y := q.y
  let z := q.z
  let b := d.sq.sub (x.sq.add (y.sq.add z.sq))
  ⟨⟨b.add x.sq.double, ((x.mul y).sub (d.mul z)).double, ((x.mul z).add (d.mul y)).double⟩,
   ⟨((y.mul x).add (d.mul z)).double, b.add y.sq.double, ((y.mul z).sub (d.mul x)).double⟩,
   ⟨((z.mul x).sub (d.mul y)).double, ((z.mul y).add (d.mul x)).double, b.add z.sq.double⟩⟩

private def inputs (d : Int) (v : Vec3) (rest : Values) : Values :=
  .cons d (.cons v.x (.cons v.y (.cons v.z rest)))

theorem cayleyNum_apply (d : Int) (s v : Vec3) :
    Eq ((cayleyNum d s).apply v) (adjointNum ⟨d, s.x, s.y, s.z⟩ v) :=
  let p := Coordinates.variables Nat.zero
  let i := Nat.zero.succ.succ.succ.succ
  let a := Expr.var i
  let b := Expr.var i.succ
  let c := Expr.var i.succ.succ
  let v' : Coordinates := ⟨.zero, a, b, c⟩
  let matrix := reifiedCayley p
  let r := (p.mul v').mul p.conj
  let values := inputs d s (.cons v.x (.cons v.y (.cons v.z .nil)))
  Vec3.ext ((matrix.row1.dot ⟨a, b, c⟩).sound r.x values Eq.refl)
    ((matrix.row2.dot ⟨a, b, c⟩).sound r.y values Eq.refl)
    ((matrix.row3.dot ⟨a, b, c⟩).sound r.z values Eq.refl)

theorem cayley_action (s v : RatVec3) : Eq ((Cayley s).apply v) (Ad (cayleyQuaternion s) v) :=
  RatVec3.eq_of_num_den (cayleyNum_apply (Int.ofNat s.den) s.num v.num) Eq.refl

private theorem cayley_integer_identity (d : Int) (v : Vec3) :
    Eq ((skewPlusNum d v).transpose.mul (cayleyNum d v))
      (Mat3.scale (Quaternion.dot ⟨d, v.x, v.y, v.z⟩ ⟨d, v.x, v.y, v.z⟩) (skewPlusNum d v)) :=
  let q := Coordinates.variables Nat.zero
  let values := inputs d v .nil
  let plus : ExprMat := ⟨⟨q.w, q.z.neg, q.y⟩, ⟨q.z, q.w, q.x.neg⟩, ⟨q.y.neg, q.x, q.w⟩⟩
  let lhs := plus.transpose.mul (reifiedCayley q)
  let n := q.dot q
  let r1 := plus.row1.scale n
  let r2 := plus.row2.scale n
  let r3 := plus.row3.scale n
  Mat3.ext
    (Vec3.ext (lhs.row1.x.sound r1.x values Eq.refl) (lhs.row1.y.sound r1.y values Eq.refl)
      (lhs.row1.z.sound r1.z values Eq.refl))
    (Vec3.ext (lhs.row2.x.sound r2.x values Eq.refl) (lhs.row2.y.sound r2.y values Eq.refl)
      (lhs.row2.z.sound r2.z values Eq.refl))
    (Vec3.ext (lhs.row3.x.sound r3.x values Eq.refl) (lhs.row3.y.sound r3.y values Eq.refl)
      (lhs.row3.z.sound r3.z values Eq.refl))

theorem cayley_identity (s : RatVec3) :
    RatMat3.Equiv ((skewMinus s).mul (Cayley s)) (skewPlus s) :=
  let q := cayleyQuaternion s
  let n := (Cayley s).den
  let h := (congrArg Int.ofNat (adjointDen_eq q (cayleyQuaternion_nonzero s))).trans q.normSq_cast
  RatMat3.equiv_scaled ((skewMinus s).mul (Cayley s)) (skewPlus s) n
    ((cayley_integer_identity (Int.ofNat s.den) s.num).trans
      (congrArg (fun k => Mat3.scale k (skewPlus s).num) h.symm)) Eq.refl

private theorem cayley_integer_orthogonal (d : Int) (v : Vec3) :
    Eq ((cayleyNum d v).transpose.mul (cayleyNum d v))
      (Mat3.diagonal (Int.square (Quaternion.dot ⟨d, v.x, v.y, v.z⟩ ⟨d, v.x, v.y, v.z⟩))) :=
  let q := Coordinates.variables Nat.zero
  let values := inputs d v .nil
  let a := reifiedCayley q
  let lhs := a.transpose.mul a
  let n := (q.dot q).sq
  Mat3.ext
    (Vec3.ext (lhs.row1.x.sound n values Eq.refl) (lhs.row1.y.sound .zero values Eq.refl)
      (lhs.row1.z.sound .zero values Eq.refl))
    (Vec3.ext (lhs.row2.x.sound .zero values Eq.refl) (lhs.row2.y.sound n values Eq.refl)
      (lhs.row2.z.sound .zero values Eq.refl))
    (Vec3.ext (lhs.row3.x.sound .zero values Eq.refl) (lhs.row3.y.sound .zero values Eq.refl)
      (lhs.row3.z.sound n values Eq.refl))

private theorem scaled_identity (k : Int) : Eq (Mat3.diagonal k) (Mat3.scale k Mat3.one) :=
  (Mat3.ext
    (Vec3.ext (Int.mul_one k) (Int.mul_zero k) (Int.mul_zero k))
    (Vec3.ext (Int.mul_zero k) (Int.mul_one k) (Int.mul_zero k))
    (Vec3.ext (Int.mul_zero k) (Int.mul_zero k) (Int.mul_one k)) :
      Eq (Mat3.scale k Mat3.one) (Mat3.diagonal k)).symm

theorem cayley_orthogonal (s : RatVec3) :
    RatMat3.Equiv ((Cayley s).transpose.mul (Cayley s)) RatMat3.one :=
  let n := (Cayley s).den
  let q := cayleyQuaternion s
  have h := (congrArg Int.ofNat (adjointDen_eq q (cayleyQuaternion_nonzero s))).trans q.normSq_cast
  RatMat3.equiv_scaled ((Cayley s).transpose.mul (Cayley s)) RatMat3.one (n.mul n)
    ((cayley_integer_orthogonal (Int.ofNat s.den) s.num).trans
      ((congrArg (fun t => Mat3.diagonal (Int.square t)) h.symm).trans
        (scaled_identity (Int.ofNat (n.mul n))))) (Nat.one_mul (n.mul n)).symm

private theorem cayley_integer_det (d : Int) (v : Vec3) :
    Eq (cayleyNum d v).det
      (let n := Quaternion.dot ⟨d, v.x, v.y, v.z⟩ ⟨d, v.x, v.y, v.z⟩
       (n.mul n).mul n) :=
  let q := Coordinates.variables Nat.zero
  let n := q.dot q
  (reifiedCayley q).det.sound ((n.mul n).mul n) (inputs d v .nil) Eq.refl

theorem cayley_det (s : RatVec3) : IntRatio.Equivalent (Cayley s).det (IntRatio.ofInt Int.one) :=
  let n := (Cayley s).den
  let q := cayleyQuaternion s
  have e := (congrArg Int.ofNat (adjointDen_eq q (cayleyQuaternion_nonzero s))).trans q.normSq_cast
  have h : Eq (Cayley s).num.det (Int.ofNat ((n.mul n).mul n)) :=
    (cayley_integer_det (Int.ofNat s.den) s.num).trans (congrArg (fun t : Int => (t.mul t).mul t) e.symm)
  have hn : Not (Eq n Nat.zero) := Nat.succ_ne_zero (Cayley s).denPred
  have nonzero : Not (Eq ((n.mul n).mul n) Nat.zero) :=
    fun e => (Nat.mul_eq_zero.mp e).elim (fun e => (Nat.mul_eq_zero.mp e).elim hn hn) hn
  Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t ((n.mul n).mul n)) (IntRatio.ofInt Int.one))
    h.symm (IntRatio.value_self ((n.mul n).mul n) nonzero)

theorem cayley_dot (s u v : RatVec3) :
    IntRatio.Equivalent (((Cayley s).apply u).dot3 ((Cayley s).apply v)) (u.dot3 v) :=
  Eq.subst (fun t => IntRatio.Equivalent t (u.dot3 v))
    (Eq.map₂ RatVec3.dot3 (cayley_action s u) (cayley_action s v)).symm
    (ad_dot (cayleyQuaternion s) (cayleyQuaternion_nonzero s) u v)

def cayleyIterate (s : RatVec3) (v : RatVec3) (n : Nat) : RatVec3 :=
  Nat.rec v (fun _ w => (Cayley s).apply w) n

theorem cayley_iterate_norm (s v : RatVec3) (n : Nat) :
    IntRatio.Equivalent ((cayleyIterate s v n).dot3 (cayleyIterate s v n)) (v.dot3 v) :=
  Nat.rec (motive := fun n =>
    IntRatio.Equivalent ((cayleyIterate s v n).dot3 (cayleyIterate s v n)) (v.dot3 v))
    (IntRatio.equivalent_refl (v.dot3 v))
    (fun n ih =>
      (cayley_dot s (cayleyIterate s v n) (cayleyIterate s v n)).trans ih) n

end Geometry.Cayley3D
end Omega

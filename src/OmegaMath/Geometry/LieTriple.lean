module
prelude
public import OmegaMath.Geometry.Cayley3D

/-! Omega original.

The Lie triple bracket on integer three-vectors and its constant-curvature contraction.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.LieTriple

open Quaternion.Polynomial

def add (u v : Vec3) : Vec3 := ⟨u.x.add v.x, u.y.add v.y, u.z.add v.z⟩

def neg (u : Vec3) : Vec3 := ⟨u.x.neg, u.y.neg, u.z.neg⟩

def zero : Vec3 := ⟨Int.zero, Int.zero, Int.zero⟩

/-- The commutator of pure Hamilton quaternions, expressed as twice the cross product. -/
def commutator (u v : Vec3) : Vec3 :=
  Vec3.scale Int.two
    ⟨(u.y.mul v.z).sub (u.z.mul v.y),
     (u.z.mul v.x).sub (u.x.mul v.z),
     (u.x.mul v.y).sub (u.y.mul v.x)⟩

def lieTriple (u v w : Vec3) : Vec3 :=
  add (v.scale (u.dot3 w)) (neg (u.scale (v.dot3 w)))

private structure PolyVec where
  x : Expr
  y : Expr
  z : Expr

private def PolyVec.variables (n : Nat) : PolyVec :=
  ⟨.var n, .var n.succ, .var n.succ.succ⟩

private def PolyVec.next (n : Nat) : Nat := n.succ.succ.succ

private def PolyVec.add (u v : PolyVec) : PolyVec :=
  ⟨u.x.add v.x, u.y.add v.y, u.z.add v.z⟩

private def PolyVec.neg (u : PolyVec) : PolyVec :=
  ⟨u.x.neg, u.y.neg, u.z.neg⟩

private def PolyVec.scale (u : PolyVec) (a : Expr) : PolyVec :=
  ⟨a.mul u.x, a.mul u.y, a.mul u.z⟩

private def PolyVec.dot (u v : PolyVec) : Expr :=
  (u.x.mul v.x).add ((u.y.mul v.y).add (u.z.mul v.z))

private def PolyVec.triple (u v w : PolyVec) : PolyVec :=
  (v.scale (u.dot w)).add (u.scale (v.dot w)).neg

private def inputs (u : Vec3) (tail : Values) : Values :=
  .cons u.x (.cons u.y (.cons u.z tail))

theorem lieTriple_antisymm (u v w : Vec3) :
    Eq (lieTriple u v w) (neg (lieTriple v u w)) :=
  let i := Nat.zero
  let j := PolyVec.next i
  let k := PolyVec.next j
  let U := PolyVec.variables i
  let V := PolyVec.variables j
  let W := PolyVec.variables k
  let p := U.triple V W
  let q := (V.triple U W).neg
  let values := inputs u (inputs v (inputs w .nil))
  Vec3.ext (p.x.sound q.x values Eq.refl) (p.y.sound q.y values Eq.refl)
    (p.z.sound q.z values Eq.refl)

theorem lieTriple_jacobi (u v w : Vec3) :
    Eq (add (add (lieTriple u v w) (lieTriple v w u)) (lieTriple w u v)) zero :=
  let i := Nat.zero
  let j := PolyVec.next i
  let k := PolyVec.next j
  let U := PolyVec.variables i
  let V := PolyVec.variables j
  let W := PolyVec.variables k
  let p := ((U.triple V W).add (V.triple W U)).add (W.triple U V)
  let values := inputs u (inputs v (inputs w .nil))
  Vec3.ext (p.x.sound .zero values Eq.refl) (p.y.sound .zero values Eq.refl)
    (p.z.sound .zero values Eq.refl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem lieTriple_derivation (x y u v w : Vec3) :
    Eq (lieTriple x y (lieTriple u v w))
      (add (add (lieTriple (lieTriple x y u) v w) (lieTriple u (lieTriple x y v) w))
        (lieTriple u v (lieTriple x y w))) :=
  let i := Nat.zero
  let j := PolyVec.next i
  let k := PolyVec.next j
  let l := PolyVec.next k
  let m := PolyVec.next l
  let X := PolyVec.variables i
  let Y := PolyVec.variables j
  let U := PolyVec.variables k
  let V := PolyVec.variables l
  let W := PolyVec.variables m
  let p := X.triple Y (U.triple V W)
  let q := ((X.triple Y U).triple V W).add (U.triple (X.triple Y V) W)
  let q := q.add (U.triple V (X.triple Y W))
  let values := inputs x (inputs y (inputs u (inputs v (inputs w .nil))))
  Vec3.ext (p.x.sound q.x values Eq.refl) (p.y.sound q.y values Eq.refl)
    (p.z.sound q.z values Eq.refl)

def gramAreaSq (u v : Vec3) : Int :=
  ((u.dot3 u).mul (v.dot3 v)).sub ((u.dot3 v).square)

/-- The sectional curvature numerator in the convention determined by this bracket. -/
theorem lieTriple_unit_sectional_curvature (u v : Vec3) :
    Eq ((lieTriple u v u).dot3 v) (gramAreaSq u v) :=
  let U := PolyVec.variables Nat.zero
  let V := PolyVec.variables (PolyVec.next Nat.zero)
  ((U.triple V U).dot V).sound
    (((U.dot U).mul (V.dot V)).sub (U.dot V).sq) (inputs u (inputs v .nil)) Eq.refl

/-- Interchanging the last two slots of the curvature contraction changes its sign. -/
theorem lieTriple_sectional_curvature_reversed (u v : Vec3) :
    Eq ((lieTriple u v v).dot3 u) (gramAreaSq u v).neg :=
  let U := PolyVec.variables Nat.zero
  let V := PolyVec.variables (PolyVec.next Nat.zero)
  ((U.triple V V).dot U).sound
    (((U.dot U).mul (V.dot V)).sub (U.dot V).sq).neg (inputs u (inputs v .nil)) Eq.refl

def areaDenPred (u v : RatVec3) : Nat :=
  let pair := IntRatio.mulDenPred u.denPred v.denPred
  IntRatio.mulDenPred pair pair

/-- Squared Gram area with denominator `(u.den * v.den)²`. -/
def rationalGramAreaSq (u v : RatVec3) : IntRatio :=
  .fraction (gramAreaSq u.num v.num) (areaDenPred u v)

/-- The contraction is quadratic in each input, so it has the same denominator as the Gram area. -/
def rationalCurvatureNumerator (u v : RatVec3) : IntRatio :=
  .fraction ((lieTriple u.num v.num u.num).dot3 v.num) (areaDenPred u v)

/-- Canceling the common Gram factor yields exactly one on every nondegenerate rational plane. -/
theorem lieTriple_sectional_ratio (u v : RatVec3)
    (h : Not (Eq (gramAreaSq u.num v.num) Int.zero)) :
    IntRatio.Equivalent
      ((rationalCurvatureNumerator u v).mul (rationalGramAreaSq u v).inv)
      (IntRatio.ofInt Int.one) :=
  let den := areaDenPred u v
  Eq.subst (fun n => IntRatio.Equivalent
      ((IntRatio.fraction n den).mul (rationalGramAreaSq u v).inv) (IntRatio.ofInt Int.one))
    (lieTriple_unit_sectional_curvature u.num v.num).symm
    (IntRatio.mul_inv_cancel (gramAreaSq u.num v.num) den h)

end Omega.Geometry.LieTriple

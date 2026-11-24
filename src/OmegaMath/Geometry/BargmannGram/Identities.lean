module
prelude
public import OmegaMath.Geometry.BargmannGram.Coordinates
import OmegaMath.Geometry.BargmannGram.Polynomial

/-!
Omega original.

Hamilton multiplication preserves the squared norm. The quaternion triad with
repeated outer input lies in the linear span of its two inputs.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.BargmannGram

open Polynomial

private structure QuadExpr where
  w : Expr
  x : Expr
  y : Expr
  z : Expr

private def QuadExpr.dot (a b : QuadExpr) : Expr :=
  ((a.w.mul b.w).add (a.x.mul b.x)).add ((a.y.mul b.y).add (a.z.mul b.z))

private def QuadExpr.mul (a b : QuadExpr) : QuadExpr :=
  ⟨(((a.w.mul b.w).sub (a.x.mul b.x)).sub (a.y.mul b.y)).sub (a.z.mul b.z),
   (((a.w.mul b.x).add (a.x.mul b.w)).add (a.y.mul b.z)).sub (a.z.mul b.y),
   (((a.w.mul b.y).sub (a.x.mul b.z)).add (a.y.mul b.w)).add (a.z.mul b.x),
   (((a.w.mul b.z).add (a.x.mul b.y)).sub (a.y.mul b.x)).add (a.z.mul b.w)⟩

private def QuadExpr.conj (a : QuadExpr) : QuadExpr := ⟨a.w, a.x.neg, a.y.neg, a.z.neg⟩
private def QuadExpr.scale (k : Expr) (a : QuadExpr) : QuadExpr :=
  ⟨k.mul a.w, k.mul a.x, k.mul a.y, k.mul a.z⟩

private def variables (n : Nat) : QuadExpr :=
  ⟨Expr.var n, Expr.var n.succ, Expr.var n.succ.succ, Expr.var n.succ.succ.succ⟩

private def bindQuad (a : Quad4) (v : Nat → Int) : Nat → Int :=
  Expr.bind a.w (Expr.bind a.x (Expr.bind a.y (Expr.bind a.z v)))

namespace Quad4

theorem dot_comm (a b : Quad4) : Eq (a.dot b) (b.dot a) :=
  Eq.map₂ Int.add (Eq.map₂ Int.add (Int.mul_comm _ _) (Int.mul_comm _ _))
    (Eq.map₂ Int.add (Int.mul_comm _ _) (Int.mul_comm _ _))

theorem dot_scale_left (k : Int) (a b : Quad4) : Eq ((scale k a).dot b) (k.mul (a.dot b)) :=
  let v := Expr.bind k (bindQuad a (bindQuad b (fun _ => Int.zero)))
  let scale := Expr.var Nat.zero
  let α := variables Nat.zero.succ
  let β := variables Nat.zero.succ.succ.succ.succ.succ
  Expr.certify v ((α.scale scale).dot β) (scale.mul (α.dot β)) Eq.refl

theorem dot_scale_right (k : Int) (a b : Quad4) : Eq (a.dot (scale k b)) (k.mul (a.dot b)) :=
  (dot_comm a (scale k b)).trans ((dot_scale_left k b a).trans (congrArg k.mul (dot_comm b a)))

theorem normSq_scale (k : Int) (a : Quad4) :
    Eq (scale k a).normSq (k.natAbs.mul (k.natAbs.mul a.normSq)) :=
  Int.ofNat_inj.mp ((normSq_cast (scale k a)).trans
    ((dot_scale_left k a (scale k a)).trans
      ((congrArg k.mul (dot_scale_right k a a)).trans
        ((Int.mul_assoc k k (a.dot a)).symm.trans
          (Eq.map₂ Int.mul Int.natAbs_mul_self.symm (normSq_cast a).symm |>.trans
            (congrArg Int.ofNat (Nat.mul_assoc k.natAbs k.natAbs a.normSq)))))))

private theorem dot_mul_self (a b : Quad4) :
    Eq ((a.mul b).dot (a.mul b)) ((a.dot a).mul (b.dot b)) :=
  let v := bindQuad a (bindQuad b (fun _ => Int.zero))
  let α := variables Nat.zero
  let β := variables Nat.zero.succ.succ.succ.succ
  let product := α.mul β
  Expr.certify v (product.dot product) ((α.dot α).mul (β.dot β)) Eq.refl

theorem normSq_mul (a b : Quad4) : Eq (a.mul b).normSq (a.normSq.mul b.normSq) :=
  Int.ofNat_inj.mp ((normSq_cast (a.mul b)).trans
    ((dot_mul_self a b).trans (Eq.map₂ Int.mul (normSq_cast a).symm (normSq_cast b).symm)))

end Quad4

theorem triad_span (a b : Quad4) :
    Eq (triad b a b) ((Quad4.scale (Int.two.mul (a.dot b)) b).add
      (Quad4.scale (b.dot b).neg a)) :=
  let v := bindQuad a (bindQuad b (fun _ => Int.zero))
  let α := variables Nat.zero
  let β := variables Nat.zero.succ.succ.succ.succ
  let product := (β.mul α.conj).mul β
  let ab := (Expr.const Int.two).mul (α.dot β)
  let bb := (β.dot β).neg
  Quad4.ext
    (Expr.certify v product.w ((ab.mul β.w).add (bb.mul α.w)) Eq.refl)
    (Expr.certify v product.x ((ab.mul β.x).add (bb.mul α.x)) Eq.refl)
    (Expr.certify v product.y ((ab.mul β.y).add (bb.mul α.y)) Eq.refl)
    (Expr.certify v product.z ((ab.mul β.z).add (bb.mul α.z)) Eq.refl)


private theorem dot_add_right (a b c : Quad4) : Eq (a.dot (b.add c)) ((a.dot b).add (a.dot c)) :=
  let distribute := fun (x y z u v w : Int) =>
    (Eq.map₂ Int.add (Int.mul_add x y z) (Int.mul_add u v w)).trans
      (Int.add_add_add_comm (x.mul y) (x.mul z) (u.mul v) (u.mul w))
  (Eq.map₂ Int.add (distribute a.w b.w c.w a.x b.x c.x)
    (distribute a.y b.y c.y a.z b.z c.z)).trans
    (Int.add_add_add_comm ((a.w.mul b.w).add (a.x.mul b.x)) ((a.w.mul c.w).add (a.x.mul c.x))
      ((a.y.mul b.y).add (a.z.mul b.z)) ((a.y.mul c.y).add (a.z.mul c.z)))

theorem dot_triad_left (a b : Quad4) :
    Eq (a.dot (triad b a b)) ((Int.two.mul (Int.square (a.dot b))).sub ((b.dot b).mul (a.dot a))) :=
  (congrArg a.dot (triad_span a b)).trans
    ((dot_add_right a _ _).trans
      (Eq.map₂ Int.add
        ((Quad4.dot_scale_right _ a b).trans (Int.mul_assoc Int.two (a.dot b) (a.dot b)))
        ((Quad4.dot_scale_right _ a a).trans (Int.neg_mul (b.dot b) (a.dot a)))))

theorem dot_triad_middle (a b : Quad4) : Eq (b.dot (triad b a b)) ((b.dot b).mul (a.dot b)) :=
  let v := Expr.bind (b.dot b) (Expr.bind (a.dot b) (fun _ => Int.zero))
  let B := Expr.var Nat.zero
  let p := Expr.var Nat.zero.succ
  have numerator := Expr.certify v
    ((((Expr.const Int.two).mul p).mul B).add (B.neg.mul p)) (B.mul p) Eq.refl
  (congrArg b.dot (triad_span a b)).trans
    ((dot_add_right b _ _).trans
      ((Eq.map₂ Int.add (Quad4.dot_scale_right _ b b)
        ((Quad4.dot_scale_right _ b a).trans (congrArg (b.dot b).neg.mul (b.dot_comm a)))).trans
        numerator))

theorem normSq_triad (a b : Quad4) :
    Eq (triad b a b).normSq ((a.normSq.mul b.normSq).mul b.normSq) :=
  ((b.mul a.conj).normSq_mul b).trans
    (congrArg (fun n : Nat => n.mul b.normSq)
      ((b.normSq_mul a.conj).trans
        ((congrArg b.normSq.mul a.normSq_conj).trans (Nat.mul_comm b.normSq a.normSq))))

def gramNumerator (A B C p q r : Int) : Int :=
  (((A.mul B).mul C).add (Int.two.mul ((p.mul q).mul r))).sub
    (((Int.square p).mul C).add ((Int.square q).mul A) |>.add ((Int.square r).mul B))

private def gramExpr (A B C p q r : Expr) : Expr :=
  (((A.mul B).mul C).add ((Expr.const Int.two).mul ((p.mul q).mul r))).sub
    (((p.sq.mul C).add (q.sq.mul A)).add (r.sq.mul B))

private def detMinorExpr (a b c d e f g h i : Expr) : Expr :=
  ((a.mul ((e.mul i).sub (f.mul h))).sub (b.mul ((d.mul i).sub (f.mul g)))).add
    (c.mul ((d.mul h).sub (e.mul g)))

set_option maxRecDepth 2048 in
/-- Cauchy–Binet for three rows in four columns, with the four maximal minors. -/
theorem gram_squares_nonneg (a b c : Quad4) :
    Int.NonNeg (gramNumerator (a.dot a) (b.dot b) (c.dot c) (a.dot b) (b.dot c) (c.dot a)) :=
  let v := bindQuad a (bindQuad b (bindQuad c (fun _ => Int.zero)))
  let α := variables Nat.zero
  let β := variables Nat.zero.succ.succ.succ.succ
  let γ := variables Nat.zero.succ.succ.succ.succ.succ.succ.succ.succ
  let m := detMinorExpr α.w α.x α.y β.w β.x β.y γ.w γ.x γ.y
  let n := detMinorExpr α.w α.x α.z β.w β.x β.z γ.w γ.x γ.z
  let o := detMinorExpr α.w α.y α.z β.w β.y β.z γ.w γ.y γ.z
  let p := detMinorExpr α.x α.y α.z β.x β.y β.z γ.x γ.y γ.z
  have sums := Expr.certify v (gramExpr (α.dot α) (β.dot β) (γ.dot γ)
    (α.dot β) (β.dot γ) (γ.dot α)) ((m.sq.add n.sq).add (o.sq.add p.sq)) Eq.refl
  let square := fun (x : Int) => x.natAbs.mul x.natAbs
  let cast := fun (x y : Int) => Eq.map₂ Int.add (Int.natAbs_mul_self (a := x))
    (Int.natAbs_mul_self (a := y))
  have squares := Eq.map₂ Int.add (cast (m.eval v) (n.eval v)) (cast (o.eval v) (p.eval v))
  Eq.subst Int.NonNeg (squares.trans sums.symm)
    (Int.NonNeg.mk (((square (m.eval v)).add (square (n.eval v))).add
      ((square (o.eval v)).add (square (p.eval v)))))

theorem gram_triad_vanishes (A B p : Int) :
    Eq (gramNumerator A B ((A.mul B).mul B) p (B.mul p)
      ((Int.two.mul (Int.square p)).sub (B.mul A))) Int.zero :=
  let v := Expr.bind A (Expr.bind B (Expr.bind p (fun _ => Int.zero)))
  let a := Expr.var Nat.zero
  let b := Expr.var Nat.zero.succ
  let u := Expr.var Nat.zero.succ.succ
  let two := Expr.const Int.two
  Expr.certify v (gramExpr a b ((a.mul b).mul b) u (b.mul u)
    ((two.mul u.sq).sub (b.mul a))) (Expr.const Int.zero) Eq.refl

end Omega.Geometry.BargmannGram

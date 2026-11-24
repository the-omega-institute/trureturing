/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Harmonic.HurwitzFreeGroup.ReducedDifference
public import OmegaMath.Geometry.Cayley3D.Adjoint

/-!
Omega original.

The normalized Cayley adjoint distinguishes reduced Hurwitz words by its
action on the first two coordinate axes.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.FreeGroup

open Geometry.Cayley3D (Ad adjointNum adjointDen_eq adjointQuaternion adjoint_pure)
open Quaternion.Polynomial (Expr Values)

def axisX : Vec3 := ⟨Int.one, Int.zero, Int.zero⟩
def axisY : Vec3 := ⟨Int.zero, Int.one, Int.zero⟩

private theorem denominator_of_int (q : Quaternion) (hq : q.Nonzero) (v : Vec3) :
    Eq (Ad q (RatVec3.ofInt v)).den q.normSq :=
  (congrArg Nat.succ (Nat.zero_add q.normSq.pred)).trans (adjointDen_eq q hq)

private theorem evalQuat_nonzero (w : Word) : (evalQuat w).Nonzero :=
  have five_ne_zero : Not (Eq five Nat.zero) := Nat.succ_ne_zero five.pred
  have powers : ∀ n : Nat, Not (Eq (powFive n) Nat.zero) :=
    Nat.rec (motive := fun n => Not (Eq (powFive n) Nat.zero))
      (Nat.succ_ne_zero Nat.zero)
      (fun _ ih h => (Nat.mul_eq_zero.mp h).elim five_ne_zero ih)
  Quaternion.nonzero_of_normSq_ne_zero (fun h => powers w.length ((reduced_word_normSq w).symm.trans h))

private theorem pure_scale (k : Int) (v : Vec3) :
    Eq (Vec3.scale k v).pure (Quaternion.scale k v.pure) :=
  Quaternion.ext (Int.mul_zero k).symm Eq.refl Eq.refl Eq.refl

private theorem adjoint_cross (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero) (v : Vec3)
    (same : RatVec3.Equiv (Ad p (RatVec3.ofInt v)) (Ad q (RatVec3.ofInt v))) :
    Eq (Quaternion.scale (Int.ofNat q.normSq) (adjointQuaternion p v))
      (Quaternion.scale (Int.ofNat p.normSq) (adjointQuaternion q v)) :=
  let move := fun r t : Quaternion => fun den : Eq (Ad t (RatVec3.ofInt v)).den t.normSq =>
    let n := Int.ofNat t.normSq
    (congrArg (fun d => (Vec3.scale (Int.ofNat d) (adjointNum r v)).pure) den).trans
      ((pure_scale n (adjointNum r v)).trans (congrArg (Quaternion.scale n) (adjoint_pure r v)))
  (move p q (denominator_of_int q hq v)).symm.trans
    ((congrArg Vec3.pure same).trans (move q p (denominator_of_int p hp v)))

private theorem sandwich_scale (a b c : Quaternion) (k : Int) :
    Eq ((a.mul (Quaternion.scale k b)).mul c) (Quaternion.scale k ((a.mul b).mul c)) :=
  (congrArg (fun t : Quaternion => t.mul c) (Quaternion.scale_mul_right k a b)).trans
    (Quaternion.scale_mul_left k (a.mul b) c)

private theorem sandwich_left (p q : Quaternion) (v : Vec3) :
    Eq ((p.conj.mul (adjointQuaternion p v)).mul q)
      (Quaternion.scale (Int.ofNat p.normSq) (v.pure.mul (p.conj.mul q))) :=
  let V := v.pure
  let n := Int.ofNat p.normSq
  have left : Eq (p.conj.mul (p.mul V)) (Quaternion.scale n V) :=
    (Quaternion.mul_assoc p.conj p V).symm.trans
      ((congrArg (fun t : Quaternion => t.mul V) (Quaternion.conj_mul_eq_normSq p)).trans
        (Quaternion.scalar_mul n V))
  have first : Eq (p.conj.mul (adjointQuaternion p v)) (Quaternion.scale n (V.mul p.conj)) :=
    (Quaternion.mul_assoc p.conj (p.mul V) p.conj).symm.trans
      ((congrArg (fun t : Quaternion => t.mul p.conj) left).trans
        (Quaternion.scale_mul_left n V p.conj))
  (congrArg (fun t : Quaternion => t.mul q) first).trans
    ((Quaternion.scale_mul_left n (V.mul p.conj) q).trans
      (congrArg (Quaternion.scale n) (Quaternion.mul_assoc V p.conj q)))

private theorem sandwich_right (p q : Quaternion) (v : Vec3) :
    Eq ((p.conj.mul (adjointQuaternion q v)).mul q)
      (Quaternion.scale (Int.ofNat q.normSq) ((p.conj.mul q).mul v.pure)) :=
  let V := v.pure
  let n := Int.ofNat q.normSq
  have right : Eq ((adjointQuaternion q v).mul q) (Quaternion.scale n (q.mul V)) :=
    (Quaternion.mul_assoc (q.mul V) q.conj q).trans
      ((congrArg (q.mul V).mul (Quaternion.conj_mul_eq_normSq q)).trans
        (Quaternion.mul_scalar n (q.mul V)))
  (Quaternion.mul_assoc p.conj (adjointQuaternion q v) q).trans
    ((congrArg p.conj.mul right).trans
      ((Quaternion.scale_mul_right n p.conj (q.mul V)).trans
        (congrArg (Quaternion.scale n) (Quaternion.mul_assoc p.conj q V).symm)))

private theorem relative_commutes (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero) (v : Vec3)
    (same : RatVec3.Equiv (Ad p (RatVec3.ofInt v)) (Ad q (RatVec3.ofInt v))) :
    Eq ((p.conj.mul q).mul v.pure) (v.pure.mul (p.conj.mul q)) :=
  let n := Int.ofNat p.normSq
  let m := Int.ofNat q.normSq
  let left := v.pure.mul (p.conj.mul q)
  let right := (p.conj.mul q).mul v.pure
  have equate : Eq (Quaternion.scale m (Quaternion.scale n left))
      (Quaternion.scale n (Quaternion.scale m right)) :=
    have unfolded := congrArg (fun x : Quaternion => (p.conj.mul x).mul q)
      (adjoint_cross p q hp hq v same)
    have l := (sandwich_scale p.conj (adjointQuaternion p v) q m).trans
      (congrArg (Quaternion.scale m) (sandwich_left p q v))
    have r := (sandwich_scale p.conj (adjointQuaternion q v) q n).trans
      (congrArg (Quaternion.scale n) (sandwich_right p q v))
    l.symm.trans (unfolded.trans r)
  have scale_eq : Eq (Quaternion.scale (n.mul m) right) (Quaternion.scale (n.mul m) left) :=
    (Quaternion.scale_mul right n m).symm.trans
      (equate.symm.trans ((Quaternion.scale_mul left m n).trans
        (congrArg (fun k => Quaternion.scale k left) (Int.mul_comm m n))))
  let ne := fun (r : Quaternion) (hr : r.Nonzero) (h : Eq (Int.ofNat r.normSq) Int.zero) =>
    Quaternion.normSq_ne_zero hr (Int.ofNat_inj.mp h)
  Quaternion.scale_cancel (Int.mul_ne_zero (ne p hp) (ne q hq)) scale_eq

private theorem scalar_of_commutes (q : Quaternion)
    (commX : Eq (q.mul axisX.pure) (axisX.pure.mul q))
    (commY : Eq (q.mul axisY.pure) (axisY.pure.mul q)) : Eq q (Quaternion.scalar q.w) :=
  let P := Quaternion.Polynomial.Coordinates.variables Nat.zero
  let X : Quaternion.Polynomial.Coordinates := ⟨.zero, .one, .zero, .zero⟩
  let Y : Quaternion.Polynomial.Coordinates := ⟨.zero, .zero, .one, .zero⟩
  let values := Values.cons q.w (.cons q.x (.cons q.y (.cons q.z .nil)))
  let two := Expr.one.add .one
  let cancel := fun (t : Int) (h : Eq (Int.two.mul t) Int.zero) =>
    (Int.mul_eq_zero.mp h).elim
      (fun h => False.elim (Int.ofNat_succ_ne_zero Nat.one h)) (fun h => h)
  have x := (((P.mul Y).z.sub (Y.mul P).z).sound (two.mul P.x) values Eq.refl).symm.trans
    (Int.sub_eq_zero.mpr (congrArg Quaternion.z commY))
  have y := (((X.mul P).z.sub (P.mul X).z).sound (two.mul P.y) values Eq.refl).symm.trans
    (Int.sub_eq_zero.mpr (congrArg Quaternion.z commX.symm))
  have z := (((P.mul X).y.sub (X.mul P).y).sound (two.mul P.z) values Eq.refl).symm.trans
    (Int.sub_eq_zero.mpr (congrArg Quaternion.y commX))
  Quaternion.ext Eq.refl (cancel q.x x) (cancel q.y y) (cancel q.z z)

/-- Agreement on two coordinate axes identifies the reduced word. -/
theorem reduced_words_adjoint_injective (u v : Word) (hu : IsReduced u) (hv : IsReduced v)
    (sameX : RatVec3.Equiv (Ad (evalQuat u) (RatVec3.ofInt axisX))
      (Ad (evalQuat v) (RatVec3.ofInt axisX)))
    (sameY : RatVec3.Equiv (Ad (evalQuat u) (RatVec3.ofInt axisY))
      (Ad (evalQuat v) (RatVec3.ofInt axisY))) :
    Eq u v :=
  let p := evalQuat u
  let q := evalQuat v
  have hp := evalQuat_nonzero u
  have hq := evalQuat_nonzero v
  reduced_words_eq_of_relative_scalar u v hu hv (p.conj.mul q).w
    (scalar_of_commutes (p.conj.mul q) (relative_commutes p q hp hq axisX sameX)
      (relative_commutes p q hp hq axisY sameY))

private theorem ad_one_int (v : Vec3) :
    Eq (Ad Quaternion.one (RatVec3.ofInt v)) (RatVec3.ofInt v) :=
  have left := (Quaternion.scalar_mul Int.one v.pure).trans (Quaternion.scale_one v.pure)
  have right := (Quaternion.mul_scalar Int.one v.pure).trans (Quaternion.scale_one v.pure)
  have product : Eq (adjointQuaternion Quaternion.one v) v.pure :=
    (congrArg (fun q : Quaternion => q.mul Quaternion.one) left).trans right
  RatVec3.eq_of_num_den (congrArg Vec3.imaginary product) Eq.refl

/-- The Cayley adjoint representation has trivial kernel on reduced Hurwitz words. -/
theorem reduced_word_adjoint_faithful (w : Word) (hr : IsReduced w)
    (fixedX : RatVec3.Equiv (Ad (evalQuat w) (RatVec3.ofInt axisX)) (RatVec3.ofInt axisX))
    (fixedY : RatVec3.Equiv (Ad (evalQuat w) (RatVec3.ofInt axisY)) (RatVec3.ofInt axisY)) :
    Eq w .nil :=
  have fix := fun (v : Vec3) (h : RatVec3.Equiv
      (Ad (evalQuat w) (RatVec3.ofInt v)) (RatVec3.ofInt v)) =>
    Eq.subst (fun r => RatVec3.Equiv (Ad (evalQuat w) (RatVec3.ofInt v)) r)
      (ad_one_int v).symm h
  reduced_words_adjoint_injective w .nil hr True.intro (fix axisX fixedX) (fix axisY fixedY)

end Omega.Hurwitz.FreeGroup

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.Quaternion
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Three-dimensional integer and rational vectors, with the exact quaternion adjoint action.
-/

noncomputable section

@[expose] public section

namespace Omega

structure Vec3 where
  x : Int
  y : Int
  z : Int

namespace Vec3

def dot3 (a b : Vec3) : Int := (a.x.mul b.x).add ((a.y.mul b.y).add (a.z.mul b.z))

def scale (k : Int) (a : Vec3) : Vec3 := ⟨k.mul a.x, k.mul a.y, k.mul a.z⟩

def pure (v : Vec3) : Quaternion := ⟨Int.zero, v.x, v.y, v.z⟩

def imaginary (q : Quaternion) : Vec3 := ⟨q.x, q.y, q.z⟩

theorem ext {a b : Vec3} (hx : Eq a.x b.x) (hy : Eq a.y b.y) (hz : Eq a.z b.z) : Eq a b :=
  (congrArg (fun x => Vec3.mk x a.y a.z) hx).trans (Eq.map₂ (Vec3.mk b.x) hy hz)

theorem scale_one (a : Vec3) : Eq (scale Int.one a) a :=
  ext (Int.one_mul a.x) (Int.one_mul a.y) (Int.one_mul a.z)

theorem scale_mul (a : Vec3) (k l : Int) : Eq (scale k (scale l a)) (scale (k.mul l) a) :=
  ext (Int.mul_assoc k l a.x).symm (Int.mul_assoc k l a.y).symm (Int.mul_assoc k l a.z).symm

theorem dot_pure (a b : Vec3) : Eq (a.pure.dot b.pure) (dot3 a b) :=
  congrArg (fun t : Int => t.add ((a.y.mul b.y).add (a.z.mul b.z))) (Int.zero_add (a.x.mul b.x))

end Vec3

/-- Three exact rational coordinates with a shared positive denominator. -/
structure RatVec3 where
  num : Vec3
  denPred : Nat

namespace RatVec3

def den (v : RatVec3) : Nat := v.denPred.succ

def ofInt (v : Vec3) : RatVec3 := ⟨v, Nat.zero⟩

def Equiv (u v : RatVec3) : Prop :=
  Eq (Vec3.scale (Int.ofNat v.den) u.num) (Vec3.scale (Int.ofNat u.den) v.num)

def dot3 (u v : RatVec3) : IntRatio := IntRatio.value (u.num.dot3 v.num) (u.den.mul v.den)

theorem eq_of_num_den {u v : RatVec3} (hn : Eq u.num v.num) (hd : Eq u.den v.den) : Eq u v :=
  Eq.map₂ RatVec3.mk hn (Nat.succ.inj hd)

theorem equiv_of_eq {u v : RatVec3} (h : Eq u v) : Equiv u v :=
  Eq.subst (Equiv u) h Eq.refl

theorem equiv_scale (u v : RatVec3) (k : Nat)
    (hn : Eq u.num (Vec3.scale (Int.ofNat k) v.num)) (hd : Eq u.den (v.den.mul k)) :
    Equiv u v :=
  (congrArg (Vec3.scale (Int.ofNat v.den)) hn).trans
    ((Vec3.scale_mul v.num (Int.ofNat v.den) (Int.ofNat k)).trans
      (congrArg (fun n => Vec3.scale (Int.ofNat n) v.num) hd.symm))

theorem dot3_ofInt (u v : Vec3) : Eq (dot3 (ofInt u) (ofInt v)) (IntRatio.ofInt (u.dot3 v)) :=
  Eq.refl

end RatVec3

namespace Geometry.Cayley3D

open Quaternion.Polynomial

def adjointQuaternion (p : Quaternion) (v : Vec3) : Quaternion :=
  (p.mul v.pure).mul p.conj

def adjointNum (p : Quaternion) (v : Vec3) : Vec3 := Vec3.imaginary (adjointQuaternion p v)

/-- The fallback denominator at the zero quaternion is one. -/
def adjointDen (p : Quaternion) : Nat := p.normSq.pred.succ

theorem adjointDen_eq (p : Quaternion) (hp : p.Nonzero) : Eq (adjointDen p) p.normSq :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → Eq n.pred.succ n)
    (fun h => False.elim (h Eq.refl)) (fun _ _ _ => Eq.refl) p.normSq) (Quaternion.normSq_ne_zero hp)

/-- The rational adjoint rotation for a nonzero quaternion, acting on homogeneous vectors. -/
def Ad (p : Quaternion) (v : RatVec3) : RatVec3 :=
  ⟨adjointNum p v.num, IntRatio.mulDenPred p.normSq.pred v.denPred⟩

theorem adjoint_pure (p : Quaternion) (v : Vec3) :
    Eq (adjointNum p v).pure (adjointQuaternion p v) :=
  let i := Nat.zero
  let j := i.succ.succ.succ.succ
  let P := Coordinates.variables i
  let V : Coordinates := ⟨.zero, .var j, .var j.succ, .var j.succ.succ⟩
  let values := Values.cons p.w (.cons p.x (.cons p.y (.cons p.z
    (.cons v.x (.cons v.y (.cons v.z .nil))))))
  Quaternion.ext (((P.mul V).mul P.conj).w.sound .zero values Eq.refl).symm
    Eq.refl Eq.refl Eq.refl

theorem adjointNum_dot (p : Quaternion) (u v : Vec3) :
    Eq ((adjointNum p u).dot3 (adjointNum p v))
      ((u.dot3 v).mul (Int.ofNat (p.normSq.mul p.normSq))) :=
  let n := Int.ofNat p.normSq
  let d := u.dot3 v
  have t := Quaternion.dot_mul_right p.conj (p.mul u.pure) (p.mul v.pure)
  have s := Quaternion.dot_mul_left p u.pure v.pure
  (Vec3.dot_pure (adjointNum p u) (adjointNum p v)).symm.trans
    ((Eq.map₂ Quaternion.dot (adjoint_pure p u) (adjoint_pure p v)).trans
      (t.trans ((Eq.map₂ Int.mul (Quaternion.dot_conj p p) s).trans
        ((Eq.map₂ Int.mul p.normSq_cast.symm
          (Eq.map₂ Int.mul p.normSq_cast.symm (Vec3.dot_pure u v))).trans
          ((Int.mul_assoc n n d).symm.trans (Int.mul_comm (n.mul n) d))))))

theorem ad_dot (p : Quaternion) (hp : p.Nonzero) (u v : RatVec3) :
    IntRatio.Equivalent ((Ad p u).dot3 (Ad p v)) (u.dot3 v) :=
  let n := p.normSq
  let d := u.den
  let e := v.den
  have den : Eq ((Ad p u).den.mul (Ad p v).den) ((d.mul e).mul (n.mul n)) :=
    (Eq.map₂ Nat.mul (congrArg (fun k : Nat => k.mul d) (adjointDen_eq p hp))
      (congrArg (fun k : Nat => k.mul e) (adjointDen_eq p hp))).trans
      ((Eq.map₂ Nat.mul (Nat.mul_comm n d) (Nat.mul_comm n e)).trans
        ((Nat.mul_assoc d n (e.mul n)).trans
          ((congrArg d.mul ((Nat.mul_assoc n e n).symm.trans
            ((congrArg (fun k : Nat => k.mul n) (Nat.mul_comm n e)).trans
              (Nat.mul_assoc e n n)))).trans (Nat.mul_assoc d e (n.mul n)).symm)))
  have h := Quaternion.normSq_ne_zero hp
  Eq.subst (fun r => IntRatio.Equivalent r (u.dot3 v))
    (Eq.map₂ IntRatio.value (adjointNum_dot p u.num v.num) den).symm
    (IntRatio.value_scale_of_ne_zero (u.num.dot3 v.num) (d.mul e) (n.mul n)
      (fun e => (Nat.mul_eq_zero.mp e).elim h h))

theorem adjointNum_scale (p : Quaternion) (k : Int) (v : Vec3) :
    Eq (adjointNum (Quaternion.scale k p) v)
      (Vec3.scale (Int.square k) (adjointNum p v)) :=
  have t : Eq (adjointQuaternion (Quaternion.scale k p) v)
      (Quaternion.scale (Int.square k) (adjointQuaternion p v)) :=
    (Eq.map₂ Quaternion.mul (Quaternion.scale_mul_left k p v.pure) (Quaternion.conj_scale k p)).trans
      ((Quaternion.scale_mul_left k (p.mul v.pure) (Quaternion.scale k p.conj)).trans
        ((congrArg (Quaternion.scale k) (Quaternion.scale_mul_right k (p.mul v.pure) p.conj)).trans
          (Quaternion.scale_mul (adjointQuaternion p v) k k)))
  congrArg Vec3.imaginary t

theorem ad_scale (p : Quaternion) (hp : p.Nonzero) (k : Int) (hk : Not (Eq k Int.zero))
    (v : RatVec3) : RatVec3.Equiv (Ad (Quaternion.scale k p) v) (Ad p v) :=
  let d := k.natAbs.mul k.natAbs
  let q := Quaternion.scale k p
  have hq := Quaternion.nonzero_scale hp hk
  have den : Eq (Ad q v).den ((Ad p v).den.mul d) :=
    (congrArg (fun n : Nat => n.mul v.den) ((adjointDen_eq q hq).trans
      (Quaternion.normSq_scale k p))).trans
      ((Nat.mul_right_comm p.normSq d v.den).trans
        (congrArg (fun n : Nat => (n.mul v.den).mul d) (adjointDen_eq p hp).symm))
  RatVec3.equiv_scale (Ad q v) (Ad p v) d
    ((adjointNum_scale p k v.num).trans
      (congrArg (fun s => Vec3.scale s (adjointNum p v.num)) Int.natAbs_mul_self.symm)) den

theorem adjointNum_hom (p q : Quaternion) (v : Vec3) :
    Eq (adjointNum (p.mul q) v) (adjointNum p (adjointNum q v)) :=
  have t := Quaternion.mul_assoc p q v.pure
  have h : Eq (adjointQuaternion (p.mul q) v) (adjointQuaternion p (adjointNum q v)) :=
    (Eq.map₂ Quaternion.mul t (Quaternion.conj_mul p q)).trans
      ((Quaternion.mul_assoc p (q.mul v.pure) (q.conj.mul p.conj)).trans
        ((congrArg p.mul (Quaternion.mul_assoc (q.mul v.pure) q.conj p.conj).symm).trans
          ((Quaternion.mul_assoc p (adjointQuaternion q v) p.conj).symm.trans
            (congrArg (fun a : Quaternion => (p.mul a).mul p.conj) (adjoint_pure q v).symm))))
  congrArg Vec3.imaginary h

theorem ad_hom_eq (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero) (v : RatVec3) :
    Eq (Ad (p.mul q) v) (Ad p (Ad q v)) :=
  have h := Quaternion.nonzero_mul hp hq
  have t : Eq (Ad (p.mul q) v).den (Ad p (Ad q v)).den :=
    (congrArg (fun n : Nat => n.mul v.den)
      ((adjointDen_eq (p.mul q) h).trans (Quaternion.normSq_mul p q))).trans
      ((Nat.mul_assoc p.normSq q.normSq v.den).trans
        (Eq.map₂ Nat.mul (adjointDen_eq p hp).symm
          (congrArg (fun n : Nat => n.mul v.den) (adjointDen_eq q hq).symm)))
  RatVec3.eq_of_num_den (adjointNum_hom p q v.num) t

theorem ad_hom (p q : Quaternion) (hp : p.Nonzero) (hq : q.Nonzero) (v : RatVec3) :
    RatVec3.Equiv (Ad (p.mul q) v) (Ad p (Ad q v)) :=
  RatVec3.equiv_of_eq (ad_hom_eq p q hp hq v)

end Geometry.Cayley3D
end Omega

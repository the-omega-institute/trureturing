/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.Quaternion

/-!
Omega original.

The ternion heap on nonzero integer quaternions modulo signed rational proportionality.
-/

noncomputable section

@[expose] public section

namespace Omega.Ternion

open Quaternion

/-- Two nonzero integer quaternions span the same rational ray if they admit a
common nonzero integer representative. The two scales may have either sign. -/
def RayEquiv (a b : Quaternion) : Prop :=
  And a.Nonzero (And b.Nonzero (Exists fun k : Int => Exists fun l : Int =>
    And (Not (Eq k Int.zero)) (And (Not (Eq l Int.zero)) (Eq (scale k a) (scale l b)))))

theorem int_one_ne_zero : Not (Eq Int.one Int.zero) := Int.ofNat_succ_ne_zero Nat.zero

theorem RayEquiv.intro {a b : Quaternion} (ha : a.Nonzero) (hb : b.Nonzero)
    (k l : Int) (hk : Not (Eq k Int.zero)) (hl : Not (Eq l Int.zero))
    (h : Eq (scale k a) (scale l b)) : RayEquiv a b :=
  And.intro ha (And.intro hb (Exists.intro k (Exists.intro l (And.intro hk (And.intro hl h)))))

theorem RayEquiv.refl {a : Quaternion} (ha : a.Nonzero) : RayEquiv a a :=
  RayEquiv.intro ha ha Int.one Int.one int_one_ne_zero int_one_ne_zero Eq.refl

theorem RayEquiv.symm {a b : Quaternion} (h : RayEquiv a b) : RayEquiv b a :=
  h.right.right.elim (fun k witness => witness.elim (fun l e =>
    RayEquiv.intro h.right.left h.left l k e.right.left e.left e.right.right.symm))

theorem RayEquiv.trans {a b c : Quaternion} (h : RayEquiv a b) (g : RayEquiv b c) : RayEquiv a c :=
  h.right.right.elim (fun k witness => witness.elim (fun l left =>
    g.right.right.elim (fun m witness => witness.elim (fun n right =>
      have middle := (scale_mul b m l).trans
        ((congrArg (fun t : Int => scale t b) (Int.mul_comm m l)).trans (scale_mul b l m).symm)
      have eq := (scale_mul a m k).symm.trans ((congrArg (scale m) left.right.right).trans
        (middle.trans ((congrArg (scale l) right.right.right).trans (scale_mul c l n))))
      RayEquiv.intro h.left g.right.left (m.mul k) (l.mul n)
        (Int.mul_ne_zero right.left left.left) (Int.mul_ne_zero left.right.left right.right.left) eq))))

theorem ray_scale (a : Quaternion) (ha : a.Nonzero) (k : Int) (hk : Not (Eq k Int.zero)) :
    RayEquiv (scale k a) a :=
  RayEquiv.intro (nonzero_scale ha hk) ha Int.one k int_one_ne_zero hk (scale_one (scale k a))

/-- The integer representative of the projective ternary product. -/
def triad (a b c : Quaternion) : Quaternion := (a.mul b.conj).mul c

theorem triad_closed {a b c : Quaternion} (ha : a.Nonzero) (hb : b.Nonzero) (hc : c.Nonzero) :
    (triad a b c).Nonzero :=
  let h := triad_nonzero ha hb hc
  nonzero_of_normSq_ne_zero (fun e => h.right (h.left.symm.trans e))

/-- A data certificate that a norm is a successor in the strict prelude. -/
inductive PositiveNorm : Nat → Type where
  | succ (n : Nat) : PositiveNorm n.succ

/-- A nonzero representative of a projective ternion. Projective equality is a relation. -/
structure ProjTernion where
  rep : Quaternion
  positive : PositiveNorm rep.normSq

namespace ProjTernion

def ofNonzero (q : Quaternion) (h : q.Nonzero) : ProjTernion :=
  ⟨q, (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → PositiveNorm n)
    (fun h => False.elim (h Eq.refl)) (fun n _ _ => PositiveNorm.succ n) q.normSq)
      (normSq_ne_zero h)⟩

theorem nonzero (p : ProjTernion) : p.rep.Nonzero :=
  nonzero_of_normSq_ne_zero
    (PositiveNorm.rec (motive := fun n _ => Not (Eq n Nat.zero)) Nat.succ_ne_zero p.positive)

def Equivalent (a b : ProjTernion) : Prop := RayEquiv a.rep b.rep

def triad (a b c : ProjTernion) : ProjTernion :=
  ofNonzero (Ternion.triad a.rep b.rep c.rep) (triad_closed a.nonzero b.nonzero c.nonzero)

end ProjTernion

theorem triad_scale (a b c : Quaternion) (i j k : Int) :
    Eq (triad (scale i a) (scale j b) (scale k c)) (scale (k.mul (i.mul j)) (triad a b c)) :=
  have left : Eq ((scale i a).mul (scale j b).conj) (scale (i.mul j) (a.mul b.conj)) :=
    (congrArg (scale i a).mul (conj_scale j b)).trans
      ((scale_mul_left i a (scale j b.conj)).trans
        ((congrArg (scale i) (scale_mul_right j a b.conj)).trans (scale_mul (a.mul b.conj) i j)))
  (congrArg (fun p : Quaternion => p.mul (scale k c)) left).trans
    ((scale_mul_right k (scale (i.mul j) (a.mul b.conj)) c).trans
      ((congrArg (scale k) (scale_mul_left (i.mul j) (a.mul b.conj) c)).trans
        (scale_mul (triad a b c) k (i.mul j))))

theorem triad_congr {a b c d e f : Quaternion}
    (ab : RayEquiv a b) (cd : RayEquiv c d) (ef : RayEquiv e f) :
    RayEquiv (triad a c e) (triad b d f) :=
  ab.right.right.elim (fun i witness => witness.elim (fun j left =>
    cd.right.right.elim (fun k witness => witness.elim (fun l middle =>
      ef.right.right.elim (fun m witness => witness.elim (fun n right =>
        have eq := Eq.map₂ (fun p q => triad p q (scale m e))
          left.right.right middle.right.right
        have all := eq.trans (congrArg (triad (scale j b) (scale l d)) right.right.right)
        RayEquiv.intro (triad_closed ab.left cd.left ef.left)
          (triad_closed ab.right.left cd.right.left ef.right.left)
          (m.mul (i.mul k)) (n.mul (j.mul l))
          (Int.mul_ne_zero right.left (Int.mul_ne_zero left.left middle.left))
          (Int.mul_ne_zero right.right.left (Int.mul_ne_zero left.right.left middle.right.left))
          ((triad_scale a c e i k m).symm.trans (all.trans (triad_scale b d f j l n)))))))))

theorem triad_left_absorption (x z : Quaternion) (hx : x.Nonzero) (hz : z.Nonzero) :
    RayEquiv (triad x x z) z :=
  let d := Int.ofNat x.normSq
  have h := (congrArg (fun a : Quaternion => a.mul z) (mul_conj_eq_normSq x)).trans (scalar_mul d z)
  have hd : Not (Eq d Int.zero) := fun e => normSq_ne_zero hx (Int.ofNat_inj.mp e)
  Eq.subst (fun a => RayEquiv a z) h.symm (ray_scale z hz d hd)

theorem triad_right_absorption (x z : Quaternion) (hx : x.Nonzero) (hz : z.Nonzero) :
    RayEquiv (triad x z z) x :=
  let d := Int.ofNat z.normSq
  have h := (mul_assoc x z.conj z).trans
    ((congrArg x.mul (conj_mul_eq_normSq z)).trans (mul_scalar d x))
  have hd : Not (Eq d Int.zero) := fun e => normSq_ne_zero hz (Int.ofNat_inj.mp e)
  Eq.subst (fun a => RayEquiv a x) h.symm (ray_scale x hx d hd)

theorem triad_assoc_eq (x y z u v : Quaternion) :
    Eq (triad (triad x y z) u v) (triad x y (triad z u v)) :=
  (mul_assoc ((x.mul y.conj).mul z) u.conj v).trans
    (mul_assoc (x.mul y.conj) z (u.conj.mul v) |>.trans
      (congrArg (x.mul y.conj).mul (mul_assoc z u.conj v).symm))

theorem triad_assoc (x y z u v : Quaternion) (hx : x.Nonzero) (hy : y.Nonzero)
    (hz : z.Nonzero) (hu : u.Nonzero) (hv : v.Nonzero) :
    RayEquiv (triad (triad x y z) u v) (triad x y (triad z u v)) :=
  Eq.subst (RayEquiv (triad (triad x y z) u v)) (triad_assoc_eq x y z u v)
    (RayEquiv.refl (triad_closed (triad_closed hx hy hz) hu hv))

def p0 : Quaternion := Quaternion.one

def pHalf : Quaternion := ⟨Int.one, Int.one, Int.zero, Int.zero⟩

def qHalf : Quaternion := ⟨Int.one, Int.zero, Int.one, Int.zero⟩

theorem triad_noncommutative :
    Not (RayEquiv (triad pHalf p0 qHalf) (triad qHalf p0 pHalf)) :=
  fun h => h.right.right.elim (fun k witness => witness.elim (fun l e =>
    have same : Eq k l :=
      (Int.mul_one k).symm.trans ((congrArg Quaternion.w e.right.right).trans (Int.mul_one l))
    have opposite : Eq k l.neg :=
      (Int.mul_one k).symm.trans ((congrArg Quaternion.z e.right.right).trans
        ((Int.mul_neg l Int.one).trans (congrArg Int.neg (Int.mul_one l))))
    have sign : Eq l l.neg := same.symm.trans opposite
    have zero : Eq l Int.zero :=
      (Int.rec (motive := fun n => Eq n n.neg → Eq n Int.zero)
        (fun n => Nat.rec (motive := fun n => Eq (Int.ofNat n) (Int.ofNat n).neg →
          Eq (Int.ofNat n) Int.zero) (fun _ => Eq.refl)
          (fun d _ sign => False.elim (Eq.subst Int.NonNeg sign (Int.NonNeg.mk d.succ))) n)
        (fun d sign => False.elim (Eq.subst Int.NonNeg sign.symm (Int.NonNeg.mk d.succ))) l) sign
    e.right.left zero))

end Omega.Ternion

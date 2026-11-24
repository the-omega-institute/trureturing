/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.Quaternion.Polynomial

/-!
Omega original.

Integer Hamilton quaternions with the positive definite squared norm.
-/

noncomputable section

@[expose] public section

namespace Omega

structure Quaternion where
  w : Int
  x : Int
  y : Int
  z : Int

namespace Quaternion

def zero : Quaternion := ⟨Int.zero, Int.zero, Int.zero, Int.zero⟩

def scalar (s : Int) : Quaternion := ⟨s, Int.zero, Int.zero, Int.zero⟩

def one : Quaternion := scalar Int.one

def scale (k : Int) (a : Quaternion) : Quaternion :=
  ⟨k.mul a.w, k.mul a.x, k.mul a.y, k.mul a.z⟩

def add (a b : Quaternion) : Quaternion :=
  ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

def neg (a : Quaternion) : Quaternion := ⟨a.w.neg, a.x.neg, a.y.neg, a.z.neg⟩

def sub (a b : Quaternion) : Quaternion := a.add b.neg

def conj (a : Quaternion) : Quaternion := ⟨a.w, a.x.neg, a.y.neg, a.z.neg⟩

def mul (a b : Quaternion) : Quaternion :=
  ⟨(((a.w.mul b.w).sub (a.x.mul b.x)).sub (a.y.mul b.y)).sub (a.z.mul b.z),
   (((a.w.mul b.x).add (a.x.mul b.w)).add (a.y.mul b.z)).sub (a.z.mul b.y),
   (((a.w.mul b.y).sub (a.x.mul b.z)).add (a.y.mul b.w)).add (a.z.mul b.x),
   (((a.w.mul b.z).add (a.x.mul b.y)).sub (a.y.mul b.x)).add (a.z.mul b.w)⟩

def dot (a b : Quaternion) : Int :=
  ((a.w.mul b.w).add (a.x.mul b.x)).add ((a.y.mul b.y).add (a.z.mul b.z))

/-- The sum of the four squared coordinates, represented as a natural number. -/
def normSq (a : Quaternion) : Nat :=
  let sq := fun (t : Int) => t.natAbs.mul t.natAbs
  ((sq a.w).add (sq a.x)).add ((sq a.y).add (sq a.z))

def Nonzero (a : Quaternion) : Prop :=
  Not (And (Eq a.w Int.zero) (And (Eq a.x Int.zero) (And (Eq a.y Int.zero) (Eq a.z Int.zero))))

theorem ext {a b : Quaternion} (hw : Eq a.w b.w) (hx : Eq a.x b.x)
    (hy : Eq a.y b.y) (hz : Eq a.z b.z) : Eq a b :=
  (Eq.map₂ (fun w x => Quaternion.mk w x a.y a.z) hw hx).trans
    (Eq.map₂ (Quaternion.mk b.w b.x) hy hz)

theorem conj_conj (a : Quaternion) : Eq a.conj.conj a :=
  ext Eq.refl (Int.neg_neg a.x) (Int.neg_neg a.y) (Int.neg_neg a.z)

theorem normSq_cast (a : Quaternion) : Eq (Int.ofNat a.normSq) (a.dot a) :=
  Eq.map₂ Int.add
    (Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self)
    (Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self)

theorem normSq_eq_zero_iff (a : Quaternion) : Iff (Eq a.normSq Nat.zero) (Eq a zero) :=
  Iff.intro
    (fun h =>
      have pairs := (Int.sum_of_two_squares_eq_zero a.w a.x)
      have other := (Int.sum_of_two_squares_eq_zero a.y a.z)
      have sums := Nat.eq_zero_of_add_eq_zero h
      have wx := pairs.mp ((Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self).symm.trans
        (congrArg Int.ofNat sums.left))
      have yz := other.mp ((Eq.map₂ Int.add Int.natAbs_mul_self Int.natAbs_mul_self).symm.trans
        (congrArg Int.ofNat sums.right))
      ext wx.left wx.right yz.left yz.right)
    (fun h => congrArg normSq h)

theorem nonzero_iff_ne_zero (a : Quaternion) : Iff a.Nonzero (Not (Eq a zero)) :=
  Iff.intro
    (fun h e => h (And.intro (congrArg Quaternion.w e) (And.intro (congrArg Quaternion.x e)
      (And.intro (congrArg Quaternion.y e) (congrArg Quaternion.z e)))))
    (fun h e => h (ext e.left e.right.left e.right.right.left e.right.right.right))

theorem normSq_ne_zero {a : Quaternion} (h : a.Nonzero) : Not (Eq a.normSq Nat.zero) :=
  fun e => (nonzero_iff_ne_zero a).mp h ((normSq_eq_zero_iff a).mp e)

theorem nonzero_of_normSq_ne_zero {a : Quaternion} (h : Not (Eq a.normSq Nat.zero)) : a.Nonzero :=
  (nonzero_iff_ne_zero a).mpr (fun e => h ((normSq_eq_zero_iff a).mpr e))

theorem dot_comm (a b : Quaternion) : Eq (a.dot b) (b.dot a) :=
  Eq.map₂ Int.add (Eq.map₂ Int.add (Int.mul_comm a.w b.w) (Int.mul_comm a.x b.x))
    (Eq.map₂ Int.add (Int.mul_comm a.y b.y) (Int.mul_comm a.z b.z))

theorem normSq_conj (a : Quaternion) : Eq a.conj.normSq a.normSq :=
  let square := fun n : Nat => n.mul n
  Eq.map₂ Nat.add (congrArg (Nat.add (square a.w.natAbs)) (congrArg square (Int.natAbs_neg a.x)))
    (Eq.map₂ Nat.add (congrArg square (Int.natAbs_neg a.y)) (congrArg square (Int.natAbs_neg a.z)))

private def inputs (a : Quaternion) (rest : Polynomial.Values) : Polynomial.Values :=
  .cons a.w (.cons a.x (.cons a.y (.cons a.z rest)))

private def four : Nat := Nat.succ Nat.zero.succ.succ.succ

theorem mul_assoc (a b c : Quaternion) : Eq ((a.mul b).mul c) (a.mul (b.mul c)) :=
  let values := inputs a (inputs b (inputs c .nil))
  let A := Polynomial.Coordinates.variables Nat.zero
  let B := Polynomial.Coordinates.variables four
  let C := Polynomial.Coordinates.variables (four.add four)
  let lhs := (A.mul B).mul C
  let rhs := A.mul (B.mul C)
  ext (lhs.w.sound rhs.w values Eq.refl) (lhs.x.sound rhs.x values Eq.refl)
    (lhs.y.sound rhs.y values Eq.refl) (lhs.z.sound rhs.z values Eq.refl)

theorem conj_mul (a b : Quaternion) : Eq (a.mul b).conj (b.conj.mul a.conj) :=
  let values := inputs a (inputs b .nil)
  let A := Polynomial.Coordinates.variables Nat.zero
  let B := Polynomial.Coordinates.variables four
  let lhs := (A.mul B).conj
  let rhs := B.conj.mul A.conj
  ext (lhs.w.sound rhs.w values Eq.refl) (lhs.x.sound rhs.x values Eq.refl)
    (lhs.y.sound rhs.y values Eq.refl) (lhs.z.sound rhs.z values Eq.refl)

theorem mul_conj_eq_normSq (a : Quaternion) : Eq (a.mul a.conj) (scalar (Int.ofNat a.normSq)) :=
  let values := inputs a .nil
  let A := Polynomial.Coordinates.variables Nat.zero
  let P := A.mul A.conj
  ext ((P.w.sound (A.dot A) values Eq.refl).trans a.normSq_cast.symm)
    (P.x.sound .zero values Eq.refl) (P.y.sound .zero values Eq.refl) (P.z.sound .zero values Eq.refl)

theorem conj_mul_eq_normSq (a : Quaternion) : Eq (a.conj.mul a) (scalar (Int.ofNat a.normSq)) :=
  (congrArg a.conj.mul (conj_conj a)).symm.trans
    ((mul_conj_eq_normSq a.conj).trans (congrArg (fun n => scalar (Int.ofNat n)) (normSq_conj a)))

theorem scalar_mul (k : Int) (a : Quaternion) : Eq ((scalar k).mul a) (scale k a) :=
  let values := Polynomial.Values.cons k (inputs a .nil)
  let K := Polynomial.Expr.var Nat.zero
  let A := Polynomial.Coordinates.variables Nat.zero.succ
  let lhs := (Polynomial.Coordinates.scalar K).mul A
  let rhs := A.scale K
  ext (lhs.w.sound rhs.w values Eq.refl) (lhs.x.sound rhs.x values Eq.refl)
    (lhs.y.sound rhs.y values Eq.refl) (lhs.z.sound rhs.z values Eq.refl)

theorem mul_scalar (k : Int) (a : Quaternion) : Eq (a.mul (scalar k)) (scale k a) :=
  let values := Polynomial.Values.cons k (inputs a .nil)
  let K := Polynomial.Expr.var Nat.zero
  let A := Polynomial.Coordinates.variables Nat.zero.succ
  let lhs := A.mul (Polynomial.Coordinates.scalar K)
  let rhs := A.scale K
  ext (lhs.w.sound rhs.w values Eq.refl) (lhs.x.sound rhs.x values Eq.refl)
    (lhs.y.sound rhs.y values Eq.refl) (lhs.z.sound rhs.z values Eq.refl)

theorem scale_one (a : Quaternion) : Eq (scale Int.one a) a :=
  ext (Int.one_mul a.w) (Int.one_mul a.x) (Int.one_mul a.y) (Int.one_mul a.z)

theorem scale_mul (a : Quaternion) (k l : Int) : Eq (scale k (scale l a)) (scale (k.mul l) a) :=
  ext (Int.mul_assoc k l a.w).symm (Int.mul_assoc k l a.x).symm
    (Int.mul_assoc k l a.y).symm (Int.mul_assoc k l a.z).symm

theorem scale_mul_left (k : Int) (a b : Quaternion) :
    Eq ((scale k a).mul b) (scale k (a.mul b)) :=
  (congrArg (fun t : Quaternion => t.mul b) (scalar_mul k a).symm).trans
    ((mul_assoc (scalar k) a b).trans (scalar_mul k (a.mul b)))

theorem scale_mul_right (k : Int) (a b : Quaternion) :
    Eq (a.mul (scale k b)) (scale k (a.mul b)) :=
  (congrArg a.mul (mul_scalar k b).symm).trans
    ((mul_assoc a b (scalar k)).symm.trans (mul_scalar k (a.mul b)))

theorem conj_scale (k : Int) (a : Quaternion) : Eq (scale k a).conj (scale k a.conj) :=
  ext Eq.refl (Int.mul_neg k a.x).symm (Int.mul_neg k a.y).symm (Int.mul_neg k a.z).symm

theorem dot_scale (k : Int) (a b : Quaternion) : Eq ((scale k a).dot b) (k.mul (a.dot b)) :=
  let values := Polynomial.Values.cons k (inputs a (inputs b .nil))
  let K := Polynomial.Expr.var Nat.zero
  let A := Polynomial.Coordinates.variables Nat.zero.succ
  let B := Polynomial.Coordinates.variables four.succ
  ((A.scale K).dot B).sound (K.mul (A.dot B)) values Eq.refl

theorem dot_conj (a b : Quaternion) : Eq (a.conj.dot b.conj) (a.dot b) :=
  Eq.map₂ Int.add (congrArg (a.w.mul b.w).add (Int.neg_mul_neg a.x b.x))
    (Eq.map₂ Int.add (Int.neg_mul_neg a.y b.y) (Int.neg_mul_neg a.z b.z))

theorem dot_mul_left (p a b : Quaternion) :
    Eq ((p.mul a).dot (p.mul b)) ((p.dot p).mul (a.dot b)) :=
  let values := inputs p (inputs a (inputs b .nil))
  let P := Polynomial.Coordinates.variables Nat.zero
  let A := Polynomial.Coordinates.variables four
  let B := Polynomial.Coordinates.variables (four.add four)
  ((P.mul A).dot (P.mul B)).sound ((P.dot P).mul (A.dot B)) values Eq.refl

theorem dot_mul_right (p a b : Quaternion) :
    Eq ((a.mul p).dot (b.mul p)) ((p.dot p).mul (a.dot b)) :=
  (dot_conj (a.mul p) (b.mul p)).symm.trans
    ((Eq.map₂ dot (conj_mul a p) (conj_mul b p)).trans
      ((dot_mul_left p.conj a.conj b.conj).trans (Eq.map₂ Int.mul (dot_conj p p) (dot_conj a b))))

/-- Euler–Lagrange four-square multiplicativity over the integers. -/
theorem normSq_mul (a b : Quaternion) : Eq (a.mul b).normSq (a.normSq.mul b.normSq) :=
  Int.ofNat_inj.mp ((normSq_cast (a.mul b)).trans
    ((dot_mul_left a b b).trans (Eq.map₂ Int.mul a.normSq_cast.symm b.normSq_cast.symm)))

theorem normSq_scale (k : Int) (a : Quaternion) :
    Eq (scale k a).normSq (a.normSq.mul (k.natAbs.mul k.natAbs)) :=
  (congrArg normSq (mul_scalar k a).symm).trans (normSq_mul a (scalar k))

theorem scale_cancel {a b : Quaternion} {k : Int} (hk : Not (Eq k Int.zero))
    (h : Eq (scale k a) (scale k b)) : Eq a b :=
  ext (Int.eq_of_mul_eq_mul_left hk (congrArg Quaternion.w h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg Quaternion.x h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg Quaternion.y h))
    (Int.eq_of_mul_eq_mul_left hk (congrArg Quaternion.z h))

theorem nonzero_scale {a : Quaternion} {k : Int} (ha : a.Nonzero) (hk : Not (Eq k Int.zero)) :
    (scale k a).Nonzero :=
  (nonzero_iff_ne_zero (scale k a)).mpr (fun e => (nonzero_iff_ne_zero a).mp ha
    (scale_cancel hk (e.trans (ext (a := scale k zero) (b := zero) (Int.mul_zero k) (Int.mul_zero k)
      (Int.mul_zero k) (Int.mul_zero k)).symm)))

theorem nonzero_mul {a b : Quaternion} (ha : a.Nonzero) (hb : b.Nonzero) : (a.mul b).Nonzero :=
  nonzero_of_normSq_ne_zero
    (fun e => ((Nat.mul_eq_zero.mp ((normSq_mul a b).symm.trans e)).elim
      (normSq_ne_zero ha) (normSq_ne_zero hb)))

/-- The unnormalized ternary product has the product of the three squared norms. -/
theorem normSq_triad (a b c : Quaternion) :
    Eq ((a.mul b.conj).mul c).normSq ((a.normSq.mul b.normSq).mul c.normSq) :=
  (normSq_mul (a.mul b.conj) c).trans
    (congrArg (fun n : Nat => n.mul c.normSq)
      ((normSq_mul a b.conj).trans (congrArg a.normSq.mul (normSq_conj b))))

theorem triad_nonzero {a b c : Quaternion} (ha : a.Nonzero) (hb : b.Nonzero) (hc : c.Nonzero) :
    And (Eq ((a.mul b.conj).mul c).normSq ((a.normSq.mul b.normSq).mul c.normSq))
      (Not (Eq ((a.normSq.mul b.normSq).mul c.normSq) Nat.zero)) :=
  And.intro (normSq_triad a b c)
    (fun h => (Nat.mul_eq_zero.mp h).elim
      (fun h => (Nat.mul_eq_zero.mp h).elim (normSq_ne_zero ha) (normSq_ne_zero hb))
      (normSq_ne_zero hc))

end Quaternion
end Omega

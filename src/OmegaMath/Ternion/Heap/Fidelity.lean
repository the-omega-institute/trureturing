/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Ternion.Heap.Core
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Squared projective Born fidelity, its Lagrange bound, and its invariance under
signed projective scaling and common heap translations.
-/

noncomputable section

@[expose] public section

namespace Omega.Ternion

open Quaternion

def kappa (a b : Quaternion) : IntRatio :=
  IntRatio.value (Int.square (a.dot b)) (a.normSq.mul b.normSq)

def ProjTernion.kappa (a b : ProjTernion) : IntRatio := Ternion.kappa a.rep b.rep

theorem kappa_refl (a : Quaternion) (ha : a.Nonzero) :
    IntRatio.Equivalent (kappa a a) (IntRatio.ofInt Int.one) :=
  let n := a.normSq
  have h : Eq (Int.square (a.dot a)) (Int.ofNat (n.mul n)) :=
    congrArg Int.square a.normSq_cast.symm
  Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value t (n.mul n)) (IntRatio.ofInt Int.one))
    h.symm (IntRatio.value_self (n.mul n)
      (fun e => (Nat.mul_eq_zero.mp e).elim (normSq_ne_zero ha) (normSq_ne_zero ha)))

theorem kappa_symm (a b : Quaternion) : IntRatio.Equivalent (kappa a b) (kappa b a) :=
  Eq.subst (IntRatio.Equivalent (kappa a b))
    (Eq.map₂ IntRatio.value (congrArg Int.square (dot_comm a b)) (Nat.mul_comm a.normSq b.normSq))
    (IntRatio.equivalent_refl (kappa a b))

private theorem kappa_common_factor (p q a b : Quaternion) (d : Nat) (hd : Not (Eq d Nat.zero))
    (hNum : Eq (Int.square (p.dot q)) ((Int.square (a.dot b)).mul (Int.ofNat d)))
    (hDen : Eq (p.normSq.mul q.normSq) ((a.normSq.mul b.normSq).mul d)) :
    IntRatio.Equivalent (kappa p q) (kappa a b) :=
  Eq.subst (fun t => IntRatio.Equivalent t (kappa a b)) (Eq.map₂ IntRatio.value hNum hDen).symm
    (IntRatio.value_scale_of_ne_zero (Int.square (a.dot b)) (a.normSq.mul b.normSq) d hd)

theorem nat_mul_ne_zero {a b : Nat} (ha : Not (Eq a Nat.zero)) (hb : Not (Eq b Nat.zero)) :
    Not (Eq (a.mul b) Nat.zero) :=
  fun e => (Nat.mul_eq_zero.mp e).elim ha hb

theorem kappa_scale_left (k : Int) (a b : Quaternion) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (kappa (scale k a) b) (kappa a b) :=
  let d := k.natAbs
  have hd : Not (Eq d Nat.zero) := fun e => hk (Int.natAbs_eq_zero.mp e)
  kappa_common_factor (scale k a) b a b (d.mul d) (nat_mul_ne_zero hd hd)
    ((congrArg Int.square (dot_scale k a b)).trans ((Int.square_mul k (a.dot b)).trans
      ((Int.mul_comm (Int.square k) (Int.square (a.dot b))).trans
        (congrArg (Int.square (a.dot b)).mul Int.natAbs_mul_self.symm))))
    ((congrArg (fun n : Nat => n.mul b.normSq) (normSq_scale k a)).trans
      (Nat.mul_right_comm a.normSq (d.mul d) b.normSq))

theorem kappa_scale_right (k : Int) (a b : Quaternion) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (kappa a (scale k b)) (kappa a b) :=
  (kappa_symm a (scale k b)).trans ((kappa_scale_left k b a hk).trans (kappa_symm b a))

theorem kappa_scale (k l : Int) (a b : Quaternion) (hk : Not (Eq k Int.zero))
    (hl : Not (Eq l Int.zero)) :
    IntRatio.Equivalent (kappa (scale k a) (scale l b)) (kappa a b) :=
  (kappa_scale_left k a (scale l b) hk).trans (kappa_scale_right l a b hl)

theorem kappa_congr {a b c d : Quaternion} (h : RayEquiv a b) (g : RayEquiv c d) :
    IntRatio.Equivalent (kappa a c) (kappa b d) :=
  h.right.right.elim (fun i witness => witness.elim (fun j left =>
    g.right.right.elim (fun k witness => witness.elim (fun l right =>
      (kappa_scale i k a c left.left right.left).symm.trans
        (Eq.subst (fun t => IntRatio.Equivalent t (kappa b d))
          (Eq.map₂ kappa left.right.right right.right.right).symm
          (kappa_scale j l b d left.right.left right.right.left))))))

/-- The six Plücker coordinates of the two input vectors, squared and summed. -/
def minorSquares (a b : Quaternion) : Int :=
  let m := fun (ai aj bi bj : Int) => Int.square ((ai.mul bj).sub (aj.mul bi))
  ((m a.w a.x b.w b.x).add (m a.w a.y b.w b.y)).add
    (((m a.w a.z b.w b.z).add (m a.x a.y b.x b.y)).add
      ((m a.x a.z b.x b.z).add (m a.y a.z b.y b.z)))

theorem lagrange_identity (a b : Quaternion) :
    Eq ((Int.ofNat (a.normSq.mul b.normSq)).sub (Int.square (a.dot b))) (minorSquares a b) :=
  let start := Nat.zero
  let v := Polynomial.Expr.var
  let w := v start
  let x := v start.succ
  let y := v start.succ.succ
  let z := v start.succ.succ.succ
  let h := start.succ.succ.succ.succ
  let r := v h
  let s := v h.succ
  let t := v h.succ.succ
  let u := v h.succ.succ.succ
  let values := Polynomial.Values.cons a.w
    (.cons a.x (.cons a.y (.cons a.z (.cons b.w (.cons b.x (.cons b.y (.cons b.z .nil)))))))
  let dot := ((w.mul r).add (x.mul s)).add ((y.mul t).add (z.mul u))
  let N := (w.sq.add x.sq).add (y.sq.add z.sq)
  let M := (r.sq.add s.sq).add (t.sq.add u.sq)
  let m := fun (ai aj bi bj : Polynomial.Expr) => ((ai.mul bj).sub (aj.mul bi)).sq
  let minors := ((m w x r s).add (m w y r t)).add
    (((m w z r u).add (m x y s t)).add ((m x z s u).add (m y z t u)))
  (congrArg (fun k : Int => k.sub (Int.square (a.dot b)))
    (Eq.map₂ Int.mul a.normSq_cast b.normSq_cast)).trans
      (((N.mul M).sub dot.sq).sound minors values Eq.refl)

private theorem nonneg_add {a b : Int} (ha : a.NonNeg) (hb : b.NonNeg) : (a.add b).NonNeg :=
  (Int.rec (motive := fun a => ∀ b : Int, a.NonNeg → b.NonNeg → (a.add b).NonNeg)
    (fun n b => Int.rec (motive := fun b => (Int.ofNat n).NonNeg → b.NonNeg →
      ((Int.ofNat n).add b).NonNeg) (fun _ _ _ => True.intro) (fun _ _ h => False.elim h) b)
    (fun _ _ h _ => False.elim h) a) b ha hb

theorem minorSquares_nonneg (a b : Quaternion) : (minorSquares a b).NonNeg :=
  nonneg_add (nonneg_add (Int.square_nonneg _) (Int.square_nonneg _))
    (nonneg_add (nonneg_add (Int.square_nonneg _) (Int.square_nonneg _))
      (nonneg_add (Int.square_nonneg _) (Int.square_nonneg _)))

private theorem value_le_one (a : Int) (n : Nat) (hn : Not (Eq n Nat.zero))
    (h : a.le (Int.ofNat n)) :
    IntRatio.Le (IntRatio.value a n) (IntRatio.ofInt Int.one) :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → a.le (Int.ofNat n) →
    IntRatio.Le (IntRatio.value a n) (IntRatio.ofInt Int.one))
    (fun h _ => False.elim (h Eq.refl))
    (fun n _ _ h => Eq.subst (fun b => (a.mul Int.one).le b) (Int.one_mul (Int.ofNat n.succ)).symm
      (Eq.subst (fun k : Int => k.le (Int.ofNat n.succ)) (Int.mul_one a).symm h)) n) hn h

theorem kappa_le_one (a b : Quaternion) (ha : a.Nonzero) (hb : b.Nonzero) :
    IntRatio.Le (kappa a b) (IntRatio.ofInt Int.one) :=
  value_le_one (Int.square (a.dot b)) (a.normSq.mul b.normSq)
    (nat_mul_ne_zero (normSq_ne_zero ha) (normSq_ne_zero hb))
    (Eq.subst Int.NonNeg (lagrange_identity a b).symm (minorSquares_nonneg a b))

theorem kappa_mul_right (p a b : Quaternion) (hp : p.Nonzero) :
    IntRatio.Equivalent (kappa (a.mul p) (b.mul p)) (kappa a b) :=
  let n := p.normSq
  have hd := normSq_ne_zero hp
  have hDot : Eq ((a.mul p).dot (b.mul p)) ((a.dot b).mul (Int.ofNat n)) :=
    (dot_mul_right p a b).trans
      ((Int.mul_comm (p.dot p) (a.dot b)).trans (congrArg (a.dot b).mul p.normSq_cast.symm))
  kappa_common_factor (a.mul p) (b.mul p) a b (n.mul n) (nat_mul_ne_zero hd hd)
    ((congrArg Int.square hDot).trans (Int.square_mul (a.dot b) (Int.ofNat n)))
    ((Eq.map₂ Nat.mul (normSq_mul a p) (normSq_mul b p)).trans
      ((Nat.mul_assoc a.normSq n (b.normSq.mul n)).trans
        ((congrArg a.normSq.mul
          ((Nat.mul_assoc n b.normSq n).symm.trans
            ((congrArg (fun k : Nat => k.mul n) (Nat.mul_comm n b.normSq)).trans
              (Nat.mul_assoc b.normSq n n)))).trans
          (Nat.mul_assoc a.normSq b.normSq (n.mul n)).symm)))

theorem kappa_heap_invariant (a b u v : Quaternion) (hu : u.Nonzero) (hv : v.Nonzero) :
    IntRatio.Equivalent (kappa (triad a u v) (triad b u v)) (kappa a b) :=
  have h : u.conj.Nonzero := nonzero_of_normSq_ne_zero
    (fun e => normSq_ne_zero hu ((normSq_conj u).symm.trans e))
  Eq.subst (fun k => IntRatio.Equivalent k (kappa a b))
    (Eq.map₂ kappa (mul_assoc a u.conj v) (mul_assoc b u.conj v)).symm
    (kappa_mul_right (u.conj.mul v) a b (nonzero_mul h hv))

end Omega.Ternion

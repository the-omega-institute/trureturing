/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
public import OmegaMath.Algebra.Quaternion

/-!
Omega original.

Shell maps of integer quaternions. For an integer `s` and quaternions `p`, `a` the shell map
sends `v` to `s v + p v a`. When `p`, `q`, `r` and `a` are pure, the compositions
`P_p P_q P_p` and `P_p P_q P_r P_p` are given by exact identities whose defect terms are
multiples of `s² - N(p) N(a)`. Every product `p v a` with pure `p` and `a` is handled through
the pair action `v ↦ c v + (d v) a`, whose composition law only uses `a a = -N(a)`.
-/

noncomputable section

@[expose] public section

namespace Omega
namespace Quaternion

/-- Purity: the real coordinate vanishes. -/
def IsPure (a : Quaternion) : Prop := Eq a.w Int.zero

/-- The shell map `v ↦ s v + p v a`. -/
def shell (s : Int) (p a v : Quaternion) : Quaternion :=
  (scale s v).add ((p.mul v).mul a)

/-- The pair action `u ↦ c u + (d u) a`. -/
def pairAct (a c d u : Quaternion) : Quaternion :=
  (c.mul u).add ((d.mul u).mul a)

/-- First component of the composition of two pair actions, with `α = N(a)`. -/
def pairFst (α : Int) (c d e f : Quaternion) : Quaternion :=
  (c.mul e).add (scale α.neg (d.mul f))

/-- Second component of the composition of two pair actions. -/
def pairSnd (c d e f : Quaternion) : Quaternion :=
  (c.mul f).add (d.mul e)

theorem eq_mk_of_isPure {a : Quaternion} (h : a.IsPure) :
    Eq a (Quaternion.mk Int.zero a.x a.y a.z) :=
  ext h rfl rfl rfl

namespace ShellCertificate

open Polynomial

def cadd (a b : Coordinates) : Coordinates := ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

def pure (n : Nat) : Coordinates := ⟨.zero, .var n, .var n.succ, .var n.succ.succ⟩

def quad (a : Quaternion) (rest : Values) : Values :=
  .cons a.w (.cons a.x (.cons a.y (.cons a.z rest)))

def triple (x y z : Int) (rest : Values) : Values := .cons x (.cons y (.cons z rest))

def cfst (A : Expr) (c d e f : Coordinates) : Coordinates := cadd (c.mul e) ((d.mul f).scale A.neg)

def csnd (c d e f : Coordinates) : Coordinates := cadd (c.mul f) (d.mul e)

def n3 : Nat := Nat.zero.succ.succ.succ
def n4 : Nat := n3.succ
def n5 : Nat := n4.succ
def n8 : Nat := n4.add n4
def n12 : Nat := n8.add n4

end ShellCertificate

open Polynomial ShellCertificate

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem mul_add (x y z : Quaternion) : Eq (x.mul (y.add z)) ((x.mul y).add (x.mul z)) :=
  let values := quad x (quad y (quad z .nil))
  let X := Coordinates.variables Nat.zero
  let Y := Coordinates.variables n4
  let Z := Coordinates.variables n8
  let lhs := X.mul (cadd Y Z)
  let rhs := cadd (X.mul Y) (X.mul Z)
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem add_mul (x y z : Quaternion) : Eq ((x.add y).mul z) ((x.mul z).add (y.mul z)) :=
  let values := quad x (quad y (quad z .nil))
  let X := Coordinates.variables Nat.zero
  let Y := Coordinates.variables n4
  let Z := Coordinates.variables n8
  let lhs := (cadd X Y).mul Z
  let rhs := cadd (X.mul Z) (Y.mul Z)
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem add_comm (x y : Quaternion) : Eq (x.add y) (y.add x) :=
  let values := quad x (quad y .nil)
  let X := Coordinates.variables Nat.zero
  let Y := Coordinates.variables n4
  let lhs := cadd X Y
  let rhs := cadd Y X
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem add_add_add_comm (x y z t : Quaternion) :
    Eq ((x.add y).add (z.add t)) ((x.add z).add (y.add t)) :=
  let values := quad x (quad y (quad z (quad t .nil)))
  let X := Coordinates.variables Nat.zero
  let Y := Coordinates.variables n4
  let Z := Coordinates.variables n8
  let T := Coordinates.variables n12
  let lhs := cadd (cadd X Y) (cadd Z T)
  let rhs := cadd (cadd X Z) (cadd Y T)
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem scale_add (k : Int) (x y : Quaternion) :
    Eq (scale k (x.add y)) ((scale k x).add (scale k y)) :=
  let values := Values.cons k (quad x (quad y .nil))
  let K := Expr.var Nat.zero
  let X := Coordinates.variables Nat.zero.succ
  let Y := Coordinates.variables n5
  let lhs := (cadd X Y).scale K
  let rhs := cadd (X.scale K) (Y.scale K)
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem mk_mul_self (x y z : Int) :
    let a := Quaternion.mk Int.zero x y z
    Eq (a.mul a) (scalar (a.dot a).neg) :=
  let values := triple x y z .nil
  let A := pure Nat.zero
  let lhs := A.mul A
  let rhs := Coordinates.scalar (A.dot A).neg
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

/-- A pure quaternion squares to minus its squared norm. -/
theorem mul_self_of_isPure {a : Quaternion} (h : a.IsPure) :
    Eq (a.mul a) (scalar (a.dot a).neg) :=
  Eq.subst (motive := fun t : Quaternion => Eq (t.mul t) (scalar (t.dot t).neg))
    (eq_mk_of_isPure h).symm (mk_mul_self a.x a.y a.z)

theorem mul_mul_of_isPure {a : Quaternion} (h : a.IsPure) (u : Quaternion) :
    Eq ((u.mul a).mul a) (scale (a.dot a).neg u) :=
  (mul_assoc u a a).trans ((congrArg u.mul (mul_self_of_isPure h)).trans (mul_scalar _ u))

theorem add_scale_zero (x y : Quaternion) :
    Eq (x.add (scale (Int.ofNat Nat.zero) y)) x :=
  let coordinate := fun (c d : Int) =>
    (congrArg c.add (Int.zero_mul d)).trans (Int.add_zero c)
  ext (coordinate x.w y.w) (coordinate x.x y.x) (coordinate x.y y.y) (coordinate x.z y.z)

theorem shell_eq_pairAct (s : Int) (p a v : Quaternion) :
    Eq (shell s p a v) (pairAct a (scalar s) p v) :=
  congrArg (fun t : Quaternion => t.add ((p.mul v).mul a)) (scalar_mul s v).symm

theorem mul_pairAct (a x e f u : Quaternion) :
    Eq (x.mul (pairAct a e f u)) (pairAct a (x.mul e) (x.mul f) u) :=
  (mul_add x (e.mul u) ((f.mul u).mul a)).trans
    (Eq.map₂ add (mul_assoc x e u).symm
      ((mul_assoc x (f.mul u) a).symm.trans
        (congrArg (fun t : Quaternion => t.mul a) (mul_assoc x f u).symm)))

theorem pairAct_add (a c d c' d' u : Quaternion) :
    Eq ((pairAct a c d u).add (pairAct a c' d' u)) (pairAct a (c.add c') (d.add d') u) :=
  (add_add_add_comm (c.mul u) ((d.mul u).mul a) (c'.mul u) ((d'.mul u).mul a)).trans
    (Eq.map₂ add (add_mul c c' u).symm
      ((add_mul (d.mul u) (d'.mul u) a).symm.trans
        (congrArg (fun t : Quaternion => t.mul a) (add_mul d d' u).symm)))

theorem scale_pairAct (k : Int) (a c d u : Quaternion) :
    Eq (scale k (pairAct a c d u)) (pairAct a (scale k c) (scale k d) u) :=
  (scale_add k (c.mul u) ((d.mul u).mul a)).trans
    (Eq.map₂ add (scale_mul_left k c u).symm
      ((scale_mul_left k (d.mul u) a).symm.trans
        (congrArg (fun t : Quaternion => t.mul a) (scale_mul_left k d u).symm)))

theorem pairAct_mul {a : Quaternion} (h : a.IsPure) (c d u : Quaternion) :
    Eq ((pairAct a c d u).mul a) (pairAct a (scale (a.dot a).neg d) c u) :=
  (add_mul (c.mul u) ((d.mul u).mul a) a).trans
    ((congrArg ((c.mul u).mul a).add (mul_mul_of_isPure h (d.mul u))).trans
      ((add_comm ((c.mul u).mul a) (scale (a.dot a).neg (d.mul u))).trans
        (congrArg (fun t : Quaternion => t.add ((c.mul u).mul a))
          (scale_mul_left (a.dot a).neg d u).symm)))

/-- Composition law of pair actions for pure `a`. -/
theorem pairAct_pairAct {a : Quaternion} (h : a.IsPure) (c d e f u : Quaternion) :
    Eq (pairAct a c d (pairAct a e f u))
      (pairAct a (pairFst (a.dot a) c d e f) (pairSnd c d e f) u) :=
  (Eq.map₂ add (mul_pairAct a c e f u)
      ((congrArg (fun t : Quaternion => t.mul a) (mul_pairAct a d e f u)).trans
        (pairAct_mul h (d.mul e) (d.mul f) u))).trans
    (pairAct_add a (c.mul e) (c.mul f) (scale (a.dot a).neg (d.mul f)) (d.mul e) u)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem compress_pairs_mk (α s x1 x2 x3 y1 y2 y3 : Int) :
    let p := Quaternion.mk Int.zero x1 x2 x3
    let q := Quaternion.mk Int.zero y1 y2 y3
    let c := pairFst α (scalar s) q (scalar s) p
    let d := pairSnd (scalar s) q (scalar s) p
    let t := (s.mul s).add (α.mul (p.dot q))
    let δ := (s.mul s).sub ((p.dot p).mul α)
    And (Eq (pairFst α (scalar s) p c d) ((scale (t.add t) (scalar s)).add (scale δ (scalar s.neg))))
      (Eq (pairSnd (scalar s) p c d) ((scale (t.add t) p).add (scale δ q))) :=
  let values := Values.cons α (Values.cons s (triple x1 x2 x3 (triple y1 y2 y3 .nil)))
  let A := Expr.var Nat.zero
  let S := Expr.var Nat.zero.succ
  let P := pure Nat.zero.succ.succ
  let Q := pure n5
  let C := cfst A (Coordinates.scalar S) Q (Coordinates.scalar S) P
  let D := csnd (Coordinates.scalar S) Q (Coordinates.scalar S) P
  let T := (S.mul S).add (A.mul (P.dot Q))
  let Δ := (S.mul S).sub ((P.dot P).mul A)
  let lhs := cfst A (Coordinates.scalar S) P C D
  let rhs := cadd ((Coordinates.scalar S).scale (T.add T)) ((Coordinates.scalar S.neg).scale Δ)
  let lhs' := csnd (Coordinates.scalar S) P C D
  let rhs' := cadd (P.scale (T.add T)) (Q.scale Δ)
  And.intro
    (ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
      (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl))
    (ext (lhs'.w.sound rhs'.w values rfl) (lhs'.x.sound rhs'.x values rfl)
      (lhs'.y.sound rhs'.y values rfl) (lhs'.z.sound rhs'.z values rfl))

/-- Shell compression without norm conditions. For pure `p`, `q`, `a`, any integer `s` and
any quaternion `v`,
`P_p P_q P_p v = 2 (s² + N(a) (p·q)) P_p v + (s² - N(p) N(a)) P_{-s,q,a} v`,
where `P_{-s,q,a} v = q v a - s v`. -/
theorem shell_compress (s : Int) {p q a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (ha : a.IsPure) (v : Quaternion) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    let δ := (s.mul s).sub ((p.dot p).mul (a.dot a))
    Eq (shell s p a (shell s q a (shell s p a v)))
      ((scale (t.add t) (shell s p a v)).add (scale δ (shell s.neg q a v))) :=
  let S := scalar s
  let α := a.dot a
  let t := (s.mul s).add (α.mul (p.dot q))
  let δ := (s.mul s).sub ((p.dot p).mul α)
  let c := pairFst α S q S p
  let d := pairSnd S q S p
  let stmt := fun P Q : Quaternion =>
    let c := pairFst α S Q S P
    let d := pairSnd S Q S P
    let t := (s.mul s).add (α.mul (P.dot Q))
    let δ := (s.mul s).sub ((P.dot P).mul α)
    And (Eq (pairFst α S P c d) ((scale (t.add t) S).add (scale δ (scalar s.neg))))
      (Eq (pairSnd S P c d) ((scale (t.add t) P).add (scale δ Q)))
  have pairs : stmt p q :=
    Eq.subst (motive := fun P => stmt P q) (eq_mk_of_isPure hp).symm
      (Eq.subst (motive := fun Q => stmt (Quaternion.mk Int.zero p.x p.y p.z) Q)
        (eq_mk_of_isPure hq).symm (compress_pairs_mk α s p.x p.y p.z q.x q.y q.z))
  have inner : Eq (shell s q a (shell s p a v)) (pairAct a c d v) :=
    (congrArg (shell s q a) (shell_eq_pairAct s p a v)).trans
      ((shell_eq_pairAct s q a _).trans (pairAct_pairAct ha S q S p v))
  have left : Eq (shell s p a (shell s q a (shell s p a v)))
      (pairAct a (pairFst α S p c d) (pairSnd S p c d) v) :=
    (congrArg (shell s p a) inner).trans
      ((shell_eq_pairAct s p a _).trans (pairAct_pairAct ha S p c d v))
  have right : Eq ((scale (t.add t) (shell s p a v)).add (scale δ (shell s.neg q a v)))
      (pairAct a ((scale (t.add t) S).add (scale δ (scalar s.neg)))
        ((scale (t.add t) p).add (scale δ q)) v) :=
    (Eq.map₂ add
      ((congrArg (scale (t.add t)) (shell_eq_pairAct s p a v)).trans
        (scale_pairAct (t.add t) a S p v))
      ((congrArg (scale δ) (shell_eq_pairAct s.neg q a v)).trans
        (scale_pairAct δ a (scalar s.neg) q v))).trans
    (pairAct_add a _ _ _ _ v)
  left.trans ((Eq.map₂ (fun c' d' => pairAct a c' d' v) pairs.left pairs.right).trans right.symm)

/-- On the shell `s² = N(p) N(a)` the composition `P_p P_q P_p` is the multiple
`2 (s² + N(a) (p·q))` of `P_p`. -/
theorem shell_compress_of_eq (s : Int) {p q a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (ha : a.IsPure) (hs : Eq (s.mul s) ((p.dot p).mul (a.dot a))) (v : Quaternion) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    Eq (shell s p a (shell s q a (shell s p a v))) (scale (t.add t) (shell s p a v)) :=
  let t := (s.mul s).add ((a.dot a).mul (p.dot q))
  (shell_compress s hp hq ha v).trans
    ((congrArg (fun k : Int => (scale (t.add t) (shell s p a v)).add (scale k (shell s.neg q a v)))
      (Int.sub_eq_zero.mpr hs)).trans (add_scale_zero _ _))

end Quaternion
end Omega

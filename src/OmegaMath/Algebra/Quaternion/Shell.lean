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
the pair action `v ↦ c v + (d v) a`, whose composition law only uses `a a = -N(a)`. The
compression identity holds for every `v` exactly on the shell or when `s = 0` and `q = 0`.
For the maps `u_c v = (c v) a` with pure `a`, the three cyclic triple compositions minus the
three reverse ones equal `-N(a) (A x) a`, where `A` is the alternating sum of the six ordered
products of `p`, `q`, `r`; for pure `p`, `q`, `r` this is `6 N(a) (p · (q r)) (x a)`.
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

private def cadd (a b : Coordinates) : Coordinates := ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

private def pure (n : Nat) : Coordinates := ⟨.zero, .var n, .var n.succ, .var n.succ.succ⟩

private def quad (a : Quaternion) (rest : Values) : Values :=
  .cons a.w (.cons a.x (.cons a.y (.cons a.z rest)))

private def triple (x y z : Int) (rest : Values) : Values := .cons x (.cons y (.cons z rest))

private def cfst (A : Expr) (c d e f : Coordinates) : Coordinates := cadd (c.mul e) ((d.mul f).scale A.neg)

private def csnd (c d e f : Coordinates) : Coordinates := cadd (c.mul f) (d.mul e)

private def n3 : Nat := Nat.zero.succ.succ.succ
private def n4 : Nat := n3.succ
private def n5 : Nat := n4.succ
private def n8 : Nat := n4.add n4
private def n12 : Nat := n8.add n4

private def cneg (a : Coordinates) : Coordinates := ⟨a.w.neg, a.x.neg, a.y.neg, a.z.neg⟩

private def csub (a b : Coordinates) : Coordinates := cadd a (cneg b)

private def czero : Coordinates := ⟨.zero, .zero, .zero, .zero⟩

private def cunitI : Coordinates := ⟨.zero, .one, .zero, .zero⟩

private def cunitJ : Coordinates := ⟨.zero, .zero, .one, .zero⟩

private def cshell (S : Expr) (Q A V : Coordinates) : Coordinates :=
  cadd (V.scale S) ((Q.mul V).mul A)

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
  let A := ShellCertificate.pure Nat.zero
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
  let P := ShellCertificate.pure Nat.zero.succ.succ
  let Q := ShellCertificate.pure n5
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

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem triangle_pairs_mk (α s x1 x2 x3 y1 y2 y3 z1 z2 z3 : Int) :
    let p := Quaternion.mk Int.zero x1 x2 x3
    let q := Quaternion.mk Int.zero y1 y2 y3
    let r := Quaternion.mk Int.zero z1 z2 z3
    let S := scalar s
    let S' := scalar s.neg
    let c1 := pairFst α S r S p
    let d1 := pairSnd S r S p
    let c2 := pairFst α S q c1 d1
    let d2 := pairSnd S q c1 d1
    let t := s.mul ((s.mul s).add (α.mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := α.mul (p.dot (q.mul r))
    let δ := ((p.dot p).mul α).sub (s.mul s)
    And (Eq (pairFst α S p c2 d2) ((scale (t.add t) S).add
        ((scale (l.add l) (scale α.neg p)).add (scale δ (pairFst α S' r S' q)))))
      (Eq (pairSnd S p c2 d2) ((scale (t.add t) p).add
        ((scale (l.add l) S).add (scale δ (pairSnd S' r S' q))))) :=
  let values := Values.cons α (Values.cons s
    (triple x1 x2 x3 (triple y1 y2 y3 (triple z1 z2 z3 .nil))))
  let A := Expr.var Nat.zero
  let s' := Expr.var Nat.zero.succ
  let P := ShellCertificate.pure Nat.zero.succ.succ
  let Q := ShellCertificate.pure n5
  let R := ShellCertificate.pure n3.succ.succ.succ.succ.succ
  let S := Coordinates.scalar s'
  let S' := Coordinates.scalar s'.neg
  let C1 := cfst A S R S P
  let D1 := csnd S R S P
  let C2 := cfst A S Q C1 D1
  let D2 := csnd S Q C1 D1
  let T := s'.mul ((s'.mul s').add (A.mul (((P.dot Q).add (Q.dot R)).add (R.dot P))))
  let L := A.mul (P.dot (Q.mul R))
  let Δ := ((P.dot P).mul A).sub (s'.mul s')
  let lhs := cfst A S P C2 D2
  let rhs := cadd (S.scale (T.add T)) (cadd ((P.scale A.neg).scale (L.add L))
    ((cfst A S' R S' Q).scale Δ))
  let lhs' := csnd S P C2 D2
  let rhs' := cadd (P.scale (T.add T)) (cadd (S.scale (L.add L)) ((csnd S' R S' Q).scale Δ))
  And.intro
    (ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
      (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl))
    (ext (lhs'.w.sound rhs'.w values rfl) (lhs'.x.sound rhs'.x values rfl)
      (lhs'.y.sound rhs'.y values rfl) (lhs'.z.sound rhs'.z values rfl))

/-- Shell triangle identity without norm conditions. For pure `p`, `q`, `r`, `a`, any integer
`s`, any quaternion `v` and `z = P_p v`,
`P_p P_q P_r z = 2 s (s² + N(a) (p·q + q·r + r·p)) z + 2 N(a) [p, q, r] (z a)
  + (N(p) N(a) - s²) P_{-s,r,a} P_{-s,q,a} v`,
where `[p, q, r] = p · (q r)` is the triple product of the three pure quaternions. -/
theorem shell_triangle (s : Int) {p q r a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (hr : r.IsPure) (ha : a.IsPure) (v : Quaternion) :
    let z := shell s p a v
    let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := (a.dot a).mul (p.dot (q.mul r))
    let δ := ((p.dot p).mul (a.dot a)).sub (s.mul s)
    Eq (shell s p a (shell s q a (shell s r a z)))
      ((scale (t.add t) z).add ((scale (l.add l) (z.mul a)).add
        (scale δ (shell s.neg r a (shell s.neg q a v))))) :=
  let S := scalar s
  let S' := scalar s.neg
  let α := a.dot a
  let z := shell s p a v
  let t := s.mul ((s.mul s).add (α.mul (((p.dot q).add (q.dot r)).add (r.dot p))))
  let l := α.mul (p.dot (q.mul r))
  let δ := ((p.dot p).mul α).sub (s.mul s)
  let stmt := fun P Q R : Quaternion =>
    let c1 := pairFst α S R S P
    let d1 := pairSnd S R S P
    let c2 := pairFst α S Q c1 d1
    let d2 := pairSnd S Q c1 d1
    let t := s.mul ((s.mul s).add (α.mul (((P.dot Q).add (Q.dot R)).add (R.dot P))))
    let l := α.mul (P.dot (Q.mul R))
    let δ := ((P.dot P).mul α).sub (s.mul s)
    And (Eq (pairFst α S P c2 d2) ((scale (t.add t) S).add
        ((scale (l.add l) (scale α.neg P)).add (scale δ (pairFst α S' R S' Q)))))
      (Eq (pairSnd S P c2 d2) ((scale (t.add t) P).add
        ((scale (l.add l) S).add (scale δ (pairSnd S' R S' Q)))))
  have pairs : stmt p q r :=
    Eq.subst (motive := fun P => stmt P q r) (eq_mk_of_isPure hp).symm
      (Eq.subst (motive := fun Q => stmt (Quaternion.mk Int.zero p.x p.y p.z) Q r)
        (eq_mk_of_isPure hq).symm
        (Eq.subst (motive := fun R => stmt (Quaternion.mk Int.zero p.x p.y p.z)
            (Quaternion.mk Int.zero q.x q.y q.z) R)
          (eq_mk_of_isPure hr).symm
          (triangle_pairs_mk α s p.x p.y p.z q.x q.y q.z r.x r.y r.z)))
  let c1 := pairFst α S r S p
  let d1 := pairSnd S r S p
  let c2 := pairFst α S q c1 d1
  let d2 := pairSnd S q c1 d1
  have hz : Eq z (pairAct a S p v) := shell_eq_pairAct s p a v
  have step1 : Eq (shell s r a z) (pairAct a c1 d1 v) :=
    (congrArg (shell s r a) hz).trans
      ((shell_eq_pairAct s r a _).trans (pairAct_pairAct ha S r S p v))
  have step2 : Eq (shell s q a (shell s r a z)) (pairAct a c2 d2 v) :=
    (congrArg (shell s q a) step1).trans
      ((shell_eq_pairAct s q a _).trans (pairAct_pairAct ha S q c1 d1 v))
  have left : Eq (shell s p a (shell s q a (shell s r a z)))
      (pairAct a (pairFst α S p c2 d2) (pairSnd S p c2 d2) v) :=
    (congrArg (shell s p a) step2).trans
      ((shell_eq_pairAct s p a _).trans (pairAct_pairAct ha S p c2 d2 v))
  have defect : Eq (shell s.neg r a (shell s.neg q a v))
      (pairAct a (pairFst α S' r S' q) (pairSnd S' r S' q) v) :=
    (congrArg (shell s.neg r a) (shell_eq_pairAct s.neg q a v)).trans
      ((shell_eq_pairAct s.neg r a _).trans (pairAct_pairAct ha S' r S' q v))
  have right : Eq ((scale (t.add t) z).add ((scale (l.add l) (z.mul a)).add
        (scale δ (shell s.neg r a (shell s.neg q a v)))))
      (pairAct a ((scale (t.add t) S).add
          ((scale (l.add l) (scale α.neg p)).add (scale δ (pairFst α S' r S' q))))
        ((scale (t.add t) p).add ((scale (l.add l) S).add (scale δ (pairSnd S' r S' q)))) v) :=
    (Eq.map₂ add
      ((congrArg (scale (t.add t)) hz).trans (scale_pairAct (t.add t) a S p v))
      ((Eq.map₂ add
        ((congrArg (fun u : Quaternion => scale (l.add l) (u.mul a)) hz).trans
          ((congrArg (scale (l.add l)) (pairAct_mul ha S p v)).trans
            (scale_pairAct (l.add l) a (scale α.neg p) S v)))
        ((congrArg (scale δ) defect).trans (scale_pairAct δ a _ _ v))).trans
        (pairAct_add a _ _ _ _ v))).trans
    (pairAct_add a _ _ _ _ v)
  left.trans ((Eq.map₂ (fun c' d' => pairAct a c' d' v) pairs.left pairs.right).trans right.symm)

/-- On the shell `s² = N(p) N(a)` the defect vanishes:
`P_p P_q P_r P_p v = 2 s (s² + N(a) (p·q + q·r + r·p)) P_p v + 2 N(a) [p, q, r] (P_p v) a`.
No norm condition on `q` or `r` is needed. -/
theorem shell_triangle_of_eq (s : Int) {p q r a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (hr : r.IsPure) (ha : a.IsPure) (hs : Eq (s.mul s) ((p.dot p).mul (a.dot a)))
    (v : Quaternion) :
    let z := shell s p a v
    let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
    let l := (a.dot a).mul (p.dot (q.mul r))
    Eq (shell s p a (shell s q a (shell s r a z)))
      ((scale (t.add t) z).add (scale (l.add l) (z.mul a))) :=
  let z := shell s p a v
  let t := s.mul ((s.mul s).add ((a.dot a).mul (((p.dot q).add (q.dot r)).add (r.dot p))))
  let l := (a.dot a).mul (p.dot (q.mul r))
  (shell_triangle s hp hq hr ha v).trans
    ((congrArg (fun k : Int => (scale (t.add t) z).add ((scale (l.add l) (z.mul a)).add
        (scale k (shell s.neg r a (shell s.neg q a v)))))
      (Int.sub_eq_zero.mpr hs.symm)).trans
      (congrArg ((scale (t.add t) z).add) (add_scale_zero _ _)))

private def unitI : Quaternion := ⟨Int.zero, Int.one, Int.zero, Int.zero⟩

private def unitJ : Quaternion := ⟨Int.zero, Int.zero, Int.one, Int.zero⟩

private def defectS (s : Int) (q a w1 wi wj : Quaternion) : Int :=
  let xi := (wi.sub (unitI.mul w1)).mul a.conj
  let xj := (wj.sub (unitJ.mul w1)).mul a.conj
  let y := w1.mul a.conj
  let two := Int.one.add Int.one
  (((((two.mul s).mul w1.w).neg.sub
    (two.mul (((q.x.mul y.x).add (q.y.mul y.y)).add (q.z.mul y.z)))).add
      (q.x.mul xj.z)).sub (q.y.mul xi.z)).add (q.z.mul xi.y)

private def defectFacts (d s : Int) (q a : Quaternion) : Prop :=
  let W := fun v : Quaternion => scale d (shell s.neg q a v)
  let two := Int.one.add Int.one
  let xi := ((W unitI).sub (unitI.mul (W one))).mul a.conj
  let xj := ((W unitJ).sub (unitJ.mul (W one))).mul a.conj
  And (Eq (defectS s q a (W one) (W unitI) (W unitJ)) (two.mul ((d.mul s).mul s)))
    (And (Eq xj.z (two.mul ((d.mul (a.dot a)).mul q.x)))
      (And (Eq xi.z.neg (two.mul ((d.mul (a.dot a)).mul q.y)))
        (Eq xi.y (two.mul ((d.mul (a.dot a)).mul q.z)))))

private def defectZero (s : Int) (q a : Quaternion) : Prop :=
  let xi := (zero.sub (unitI.mul zero)).mul a.conj
  let xj := (zero.sub (unitJ.mul zero)).mul a.conj
  And (Eq (defectS s q a zero zero zero) Int.zero)
    (And (Eq xj.z Int.zero) (And (Eq xi.z.neg Int.zero) (Eq xi.y Int.zero)))

private def cdefectS (S : Expr) (Q A W1 Wi Wj : Coordinates) : Expr :=
  let xi := (csub Wi (cunitI.mul W1)).mul A.conj
  let xj := (csub Wj (cunitJ.mul W1)).mul A.conj
  let y := W1.mul A.conj
  let two := Expr.one.add Expr.one
  (((((two.mul S).mul W1.w).neg.sub
    (two.mul (((Q.x.mul y.x).add (Q.y.mul y.y)).add (Q.z.mul y.z)))).add
      (Q.x.mul xj.z)).sub (Q.y.mul xi.z)).add (Q.z.mul xi.y)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem defect_facts_mk (d s q1 q2 q3 a1 a2 a3 : Int) :
    defectFacts d s (Quaternion.mk Int.zero q1 q2 q3) (Quaternion.mk Int.zero a1 a2 a3) :=
  let values := Values.cons d (Values.cons s (triple q1 q2 q3 (triple a1 a2 a3 .nil)))
  let D := Expr.var Nat.zero
  let S := Expr.var Nat.zero.succ
  let Q := ShellCertificate.pure Nat.zero.succ.succ
  let A := ShellCertificate.pure n5
  let W := fun V : Coordinates => (cshell S.neg Q A V).scale D
  let one' := Coordinates.scalar Expr.one
  let two := Expr.one.add Expr.one
  let xi := (csub (W cunitI) (cunitI.mul (W one'))).mul A.conj
  let xj := (csub (W cunitJ) (cunitJ.mul (W one'))).mul A.conj
  let N := A.dot A
  And.intro ((cdefectS S Q A (W one') (W cunitI) (W cunitJ)).sound
      (two.mul ((D.mul S).mul S)) values rfl)
    (And.intro (xj.z.sound (two.mul ((D.mul N).mul Q.x)) values rfl)
      (And.intro (xi.z.neg.sound (two.mul ((D.mul N).mul Q.y)) values rfl)
        (xi.y.sound (two.mul ((D.mul N).mul Q.z)) values rfl)))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem defect_zero_mk (s q1 q2 q3 a1 a2 a3 : Int) :
    defectZero s (Quaternion.mk Int.zero q1 q2 q3) (Quaternion.mk Int.zero a1 a2 a3) :=
  let values := Values.cons s (triple q1 q2 q3 (triple a1 a2 a3 .nil))
  let S := Expr.var Nat.zero
  let Q := ShellCertificate.pure Nat.zero.succ
  let A := ShellCertificate.pure n4
  let xi := (csub czero (cunitI.mul czero)).mul A.conj
  let xj := (csub czero (cunitJ.mul czero)).mul A.conj
  And.intro ((cdefectS S Q A czero czero czero).sound .zero values rfl)
    (And.intro (xj.z.sound .zero values rfl)
      (And.intro (xi.z.neg.sound .zero values rfl) (xi.y.sound .zero values rfl)))

private theorem defect_facts (d s : Int) {q a : Quaternion} (hq : q.IsPure) (ha : a.IsPure) :
    And (defectFacts d s q a) (defectZero s q a) :=
  Eq.subst (motive := fun Q => And (defectFacts d s Q a) (defectZero s Q a))
    (eq_mk_of_isPure hq).symm
    (Eq.subst (motive := fun A => And (defectFacts d s (Quaternion.mk Int.zero q.x q.y q.z) A)
        (defectZero s (Quaternion.mk Int.zero q.x q.y q.z) A))
      (eq_mk_of_isPure ha).symm
      (And.intro (defect_facts_mk d s q.x q.y q.z a.x a.y a.z)
        (defect_zero_mk s q.x q.y q.z a.x a.y a.z)))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem shell_neg_zero_zero (a v : Quaternion) : Eq (shell Int.zero.neg zero a v) zero :=
  let values := quad a (quad v .nil)
  let A := Coordinates.variables Nat.zero
  let V := Coordinates.variables n4
  let lhs := cshell Expr.zero.neg czero A V
  ext (lhs.w.sound .zero values rfl) (lhs.x.sound .zero values rfl)
    (lhs.y.sound .zero values rfl) (lhs.z.sound .zero values rfl)

theorem eq_zero_of_add_eq_self {x y : Quaternion} (h : Eq (x.add y) x) : Eq y zero :=
  let coordinate := fun (c d : Int) (e : Eq (c.add d) c) =>
    Int.add_left_cancel (e.trans (Int.add_zero c).symm)
  ext (coordinate x.w y.w (congrArg Quaternion.w h)) (coordinate x.x y.x (congrArg Quaternion.x h))
    (coordinate x.y y.y (congrArg Quaternion.y h)) (coordinate x.z y.z (congrArg Quaternion.z h))

theorem add_scale_zero_right (x : Quaternion) (k : Int) : Eq (x.add (scale k zero)) x :=
  let coordinate := fun c : Int => (congrArg c.add (Int.mul_zero k)).trans (Int.add_zero c)
  ext (coordinate x.w) (coordinate x.x) (coordinate x.y) (coordinate x.z)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem two_ne_zero : Not (Eq (Int.one.add Int.one) Int.zero) :=
  Int.ofNat_succ_ne_zero (Nat.succ Nat.zero)

/-- The compression identity holds for every `v` exactly on the shell `s² = N(p) N(a)` and in the
degenerate case `s = 0`, `q = 0`. -/
theorem shell_compress_iff (s : Int) {p q a : Quaternion} (hp : p.IsPure) (hq : q.IsPure)
    (ha : a.IsPure) :
    let t := (s.mul s).add ((a.dot a).mul (p.dot q))
    Iff (∀ v : Quaternion,
        Eq (shell s p a (shell s q a (shell s p a v))) (scale (t.add t) (shell s p a v)))
      (Or (Eq (s.mul s) ((p.dot p).mul (a.dot a))) (And (Eq s Int.zero) (Eq q zero))) :=
  let t := (s.mul s).add ((a.dot a).mul (p.dot q))
  let δ := (s.mul s).sub ((p.dot p).mul (a.dot a))
  let goal := Or (Eq (s.mul s) ((p.dot p).mul (a.dot a))) (And (Eq s Int.zero) (Eq q zero))
  Iff.intro
    (fun H =>
      let W := fun v : Quaternion => scale δ (shell s.neg q a v)
      have hW : ∀ v, Eq (W v) zero := fun v =>
        eq_zero_of_add_eq_self ((shell_compress s hp hq ha v).symm.trans (H v))
      have both := defect_facts δ s hq ha
      have facts := both.left
      have zeros := both.right
      have hS : Eq (defectS s q a (W one) (W unitI) (W unitJ)) (defectS s q a zero zero zero) :=
        (congrArg (fun w => defectS s q a w (W unitI) (W unitJ)) (hW one)).trans
          (Eq.map₂ (defectS s q a zero) (hW unitI) (hW unitJ))
      let X := fun (u w1 wu : Quaternion) => (wu.sub (u.mul w1)).mul a.conj
      have hJ := Eq.map₂ (fun w1 wu => (X unitJ w1 wu).z) (hW one) (hW unitJ)
      have hIz := Eq.map₂ (fun w1 wu => (X unitI w1 wu).z.neg) (hW one) (hW unitI)
      have hIy := Eq.map₂ (fun w1 wu => (X unitI w1 wu).y) (hW one) (hW unitI)
      let cancel := fun {c : Int} (h : Eq ((Int.one.add Int.one).mul c) Int.zero) =>
        (Int.mul_eq_zero.mp h).elim (fun e => False.elim (two_ne_zero e)) (fun e => e)
      have hδss := cancel (facts.left.symm.trans (hS.trans zeros.left))
      have ofδ : Eq δ Int.zero → goal := fun e => Or.inl (Int.sub_eq_zero.mp e)
      have caseS : Eq s Int.zero → goal := fun hs0 =>
        have onShell : Eq (a.dot a) Int.zero → Eq (s.mul s) ((p.dot p).mul (a.dot a)) := fun hN =>
          ((Eq.map₂ Int.mul hs0 hs0).trans (Int.zero_mul Int.zero)).trans
            ((congrArg (p.dot p).mul hN).trans (Int.mul_zero (p.dot p))).symm
        have coord : ∀ {c : Int}, Eq ((δ.mul (a.dot a)).mul c) Int.zero → Or goal (Eq c Int.zero) :=
          fun h => (Int.mul_eq_zero.mp h).elim
            (fun h' => (Int.mul_eq_zero.mp h').elim (fun e => Or.inl (ofδ e))
              (fun hN => Or.inl (Or.inl (onShell hN))))
            Or.inr
        have h1 := coord (cancel (facts.right.left.symm.trans (hJ.trans zeros.right.left)))
        have h2 := coord (cancel (facts.right.right.left.symm.trans
          (hIz.trans zeros.right.right.left)))
        have h3 := coord (cancel (facts.right.right.right.symm.trans
          (hIy.trans zeros.right.right.right)))
        h1.elim id (fun e1 => h2.elim id (fun e2 => h3.elim id (fun e3 =>
          Or.inr (And.intro hs0 (ext hq e1 e2 e3)))))
      (Int.mul_eq_zero.mp hδss).elim
        (fun hδs => (Int.mul_eq_zero.mp hδs).elim ofδ caseS) caseS)
    (fun h => h.elim
      (fun hs v => shell_compress_of_eq s hp hq ha hs v)
      (fun hz v =>
        have vanish : Eq (shell s.neg q a v) zero :=
          Eq.subst (motive := fun s' : Int => Eq (shell s'.neg q a v) zero) hz.left.symm
            (Eq.subst (motive := fun q' : Quaternion => Eq (shell Int.zero.neg q' a v) zero)
              hz.right.symm (shell_neg_zero_zero a v))
        (shell_compress s hp hq ha v).trans
          ((congrArg (fun w => (scale (t.add t) (shell s p a v)).add (scale δ w)) vanish).trans
            (add_scale_zero_right _ δ))))

private def altProd (P Q R : Quaternion) : Quaternion :=
  ((((P.mul Q).mul R).add ((Q.mul R).mul P)).add ((R.mul P).mul Q)).sub
    ((((P.mul R).mul Q).add ((R.mul Q).mul P)).add ((Q.mul P).mul R))

private def caltProd (P Q R : Coordinates) : Coordinates :=
  csub (cadd (cadd ((P.mul Q).mul R) ((Q.mul R).mul P)) ((R.mul P).mul Q))
    (cadd (cadd ((P.mul R).mul Q) ((R.mul Q).mul P)) ((Q.mul P).mul R))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem alt_prod_mk (x1 x2 x3 y1 y2 y3 z1 z2 z3 : Int) :
    let p := Quaternion.mk Int.zero x1 x2 x3
    let q := Quaternion.mk Int.zero y1 y2 y3
    let r := Quaternion.mk Int.zero z1 z2 z3
    let d := p.dot (q.mul r)
    let d3 := (d.add d).add d
    Eq (altProd p q r) (scalar (d3.add d3).neg) :=
  let values := triple x1 x2 x3 (triple y1 y2 y3 (triple z1 z2 z3 .nil))
  let P := ShellCertificate.pure Nat.zero
  let Q := ShellCertificate.pure n3
  let R := ShellCertificate.pure (n3.add n3)
  let D := P.dot (Q.mul R)
  let D3 := (D.add D).add D
  let lhs := caltProd P Q R
  let rhs := Coordinates.scalar (D3.add D3).neg
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem sum_mul_mk (y1 y2 y3 y4 y5 y6 x : Quaternion) :
    Eq ((((y1.mul x).add (y2.mul x)).add (y3.mul x)).sub
        (((y4.mul x).add (y5.mul x)).add (y6.mul x)))
      ((((y1.add y2).add y3).sub ((y4.add y5).add y6)).mul x) :=
  let values := quad y1 (quad y2 (quad y3 (quad y4 (quad y5 (quad y6 (quad x .nil))))))
  let n24 := n12.add n12
  let Y1 := Coordinates.variables Nat.zero
  let Y2 := Coordinates.variables n4
  let Y3 := Coordinates.variables n8
  let Y4 := Coordinates.variables n12
  let Y5 := Coordinates.variables (n12.add n4)
  let Y6 := Coordinates.variables (n12.add n8)
  let X := Coordinates.variables n24
  let lhs := csub (cadd (cadd (Y1.mul X) (Y2.mul X)) (Y3.mul X))
    (cadd (cadd (Y4.mul X) (Y5.mul X)) (Y6.mul X))
  let rhs := (csub (cadd (cadd Y1 Y2) Y3) (cadd (cadd Y4 Y5) Y6)).mul X
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem alt_glue_mk (α : Int) (y1 y2 y3 y4 y5 y6 a : Quaternion) :
    let Z := fun y : Quaternion => scale α.neg (y.mul a)
    Eq ((((Z y1).add (Z y2)).add (Z y3)).sub (((Z y4).add (Z y5)).add (Z y6)))
      (scale α.neg ((((y1.add y2).add y3).sub ((y4.add y5).add y6)).mul a)) :=
  let values := Values.cons α (quad y1 (quad y2 (quad y3 (quad y4 (quad y5 (quad y6
    (quad a .nil)))))))
  let A' := Expr.var Nat.zero
  let n1 := Nat.zero.succ
  let n24 := n12.add n12
  let Y1 := Coordinates.variables n1
  let Y2 := Coordinates.variables (n4.add n1)
  let Y3 := Coordinates.variables (n8.add n1)
  let Y4 := Coordinates.variables (n12.add n1)
  let Y5 := Coordinates.variables ((n12.add n4).add n1)
  let Y6 := Coordinates.variables ((n12.add n8).add n1)
  let Av := Coordinates.variables (n24.add n1)
  let Z := fun Y : Coordinates => (Y.mul Av).scale A'.neg
  let lhs := csub (cadd (cadd (Z Y1) (Z Y2)) (Z Y3)) (cadd (cadd (Z Y4) (Z Y5)) (Z Y6))
  let rhs := ((csub (cadd (cadd Y1 Y2) Y3) (cadd (cadd Y4 Y5) Y6)).mul Av).scale A'.neg
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem alt_scale_mk (α d : Int) (x a : Quaternion) :
    let d3 := (d.add d).add d
    let l := α.mul d
    let t := (l.add l).add l
    Eq (scale α.neg ((scale (d3.add d3).neg x).mul a)) (scale (t.add t) (x.mul a)) :=
  let values := Values.cons α (Values.cons d (quad x (quad a .nil)))
  let A' := Expr.var Nat.zero
  let D := Expr.var Nat.zero.succ
  let X := Coordinates.variables Nat.zero.succ.succ
  let Av := Coordinates.variables (n4.add Nat.zero.succ.succ)
  let D3 := (D.add D).add D
  let L := A'.mul D
  let T := (L.add L).add L
  let lhs := ((X.scale (D3.add D3).neg).mul Av).scale A'.neg
  let rhs := (X.mul Av).scale (T.add T)
  ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

private theorem triple_of_isPure {a : Quaternion} (ha : a.IsPure) (p q r x : Quaternion) :
    Eq ((p.mul ((q.mul ((r.mul x).mul a)).mul a)).mul a)
      (scale (a.dot a).neg ((p.mul (q.mul (r.mul x))).mul a)) :=
  let W := r.mul x
  have inner : Eq ((q.mul (W.mul a)).mul a) (scale (a.dot a).neg (q.mul W)) :=
    (congrArg (fun t : Quaternion => t.mul a) (mul_assoc q W a).symm).trans
      (mul_mul_of_isPure ha (q.mul W))
  (congrArg (fun t : Quaternion => (p.mul t).mul a) inner).trans
    ((congrArg (fun t : Quaternion => t.mul a) (scale_mul_right (a.dot a).neg p (q.mul W))).trans
      (scale_mul_left (a.dot a).neg (p.mul (q.mul W)) a))

private theorem mul_mul_mul_assoc (A B C x : Quaternion) :
    Eq (A.mul (B.mul (C.mul x))) (((A.mul B).mul C).mul x) :=
  (congrArg A.mul (mul_assoc B C x).symm).trans
    ((mul_assoc A (B.mul C) x).symm.trans
      (congrArg (fun t : Quaternion => t.mul x) (mul_assoc A B C).symm))

/-- Oriented axis identity for arbitrary `p`, `q`, `r`. For pure `a`, any quaternions `p`, `q`,
`r`, `x` and the maps `u_c v = (c v) a`, the three cyclic compositions minus the three reverse
ones equal `-N(a) (A x) a`, where `A` is the alternating sum of the six ordered products of
`p`, `q`, `r`. -/
theorem oriented_axis_general {a : Quaternion} (ha : a.IsPure) (p q r x : Quaternion) :
    let u := fun c v : Quaternion => (c.mul v).mul a
    let A := ((((p.mul q).mul r).add ((q.mul r).mul p)).add ((r.mul p).mul q)).sub
      ((((p.mul r).mul q).add ((r.mul q).mul p)).add ((q.mul p).mul r))
    Eq ((((u p (u q (u r x))).add (u q (u r (u p x)))).add (u r (u p (u q x)))).sub
        (((u p (u r (u q x))).add (u r (u q (u p x)))).add (u q (u p (u r x)))))
      (scale (a.dot a).neg ((A.mul x).mul a)) :=
  let α := a.dot a
  let Y := fun A B C : Quaternion => A.mul (B.mul (C.mul x))
  let Z := fun A B C : Quaternion => (A.mul B).mul C
  let T := fun A B C : Quaternion => triple_of_isPure ha A B C x
  let M := fun A B C : Quaternion => mul_mul_mul_assoc A B C x
  have assoc : Eq ((((Y p q r).add (Y q r p)).add (Y r p q)).sub
      (((Y p r q).add (Y r q p)).add (Y q p r))) ((altProd p q r).mul x) :=
    (Eq.map₂ sub (Eq.map₂ add (Eq.map₂ add (M p q r) (M q r p)) (M r p q))
      (Eq.map₂ add (Eq.map₂ add (M p r q) (M r q p)) (M q p r))).trans
      (sum_mul_mk (Z p q r) (Z q r p) (Z r p q) (Z p r q) (Z r q p) (Z q p r) x)
  (Eq.map₂ sub (Eq.map₂ add (Eq.map₂ add (T p q r) (T q r p)) (T r p q))
    (Eq.map₂ add (Eq.map₂ add (T p r q) (T r q p)) (T q p r))).trans
    ((alt_glue_mk α (Y p q r) (Y q r p) (Y r p q) (Y p r q) (Y r q p) (Y q p r) a).trans
      (congrArg (fun w : Quaternion => scale α.neg (w.mul a)) assoc))

/-- Oriented axis identity. For pure `p`, `q`, `r`, `a`, any quaternion `x` and the maps
`u_c v = (c v) a`, the three cyclic compositions minus the three reverse ones satisfy
`u_p u_q u_r x + u_q u_r u_p x + u_r u_p u_q x - u_p u_r u_q x - u_r u_q u_p x - u_q u_p u_r x
  = 6 N(a) [p, q, r] (x a)`,
where `[p, q, r] = p · (q r)` is the triple product of the three pure quaternions. -/
theorem oriented_axis {p q r a : Quaternion} (hp : p.IsPure) (hq : q.IsPure) (hr : r.IsPure)
    (ha : a.IsPure) (x : Quaternion) :
    let u := fun c v : Quaternion => (c.mul v).mul a
    let l := (a.dot a).mul (p.dot (q.mul r))
    let t := (l.add l).add l
    Eq ((((u p (u q (u r x))).add (u q (u r (u p x)))).add (u r (u p (u q x)))).sub
        (((u p (u r (u q x))).add (u r (u q (u p x)))).add (u q (u p (u r x)))))
      (scale (t.add t) (x.mul a)) :=
  let α := a.dot a
  let d := p.dot (q.mul r)
  let d3 := (d.add d).add d
  let stmt := fun P Q R : Quaternion =>
    let d := P.dot (Q.mul R)
    let d3 := (d.add d).add d
    Eq (altProd P Q R) (scalar (d3.add d3).neg)
  have alt : stmt p q r :=
    Eq.subst (motive := fun P => stmt P q r) (eq_mk_of_isPure hp).symm
      (Eq.subst (motive := fun Q => stmt (Quaternion.mk Int.zero p.x p.y p.z) Q r)
        (eq_mk_of_isPure hq).symm
        (Eq.subst (motive := fun R => stmt (Quaternion.mk Int.zero p.x p.y p.z)
            (Quaternion.mk Int.zero q.x q.y q.z) R)
          (eq_mk_of_isPure hr).symm
          (alt_prod_mk p.x p.y p.z q.x q.y q.z r.x r.y r.z)))
  (oriented_axis_general ha p q r x).trans
    ((congrArg (fun w : Quaternion => scale α.neg ((w.mul x).mul a))
        alt).trans
      ((congrArg (fun w : Quaternion => scale α.neg (w.mul a)) (scalar_mul (d3.add d3).neg x)).trans
        (alt_scale_mk α d x a)))

end Quaternion
end Omega

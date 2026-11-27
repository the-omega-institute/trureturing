/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
public import OmegaMath.Harmonic.HurwitzFreeGroup.Residue
public import OmegaMath.Algebra.Quaternion

/-!
Omega original.

The split representation of integer Hamilton quaternions modulo five and
the contraction law for products of rank-one split matrices.
-/

noncomputable section

@[expose] public section

namespace Omega.Hurwitz.FreeGroup

def five : Nat := Nat.one.succ.succ.succ.succ

def coordinates (q : Quaternion) : Coordinates := ⟨q.w, q.x, q.y, q.z⟩

def generatorQuat (g : Generator) : Quaternion :=
  ⟨g.coordinates.w, g.coordinates.x, g.coordinates.y, g.coordinates.z⟩

def quaternionSplit5 (q : Quaternion) : Matrix5 := split5 (coordinates q)

private theorem matrixExt {A B : Matrix5} (ha : Eq A.a B.a) (hb : Eq A.b B.b)
    (hc : Eq A.c B.c) (hd : Eq A.d B.d) : Eq A B :=
  (Eq.map₂ (fun a b => Matrix5.mk a b A.c A.d) ha hb).trans
    (Eq.map₂ (Matrix5.mk B.a B.b) hc hd)

private theorem reduce_mul (A B : Mat2) : Eq (reduce (A.mul B)) ((reduce A).mul (reduce B)) :=
  let entry := fun (a b c d : Int) =>
    (Residue.ofInt_add (a.mul c) (b.mul d)).trans
      (Eq.map₂ Residue.add (Residue.ofInt_mul a c) (Residue.ofInt_mul b d))
  matrixExt (entry A.a A.b B.a B.c) (entry A.a A.b B.b B.d)
    (entry A.c A.d B.a B.c) (entry A.c A.d B.b B.d)

private def correction (p q : Quaternion) : Mat2 :=
  let diag := (p.x.mul q.x).add (p.z.mul q.z)
  let off := (p.x.mul q.z).sub (p.z.mul q.x)
  ⟨diag, off, off.neg, diag⟩

open Quaternion.Polynomial (Expr Values)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
/-- The integer split products have an explicit entrywise defect divisible by five. -/
private theorem split_mul_defect (p q : Quaternion) :
    Eq ((split (coordinates p)).mul (split (coordinates q)))
      ((split (coordinates (p.mul q))).add ((correction p q).scale (Int.ofNat five))) :=
  let values := Values.cons p.w (.cons p.x (.cons p.y (.cons p.z
    (.cons q.w (.cons q.x (.cons q.y (.cons q.z .nil)))))))
  let two := Expr.one.add .one
  let fiveExpr := (two.mul two).add .one
  let P := Quaternion.Polynomial.Coordinates.variables Nat.zero
  let Q := Quaternion.Polynomial.Coordinates.variables Nat.one.succ.succ.succ
  let A := fun r : Quaternion.Polynomial.Coordinates => r.w.add (two.mul r.x)
  let B := fun r : Quaternion.Polynomial.Coordinates => r.y.add (two.mul r.z)
  let C := fun r : Quaternion.Polynomial.Coordinates => (two.mul r.z).sub r.y
  let D := fun r : Quaternion.Polynomial.Coordinates => r.w.sub (two.mul r.x)
  let dot := fun (a b c d : Expr) => (a.mul c).add (b.mul d)
  let R := P.mul Q
  let diag := (P.x.mul Q.x).add (P.z.mul Q.z)
  let off := (P.x.mul Q.z).sub (P.z.mul Q.x)
  Mat2.ext
    ((dot (A P) (B P) (A Q) (C Q)).sound ((A R).add (fiveExpr.mul diag)) values rfl)
    ((dot (A P) (B P) (B Q) (D Q)).sound ((B R).add (fiveExpr.mul off)) values rfl)
    ((dot (C P) (D P) (A Q) (C Q)).sound ((C R).add (fiveExpr.mul off.neg)) values rfl)
    ((dot (C P) (D P) (B Q) (D Q)).sound ((D R).add (fiveExpr.mul diag)) values rfl)

theorem residue_five_mul (z : Int) : Eq (Residue.ofInt ((Int.ofNat five).mul z)) .zero :=
  (Residue.ofInt_mul (Int.ofNat five) z).trans (Residue.zero_mul (Residue.ofInt z))

private theorem reduce_add_correction (A C : Mat2) :
    Eq (reduce (A.add (C.scale (Int.ofNat five)))) (reduce A) :=
  let entry := fun (a c : Int) =>
    (Residue.ofInt_add a ((Int.ofNat five).mul c)).trans
      (congrArg (Residue.ofInt a).add (residue_five_mul c))
  matrixExt (entry A.a C.a) (entry A.b C.b) (entry A.c C.c) (entry A.d C.d)

/-- Reduction of the split matrix intertwines Hamilton and matrix multiplication. -/
theorem quaternionSplit5_mul (p q : Quaternion) :
    Eq (quaternionSplit5 (p.mul q)) ((quaternionSplit5 p).mul (quaternionSplit5 q)) :=
  let A := split (coordinates p)
  let B := split (coordinates q)
  let C := split (coordinates (p.mul q))
  (reduce_add_correction C (correction p q)).symm.trans
    ((congrArg reduce (split_mul_defect p q).symm).trans (reduce_mul A B))

def matrixOne : Matrix5 := ⟨.one, .zero, .zero, .one⟩

theorem matrix_mul_one (A : Matrix5) : Eq (A.mul matrixOne) A :=
  let left := fun a b : Residue =>
    Eq.map₂ Residue.add (Residue.mul_one a) (rfl : Eq (b.mul .zero) .zero)
  let right := fun a b : Residue =>
    (Eq.map₂ Residue.add (rfl : Eq (a.mul .zero) .zero) (Residue.mul_one b)).trans
      (Residue.zero_add b)
  matrixExt (left A.a A.b) (right A.a A.b) (left A.c A.d) (right A.c A.d)

/-- The row-column pairing in the product of two outer products. -/
def contraction (s t u v : Residue) : Residue := (s.mul u).add (t.mul v)

private theorem outer_entry (u s t v w r : Residue) :
    Eq (((u.mul s).mul (v.mul r)).add ((u.mul t).mul (w.mul r)))
      (u.mul ((contraction s t v w).mul r)) :=
  let term := fun a b : Residue =>
    (Residue.mul_assoc u a (b.mul r)).trans
      (congrArg u.mul (Residue.mul_assoc a b r).symm)
  (Eq.map₂ Residue.add (term s v) (term t w)).trans
    ((Residue.mul_add u ((s.mul v).mul r) ((t.mul w).mul r)).symm.trans
      (congrArg u.mul (Residue.add_mul (s.mul v) (t.mul w) r).symm))

theorem outer_mul (u v s t u' v' s' t' : Residue) :
    Eq ((Matrix5.outer u v s t).mul (Matrix5.outer u' v' s' t'))
      (Matrix5.outer u v ((contraction s t u' v').mul s') ((contraction s t u' v').mul t')) :=
  matrixExt (outer_entry u s t u' v' s') (outer_entry u s t u' v' t')
    (outer_entry v s t u' v' s') (outer_entry v s t u' v' t')

theorem outer_zero_row (u v : Residue) : Eq (Matrix5.outer u v .zero .zero).isZero .true :=
  Omega.rfl

private def both (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) .false b a

private theorem both_true (a b : Bool) (h : Eq (both a b) .true) :
    And (Eq a .true) (Eq b .true) :=
  (Bool.rec (motive := fun a => Eq (both a b) .true → And (Eq a .true) (Eq b .true))
    (fun h => False.elim (Residue.false_ne_true h)) (fun h => And.intro rfl h) a) h

theorem entries_zero {A : Matrix5} (h : Eq A.isZero .true) :
    And (Eq A.a .zero) (And (Eq A.b .zero) (And (Eq A.c .zero) (Eq A.d .zero))) :=
  have a := both_true A.a.isZero (both A.b.isZero (both A.c.isZero A.d.isZero)) h
  have b := both_true A.b.isZero (both A.c.isZero A.d.isZero) a.right
  have c := both_true A.c.isZero A.d.isZero b.right
  And.intro (Residue.zero_of_isZero a.left)
    (And.intro (Residue.zero_of_isZero b.left)
      (And.intro (Residue.zero_of_isZero c.left) (Residue.zero_of_isZero c.right)))

theorem bool_false_of_not_true (b : Bool) (h : Not (Eq b .true)) : Eq b .false :=
  (Bool.rec (motive := fun b => Not (Eq b .true) → Eq b .false)
    (fun _ => rfl) (fun h => False.elim (h rfl)) b) h

end Omega.Hurwitz.FreeGroup

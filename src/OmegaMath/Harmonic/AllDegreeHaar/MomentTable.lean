/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
public import OmegaMath.Harmonic.PiFreeHaar.Moments
import OmegaMath.Algebra.Quaternion.Polynomial

/-!
Omega original.

The mixed moments of powers of the squared scalar coordinate and even characters.
Their explicit factorial products satisfy the character recurrence in every degree.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.AllDegreeHaar.MomentTable

open PiFreeHaar (haarKappaMoment haarKappaStep haarKappaMoment_succ haarKappaMoment_0)
open PiFreeHaar.Numerals (two)
open IntRatio (Equivalent equivalent_refl ofInt value)

def four : Int := Int.ofNat PiFreeHaar.Numerals.four

/-- The scalar moment in degree `j` times `(2r+1) j(j-1)…(j-r+1) / ((j+2)…(j+r+1))`.
Both products start at one for `r = 0`. -/
def expected (j r : Nat) : IntRatio :=
  (haarKappaMoment j).mul (value (numerator j r) (rise j r))
where
  odd (r : Nat) : Int := (Int.two.mul (Int.ofNat r)).add Int.one
  fall (j r : Nat) : Int :=
    Nat.rec Int.one (fun k product => product.mul ((Int.ofNat j).sub (Int.ofNat k))) r
  rise (j r : Nat) : Nat :=
    Nat.rec Nat.one (fun k product => product.mul (j.add k).succ.succ) r
  numerator (j r : Nat) : Int := (odd r).mul (fall j r)

open expected (odd fall rise numerator)

private def scaled (moment : IntRatio) (n : Int) (d : Nat) : IntRatio :=
  moment.mul (value n d)

private theorem fall_shift (j r : Nat) :
    Eq (fall j.succ r.succ) ((Int.ofNat j.succ).mul (fall j r)) :=
  Nat.rec (motive := fun r => Eq (fall j.succ r.succ) ((Int.ofNat j.succ).mul (fall j r)))
    ((Int.one_mul _).trans ((Int.add_zero _).trans (Int.mul_one (Int.ofNat j.succ)).symm))
    (fun r ih =>
      have difference := (Int.subNatNat_eq_coe (m := j.succ) (n := r.succ)).symm.trans
        ((Eq.map₂ Int.subNatNat (Nat.add_one j).symm (Nat.add_one r).symm).trans
          ((Int.subNatNat_add_add j r Nat.one).trans (Int.subNatNat_eq_coe (m := j) (n := r))))
      (Eq.map₂ Int.mul ih difference).trans
        (Int.mul_assoc (Int.ofNat j.succ) (fall j r) ((Int.ofNat j).sub (Int.ofNat r)))) r

private theorem rise_shift (j r : Nat) :
    Eq ((rise j.succ r).mul j.succ.succ) (rise j r.succ) :=
  Nat.rec (motive := fun r => Eq ((rise j.succ r).mul j.succ.succ) (rise j r.succ))
    (congrArg (fun t : Nat => Nat.one.mul t.succ.succ) (Nat.add_zero j).symm)
    (fun r ih =>
      (Nat.mul_right_comm (rise j.succ r) (j.succ.add r).succ.succ j.succ.succ).trans
        (Eq.map₂ Nat.mul ih (congrArg (fun n : Nat => n.succ.succ)
          ((Nat.succ_add j r).trans (Nat.add_succ j r).symm)))) r

private theorem mul_ne_zero {a b : Nat} (ha : Not (Eq a Nat.zero)) (hb : Not (Eq b Nat.zero)) :
    Not (Eq (a.mul b) Nat.zero) :=
  fun h => ((Nat.mul_eq_zero).mp h).elim ha hb

private theorem rise_ne_zero (j r : Nat) : Not (Eq (rise j r) Nat.zero) :=
  Nat.rec (motive := fun r => Not (Eq (rise j r) Nat.zero))
    (Nat.succ_ne_zero Nat.zero) (fun k ih => mul_ne_zero ih (Nat.succ_ne_zero (j.add k).succ)) r

private theorem equivalent_of_eq {x y : IntRatio} (h : Eq x y) : Equivalent x y :=
  Eq.subst (motive := Equivalent x) h (equivalent_refl x)

private theorem scaled_mul (m : IntRatio) (a b : Int) (d e : Nat) :
    Equivalent ((scaled m a d).mul (value b e)) (scaled m (a.mul b) (d.mul e)) :=
  (IntRatio.mul_assoc m (value a d) (value b e)).trans
    (equivalent_of_eq (congrArg m.mul (IntRatio.value_mul a b d e)))

private theorem scaled_int_mul (m : IntRatio) (a b : Int) (d : Nat) :
    Equivalent ((ofInt a).mul (scaled m b d)) (scaled m (a.mul b) d) :=
  (IntRatio.mul_comm (ofInt a) (scaled m b d)).trans
    ((scaled_mul m b a d Nat.one).trans
      (equivalent_of_eq (Eq.map₂ (scaled m) (Int.mul_comm b a) (Nat.mul_one d))))

private theorem scaled_rescale (m : IntRatio) (n : Int) (d k : Nat) (hk : Not (Eq k Nat.zero)) :
    Equivalent (scaled m n d) (scaled m (n.mul (Int.ofNat k)) (d.mul k)) :=
  IntRatio.mul_congr (equivalent_refl m) (IntRatio.value_scale_of_ne_zero n d k hk).symm

private theorem scaled_neg (m : IntRatio) (n : Int) (d : Nat) :
    Eq (scaled m n.neg d) (scaled m n d).neg :=
  IntRatio.rec (motive := fun m => Eq (scaled m n.neg d) (scaled m n d).neg)
    rfl
    (fun a b => Nat.rec (motive := fun d =>
        Eq (scaled (IntRatio.fraction a b) n.neg d) (scaled (IntRatio.fraction a b) n d).neg)
      rfl
      (fun d _ => congrArg (fun x => IntRatio.fraction x (IntRatio.mulDenPred b d))
        (Int.mul_neg a n)) d) m

private theorem scaled_sub_same (m : IntRatio) (a b : Int) (d : Nat) :
    Equivalent ((scaled m a d).sub (scaled m b d)) (scaled m (a.sub b) d) :=
  (IntRatio.add_congr (equivalent_refl (scaled m a d))
    (equivalent_of_eq (scaled_neg m b d).symm)).trans
    ((IntRatio.mul_add m (value a d) (value b.neg d)).symm.trans
      (IntRatio.mul_congr (equivalent_refl m) (IntRatio.value_add_same a b.neg d)))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
/-- Four times the next scalar moment absorbs the scalar recurrence factor. -/
private theorem four_mul_next (j : Nat) (n : Int) (d : Nat) :
    Equivalent ((ofInt four).mul (scaled (haarKappaMoment j.succ) n d))
      (scaled (haarKappaMoment j) ((Int.two.mul (odd j)).mul n) (d.mul j.succ.succ)) :=
  let m := haarKappaMoment j
  let den := two.mul j.succ.succ
  let a := (Int.two.mul (odd j)).mul n
  let b := d.mul j.succ.succ
  have shift := IntRatio.mul_congr_left (haarKappaMoment_succ j) (value n d)
  have combine := scaled_mul m (odd j) n den d
  have multiply := scaled_int_mul m four ((odd j).mul n) (den.mul d)
  have numEq : Eq (four.mul ((odd j).mul n)) (a.mul Int.two) :=
    (Int.mul_right_comm Int.two Int.two ((odd j).mul n)).trans
      (congrArg (fun z : Int => z.mul Int.two) (Int.mul_assoc Int.two (odd j) n).symm)
  have denEq : Eq (den.mul d) (b.mul two) :=
    (Nat.mul_comm den d).trans
      ((congrArg d.mul (Nat.mul_comm two j.succ.succ)).trans (Nat.mul_assoc d j.succ.succ two).symm)
  (IntRatio.mul_congr (equivalent_refl (ofInt four)) (shift.trans combine)).trans
    (multiply.trans ((equivalent_of_eq (Eq.map₂ (scaled m) numEq denEq)).trans
      (scaled_rescale m a b two (Nat.succ_ne_zero Nat.one)).symm))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem base (j : Nat) : Equivalent (haarKappaMoment j) (expected j Nat.zero) :=
  (IntRatio.mul_one (haarKappaMoment j)).symm

open Quaternion.Polynomial (Expr Values)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem first_numerator (j : Nat) :
    Eq (((Int.two.mul (odd j)).mul Int.one).sub (Int.ofNat j.succ.succ)) (numerator j Nat.one) :=
  let x := Expr.var Nat.zero
  let two := Expr.one.double
  let three := two.add Expr.one
  Expr.sound (((two.mul ((two.mul x).add .one)).mul .one).sub (x.add two))
    (three.mul (Expr.one.mul x)) (.cons (Int.ofNat j) .nil) rfl

theorem first (j : Nat) :
    Equivalent (((ofInt four).mul (haarKappaMoment j.succ)).sub (haarKappaMoment j))
      (expected j Nat.one) :=
  let m := haarKappaMoment j
  let d := j.succ.succ
  let a := (Int.two.mul (odd j)).mul Int.one
  have left := (IntRatio.mul_congr (equivalent_refl (ofInt four))
    (IntRatio.mul_one (haarKappaMoment j.succ)).symm).trans (four_mul_next j Int.one Nat.one)
  have leftDen := equivalent_of_eq (congrArg (scaled m a) (Nat.one_mul d))
  have right := (IntRatio.mul_one m).symm.trans
    ((scaled_rescale m Int.one Nat.one d (Nat.succ_ne_zero j.succ)).trans
      (equivalent_of_eq (Eq.map₂ (scaled m) (Int.one_mul (Int.ofNat d)) (Nat.one_mul d))))
  (IntRatio.sub_congr (left.trans leftDen) right).trans
    ((scaled_sub_same m a (Int.ofNat d) d).trans
      (equivalent_of_eq (Eq.map₂ (scaled m) (first_numerator j) ((Nat.one_mul d).symm.trans
        (congrArg (fun t : Nat => Nat.one.mul t.succ.succ) (Nat.add_zero j).symm)))))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
/-- The numerator identity after moving all four terms to the rising product in degree `r+2`. -/
private theorem step_numerator (j r : Nat) :
    let p := (j.add r).succ.succ
    let q := p.succ
    Eq ((((Int.two.mul (odd j)).mul (numerator j.succ r.succ)).sub
          ((Int.two.mul (numerator j r.succ)).mul (Int.ofNat q))).sub
        ((numerator j r).mul (Int.ofNat (p.mul q))))
      (numerator j r.succ.succ) :=
  let p := (j.add r).succ.succ
  let q := p.succ
  let b := (Int.two.mul (numerator j r.succ)).mul (Int.ofNat q)
  let c := (numerator j r).mul (Int.ofNat (p.mul q))
  let x := Expr.var Nat.zero
  let y := Expr.var Nat.one
  let f := Expr.var Nat.one.succ
  let two := Expr.one.double
  let three := two.add Expr.one
  let y1 := y.add Expr.one
  let y2 := y.add two
  let oddExpr := fun t : Expr => (two.mul t).add Expr.one
  let pExpr := (x.add y).add two
  let qExpr := (x.add y).add three
  let fall1 := f.mul (x.sub y)
  let fall2 := fall1.mul (x.sub y1)
  let aExpr := (two.mul (oddExpr x)).mul ((oddExpr y1).mul ((x.add Expr.one).mul f))
  let bExpr := (two.mul ((oddExpr y1).mul fall1)).mul qExpr
  let cExpr := ((oddExpr y).mul f).mul (pExpr.mul qExpr)
  (congrArg (fun t : Int => (((Int.two.mul (odd j)).mul
    ((odd r.succ).mul t)).sub b).sub c) (fall_shift j r)).trans
    (Expr.sound ((aExpr.sub bExpr).sub cExpr) ((oddExpr y2).mul fall2)
      (.cons (Int.ofNat j) (.cons (Int.ofNat r) (.cons (fall j r) .nil))) rfl)

theorem step (j r : Nat) :
    Equivalent ((((ofInt four).mul (expected j.succ r.succ)).sub
      ((ofInt Int.two).mul (expected j r.succ))).sub (expected j r))
      (expected j r.succ.succ) :=
  let m := haarKappaMoment j
  let p := (j.add r).succ.succ
  let q := p.succ
  let d := rise j r.succ.succ
  let a := (Int.two.mul (odd j)).mul (numerator j.succ r.succ)
  let b := Int.two.mul (numerator j r.succ)
  let c := numerator j r
  let b' := b.mul (Int.ofNat q)
  let c' := c.mul (Int.ofNat (p.mul q))
  have left := (four_mul_next j (numerator j.succ r.succ) (rise j.succ r.succ)).trans
    (equivalent_of_eq (congrArg (scaled m a) (rise_shift j r.succ)))
  have lastFactor := congrArg (fun t : Nat => (rise j r.succ).mul t.succ.succ) (Nat.add_succ j r).symm
  have middle := (scaled_int_mul m Int.two (numerator j r.succ) (rise j r.succ)).trans
    ((scaled_rescale m b (rise j r.succ) q (Nat.succ_ne_zero p)).trans
      (equivalent_of_eq (congrArg (scaled m b') lastFactor)))
  have right := (scaled_rescale m c (rise j r) (p.mul q)
    (mul_ne_zero (Nat.succ_ne_zero (j.add r).succ) (Nat.succ_ne_zero p))).trans
      (equivalent_of_eq (congrArg (scaled m c') ((Nat.mul_assoc (rise j r) p q).symm.trans lastFactor)))
  (IntRatio.sub_congr ((IntRatio.sub_congr left middle).trans (scaled_sub_same m a b' d)) right).trans
    ((scaled_sub_same m (a.sub b') c' d).trans
      (equivalent_of_eq (congrArg (fun n => scaled m n d) (step_numerator j r))))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
private theorem fall_axis (r : Nat) : Eq (fall Nat.zero r.succ) Int.zero :=
  Nat.rec (motive := fun r => Eq (fall Nat.zero r.succ) Int.zero) rfl
    (fun r ih =>
      let diff := Int.zero.sub (Int.ofNat r.succ)
      (congrArg (fun t : Int => t.mul diff) ih).trans (Int.zero_mul diff)) r

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem axis (r : Nat) :
    Equivalent (expected Nat.zero r)
      (Nat.rec (motive := fun _ => IntRatio) (ofInt Int.one) (fun _ _ => ofInt Int.zero) r) :=
  Nat.rec (motive := fun r =>
      Equivalent (expected Nat.zero r)
        (Nat.rec (motive := fun _ => IntRatio) (ofInt Int.one) (fun _ _ => ofInt Int.zero) r))
    ((base Nat.zero).symm.trans haarKappaMoment_0)
    (fun r _ =>
      let d := rise Nat.zero r.succ
      have zero := (congrArg (odd r.succ).mul (fall_axis r)).trans (Int.mul_zero (odd r.succ))
      (equivalent_of_eq (congrArg (fun n => scaled (haarKappaMoment Nat.zero) n d) zero)).trans
        (IntRatio.mul_congr haarKappaMoment_0 (IntRatio.value_zero d (rise_ne_zero Nat.zero r.succ)))) r

end Omega.Harmonic.AllDegreeHaar.MomentTable

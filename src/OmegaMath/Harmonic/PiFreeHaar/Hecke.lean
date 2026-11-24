/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Geometry.BargmannGram.Fractions
import OmegaMath.Geometry.BargmannGram.Identities
import OmegaMath.Geometry.BargmannGram.Polynomial
public import OmegaMath.Harmonic.PiFreeHaar.Moments

/-!
Omega original.

The six norm-five spinors act on the first character by an exact rational eigenvalue.
-/

noncomputable section

@[expose] public section

namespace Omega.Harmonic.PiFreeHaar

open Geometry.BargmannGram
open IntRatio (Equivalent)
open Polynomial (Expr)

namespace HeckeT5

def spinorXPos : Quad4 := ⟨Int.one, Int.two, Int.zero, Int.zero⟩
def spinorXNeg : Quad4 := ⟨Int.one, Int.two.neg, Int.zero, Int.zero⟩
def spinorYPos : Quad4 := ⟨Int.one, Int.zero, Int.two, Int.zero⟩
def spinorYNeg : Quad4 := ⟨Int.one, Int.zero, Int.two.neg, Int.zero⟩
def spinorZPos : Quad4 := ⟨Int.one, Int.zero, Int.zero, Int.two⟩
def spinorZNeg : Quad4 := ⟨Int.one, Int.zero, Int.zero, Int.two.neg⟩

end HeckeT5

open HeckeT5

private def five : Nat := Nat.one.succ.succ.succ.succ

private def sumSpinors {α : Type} (add : α → α → α) (term : Quad4 → α) : α :=
  add (add (add (term spinorXPos) (term spinorXNeg)) (add (term spinorYPos) (term spinorYNeg)))
    (add (term spinorZPos) (term spinorZNeg))

/-- The first character in terms of the squared normalized scalar coordinate. -/
def evalChi1 (q : Quad4) : IntRatio :=
  ((IntRatio.ofInt chi1Linear).mul (kappa q Quad4.one)).sub (IntRatio.ofInt chi1Constant.neg)

/-- The unnormalized sum of the character over the six right products. -/
def heckeT5Chi1 (q : Quad4) : IntRatio :=
  let term := fun r => evalChi1 (q.mul r)
  (((term spinorXPos).add (term spinorXNeg)).add ((term spinorYPos).add (term spinorYNeg))).add
    ((term spinorZPos).add (term spinorZNeg))

private def chi1Numerator (scalar denominator : Int) : Int :=
  (chi1Linear.mul (Int.square scalar)).sub denominator

private theorem dot_one (q : Quad4) : Eq (q.dot Quad4.one) q.w :=
  have left := (Eq.map₂ Int.add (Int.mul_one q.w) (Int.mul_zero q.x)).trans (Int.add_zero q.w)
  have right := Eq.map₂ Int.add (Int.mul_zero q.y) (Int.mul_zero q.z)
  (Eq.map₂ Int.add left right).trans (Int.add_zero q.w)

private theorem evalChi1_value (q : Quad4) (d : Nat) (hd : Not (Eq d Nat.zero))
    (hnorm : Eq q.normSq d) :
    Equivalent (evalChi1 q) (IntRatio.value (chi1Numerator q.w (Int.ofNat d)) d) :=
  let a := chi1Linear.mul (Int.square q.w)
  have hk : Eq (kappa q Quad4.one) (IntRatio.value (Int.square q.w) d) :=
    Eq.map₂ IntRatio.value (congrArg Int.square (dot_one q))
      ((Nat.mul_one q.normSq).trans hnorm)
  have hm := (congrArg (IntRatio.ofInt chi1Linear).mul hk).trans (value_mul_int chi1Linear (Int.square q.w) d)
  Eq.subst (fun v : IntRatio => Equivalent (v.sub (IntRatio.ofInt Int.one))
      (IntRatio.value (chi1Numerator q.w (Int.ofNat d)) d)) hm.symm
    ((IntRatio.sub_congr (IntRatio.equivalent_refl (IntRatio.value a d))
      (IntRatio.value_self d hd).symm).trans
      (value_sub_same a (Int.ofNat d) d))

private theorem add_values {d : Nat} {x y : IntRatio} {a b : Int}
    (hx : Equivalent x (IntRatio.value a d)) (hy : Equivalent y (IntRatio.value b d)) :
    Equivalent (x.add y) (IntRatio.value (a.add b) d) :=
  (IntRatio.add_congr hx hy).trans (IntRatio.value_add_same a b d)

private theorem sum_numerators (q : Quad4) :
    Eq (sumSpinors Int.add (fun r => chi1Numerator (q.mul r).w (Int.ofNat (five.mul q.normSq))))
      (Int.two.neg.mul (chi1Numerator q.w (Int.ofNat q.normSq))) :=
  let values := Expr.bind q.w (Expr.bind q.x (Expr.bind q.y (Expr.bind q.z (fun _ => Int.zero))))
  let w := Expr.var Nat.zero
  let x := Expr.var Nat.one
  let y := Expr.var Nat.one.succ
  let z := Expr.var Nat.one.succ.succ
  let norm := (w.sq.add x.sq).add (y.sq.add z.sq)
  let scalar := fun r : Quad4 =>
    (((w.mul (.const r.w)).sub (x.mul (.const r.x))).sub (y.mul (.const r.y))).sub (z.mul (.const r.z))
  let numerator := fun (s d : Expr) => ((Expr.const chi1Linear).mul s.sq).sub d
  have cancel := Expr.certify values
    (sumSpinors Expr.add (fun r => numerator (scalar r) ((Expr.const (Int.ofNat five)).mul norm)))
    ((Expr.const Int.two.neg).mul (numerator w norm)) Eq.refl
  Eq.subst (fun n => Eq (sumSpinors Int.add (fun r =>
      chi1Numerator (q.mul r).w ((Int.ofNat five).mul n)))
    (Int.two.neg.mul (chi1Numerator q.w n))) q.normSq_cast.symm cancel

theorem heckeT5_chi1_eigenvalue (q : Quad4) (hq : Not (Eq q Quad4.zero)) :
    Equivalent (heckeT5Chi1 q)
      ((IntRatio.value Int.two.neg Nat.one.succ.succ.succ.succ).mul (evalChi1 q)) :=
  let d := five.mul q.normSq
  have hn := q.normSq_ne_zero hq
  have hd : Not (Eq d Nat.zero) := nat_mul_ne_zero (Nat.succ_ne_zero _) hn
  have term (r : Quad4) (hr : Eq r.normSq five) :
      Equivalent (evalChi1 (q.mul r)) (IntRatio.value (chi1Numerator (q.mul r).w (Int.ofNat d)) d) :=
    evalChi1_value (q.mul r) d hd ((Quad4.normSq_mul q r).trans
      ((congrArg q.normSq.mul hr).trans (Nat.mul_comm q.normSq five)))
  have sum := add_values
    (add_values (add_values (term spinorXPos Eq.refl) (term spinorXNeg Eq.refl))
      (add_values (term spinorYPos Eq.refl) (term spinorYNeg Eq.refl)))
    (add_values (term spinorZPos Eq.refl) (term spinorZNeg Eq.refl))
  let a := chi1Numerator q.w (Int.ofNat q.normSq)
  have hscale := IntRatio.value_mul Int.two.neg a five q.normSq
  (Eq.subst (fun n => Equivalent (heckeT5Chi1 q) (IntRatio.value n d)) (sum_numerators q) sum).trans
    (Eq.subst (fun v => Equivalent v ((IntRatio.value Int.two.neg five).mul (evalChi1 q))) hscale
      (IntRatio.mul_congr (IntRatio.equivalent_refl (IntRatio.value Int.two.neg five))
        (evalChi1_value q q.normSq hn Eq.refl).symm))

set_option maxRecDepth 2048 in
theorem heckeT5_ramanujan_margin :
    let four := Nat.one.succ.succ.succ
    let five := four.succ
    let nine := five.succ.succ.succ.succ
    let ten := nine.succ
    let fourNinetySix := (((four.mul ten).add nine).mul ten).add five.succ
    let eigenvalue := IntRatio.value Int.two.neg five
    let margin := IntRatio.value (Int.ofNat fourNinetySix) (five.mul five)
    And (Equivalent ((IntRatio.ofInt (Int.ofNat (four.mul five))).sub (eigenvalue.mul eigenvalue)) margin)
      (IntRatio.Lt (IntRatio.ofInt Int.zero) margin) :=
  And.intro Eq.refl (And.intro True.intro (fun h => Int.ofNat_succ_ne_zero _ h.symm))

end Omega.Harmonic.PiFreeHaar

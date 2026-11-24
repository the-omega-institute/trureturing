/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Calculus.DFiniteJet.Basic

/-!
Omega original.

Factorial and odd-denominator coefficients for exponential, trigonometric and
arctangent formal series over signed rational numbers.
-/

noncomputable section

@[expose] public section

namespace Omega.JetSeq

open IntRatio

/-- The predecessor of `n!`, so the denominator is positive by construction. -/
def factorialPred : Nat → Nat := Nat.rec Nat.zero (fun n d => mulDenPred n d)

def factorial (n : Nat) : Nat := (factorialPred n).succ

theorem factorial_succ (n : Nat) : Eq (factorial n.succ) (n.succ.mul (factorial n)) :=
  Eq.refl

/-- Powers of a scalar, with constant term one even at parameter zero. -/
def scalarPow (a : IntRatio) : Nat → IntRatio := Nat.rec IntRatio.one (fun _ power => a.mul power)

/-- The coefficient at `n` is `aⁿ/n!`. -/
def Exp (a : IntRatio) : JetSeq := fun n => (scalarPow a n).mul (fraction Int.one (factorialPred n))

/-- The powers of the formal imaginary unit have these integer coordinates. -/
structure TrigNumerator where
  cos : Int
  sin : Int

def trigNumerator : Nat → TrigNumerator :=
  Nat.rec ⟨Int.one, Int.zero⟩ (fun _ v => ⟨v.sin.neg, v.cos⟩)

/-- The cosine coefficient at `n` is the real coordinate of `iⁿ` divided by `n!`. -/
def Cos : JetSeq := fun n => fraction (trigNumerator n).cos (factorialPred n)

/-- The sine coefficient at `n` is the imaginary coordinate of `iⁿ` divided by `n!`. -/
def Sin : JetSeq := fun n => fraction (trigNumerator n).sin (factorialPred n)

/-- The odd arctangent coefficients alternate between `1/n` and `-1/n`. -/
def Atan : JetSeq := Nat.rec IntRatio.zero (fun n _ => fraction (trigNumerator n.succ).sin n)

/-- The even degrees are indexed by repeated addition of two. -/
def evenDegree : Nat → Nat := Nat.rec Nat.zero (fun _ n => n.succ.succ)

def alternatingSign : Nat → Int := Nat.rec Int.one (fun _ s => s.neg)

private theorem trig_even (k : Nat) :
    And (Eq (trigNumerator (evenDegree k)).cos (alternatingSign k))
      (Eq (trigNumerator (evenDegree k)).sin Int.zero) :=
  Nat.rec (motive := fun k =>
    And (Eq (trigNumerator (evenDegree k)).cos (alternatingSign k))
      (Eq (trigNumerator (evenDegree k)).sin Int.zero))
    (And.intro Eq.refl Eq.refl)
    (fun _ ih => And.intro (congrArg Int.neg ih.left) (congrArg Int.neg ih.right)) k

theorem cos_even (k : Nat) :
    Eq (Cos (evenDegree k)) (fraction (alternatingSign k) (factorialPred (evenDegree k))) :=
  congrArg (fun v => fraction v (factorialPred (evenDegree k))) (trig_even k).left

theorem sin_odd (k : Nat) :
    Eq (Sin (evenDegree k).succ)
      (fraction (alternatingSign k) (factorialPred (evenDegree k).succ)) :=
  congrArg (fun v => fraction v (factorialPred (evenDegree k).succ)) (trig_even k).left

theorem cos_odd (k : Nat) : IntRatio.Equivalent (Cos (evenDegree k).succ) IntRatio.zero :=
  Eq.subst (fun v => IntRatio.Equivalent
    (fraction v (factorialPred (evenDegree k).succ)) IntRatio.zero)
    (congrArg Int.neg (trig_even k).right).symm
    (IntRatio.value_zero _ (Nat.succ_ne_zero _))

theorem sin_even (k : Nat) : IntRatio.Equivalent (Sin (evenDegree k)) IntRatio.zero :=
  Eq.subst (fun v => IntRatio.Equivalent
    (fraction v (factorialPred (evenDegree k))) IntRatio.zero) (trig_even k).right.symm
    (IntRatio.value_zero _ (Nat.succ_ne_zero _))

theorem atan_odd (k : Nat) :
    Eq (Atan (evenDegree k).succ) (fraction (alternatingSign k) (evenDegree k)) :=
  congrArg (fun v => fraction v (evenDegree k)) (trig_even k).left

theorem atan_even (k : Nat) : IntRatio.Equivalent (Atan (evenDegree k)) IntRatio.zero :=
  Nat.rec (motive := fun k => IntRatio.Equivalent (Atan (evenDegree k)) IntRatio.zero)
    (IntRatio.equivalent_refl _) (fun k _ =>
      Eq.subst (fun v => IntRatio.Equivalent (fraction v (evenDegree k).succ) IntRatio.zero)
        (trig_even k.succ).right.symm (IntRatio.value_zero _ (Nat.succ_ne_zero _))) k

private theorem factorial_cancel (a : Int) (n : Nat) :
    IntRatio.Equivalent ((IntRatio.ofNat n.succ).mul (fraction a (factorialPred n.succ)))
      (fraction a (factorialPred n)) :=
  let d := factorialPred n
  have reduced := IntRatio.value_scale a (factorial n) n
  have cancel : IntRatio.Equivalent
      (fraction (a.mul (Int.ofNat n.succ)) (mulDenPred d n)) (fraction a d) := reduced
  have numer := Int.mul_comm (Int.ofNat n.succ) a
  have denom := Nat.mul_comm (factorial n) n.succ
  have ratio : IntRatio.Equivalent
      (fraction ((Int.ofNat n.succ).mul a) (mulDenPred d n)) (fraction a d) :=
    Eq.subst (fun v => IntRatio.Equivalent (fraction v (mulDenPred d n)) (fraction a d))
      numer.symm cancel
  have denRatio : IntRatio.Equivalent
      (fraction ((Int.ofNat n.succ).mul a) (factorialPred n.succ)) (fraction a d) :=
    Eq.subst (fun v => IntRatio.Equivalent (fraction ((Int.ofNat n.succ).mul a) v) (fraction a d))
      (congrArg Nat.pred denom) ratio
  Eq.subst (fun v => IntRatio.Equivalent
      (fraction ((Int.ofNat n.succ).mul a) v) (fraction a d))
    (Nat.zero_add (factorialPred n.succ)).symm denRatio

theorem scalarPow_finite {a : IntRatio} (ha : IntRatio.Finite a) (n : Nat) :
    IntRatio.Finite (scalarPow a n) :=
  Nat.rec (motive := fun k => IntRatio.Finite (scalarPow a k))
    True.intro (fun _ h => IntRatio.finite_mul ha h) n

theorem exp_finite {a : IntRatio} (ha : IntRatio.Finite a) : Finite (Exp a) :=
  fun n => IntRatio.finite_mul (scalarPow_finite ha n) True.intro

theorem cos_finite : Finite Cos := fun _ => True.intro

theorem sin_finite : Finite Sin := fun _ => True.intro

theorem atan_finite : Finite Atan :=
  fun n => Nat.rec (motive := fun k => IntRatio.Finite (Atan k)) True.intro (fun _ _ => True.intro) n

theorem exp_zero (a : IntRatio) : Eq (Exp a Nat.zero) IntRatio.one := Eq.refl

theorem cos_zero : Eq (Cos Nat.zero) IntRatio.one := Eq.refl

theorem sin_zero : Eq (Sin Nat.zero) IntRatio.zero := Eq.refl

theorem atan_zero : Eq (Atan Nat.zero) IntRatio.zero := Eq.refl

/-- The exponential solves `E' = a E` at every coefficient. -/
theorem deriv_exp (a : IntRatio) : Equivalent (deriv (Exp a)) (smul a (Exp a)) :=
  fun n =>
    let factor := IntRatio.ofNat n.succ
    let power := scalarPow a n.succ
    let reciprocal := fraction Int.one (factorialPred n.succ)
    (IntRatio.mul_assoc factor power reciprocal).symm.trans
      ((IntRatio.mul_congr_left (IntRatio.mul_comm factor power) reciprocal).trans
        ((IntRatio.mul_assoc power factor reciprocal).trans
          ((IntRatio.mul_congr (IntRatio.equivalent_refl power) (factorial_cancel Int.one n)).trans
            (IntRatio.mul_assoc a (scalarPow a n) (fraction Int.one (factorialPred n))))))

/-- Formal differentiation sends cosine to negative sine. -/
theorem deriv_cos : Equivalent (deriv Cos) (neg Sin) :=
  fun n => factorial_cancel (trigNumerator n).sin.neg n

/-- Formal differentiation sends sine to cosine. -/
theorem deriv_sin : Equivalent (deriv Sin) Cos :=
  fun n => factorial_cancel (trigNumerator n).cos n

/-- The derivative of arctangent is the alternating even-power series. -/
theorem deriv_atan (n : Nat) :
    IntRatio.Equivalent (deriv Atan n) (IntRatio.ofInt (trigNumerator n).cos) :=
  let a := (trigNumerator n).cos
  let d := Int.ofNat n.succ
  Eq.subst (fun k =>
    Eq (((d.mul a).mul Int.one)) (a.mul (IntRatio.denominator k)))
    (Nat.zero_add n).symm ((Int.mul_one (d.mul a)).trans (Int.mul_comm d a))

end Omega.JetSeq

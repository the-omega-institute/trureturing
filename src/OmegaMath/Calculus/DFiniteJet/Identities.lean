/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Calculus.DFiniteJet.Coefficients

/-!
Omega original.

Formal exponential and trigonometric identities obtained from the differential
laws and the constant coefficients.
-/

noncomputable section

@[expose] public section

namespace Omega.JetSeq

/-- The truncated exponential is forced by its constant coefficient and its ODE. -/
theorem exp_unique_at (N : Nat) {a : IntRatio} {f : JetSeq}
    (initial : IntRatio.Equivalent (f Nat.zero) IntRatio.one)
    (solution : ∀ k, Nat.lt k N → IntRatio.Equivalent (deriv f k) (smul a f k)) :
    EquivalentAt N f (Exp a) :=
  Nat.rec (motive := fun k => Nat.le k N → IntRatio.Equivalent (f k) (Exp a k))
    (fun _ => initial)
    (fun k ih hk => IntRatio.mul_cancel_left (IntRatio.unit_ofNat_succ k)
      ((solution k hk).trans
        ((IntRatio.mul_congr (IntRatio.equivalent_refl a) (ih (Nat.le_trans
          (Nat.le.step (Nat.le.refl k)) hk))).trans (deriv_exp a k).symm)))

private theorem exp_sum_ode (a b : IntRatio) :
    Equivalent (deriv (mul (Exp a) (Exp b))) (smul (a.add b) (mul (Exp a) (Exp b))) :=
  fun k =>
    have left : Equivalent (mul (deriv (Exp a)) (Exp b)) (smul a (mul (Exp a) (Exp b))) :=
      fun j => (mul_congr (deriv_exp a) (fun i => IntRatio.equivalent_refl (Exp b i)) j).trans
        (smul_mul a (Exp a) (Exp b) j)
    have right : Equivalent (mul (Exp a) (deriv (Exp b))) (smul b (mul (Exp a) (Exp b))) :=
      fun j => (mul_congr (fun i => IntRatio.equivalent_refl (Exp a i)) (deriv_exp b) j).trans
        (mul_smul b (Exp a) (Exp b) j)
    (deriv_mul (Exp a) (Exp b) k).trans
      ((IntRatio.add_congr (left k) (right k)).trans
        (IntRatio.add_mul a b (mul (Exp a) (Exp b) k)).symm)

/-- The exponential addition law holds at every coefficient. -/
theorem exp_add (a b : IntRatio) : Equivalent (mul (Exp a) (Exp b)) (Exp (a.add b)) :=
  fun k => exp_unique_at k (a := a.add b) (f := mul (Exp a) (Exp b))
    (IntRatio.equivalent_refl IntRatio.one) (fun j _ => exp_sum_ode a b j) k (Nat.le.refl k)

private theorem exp_congr {a b : IntRatio} (h : IntRatio.Equivalent a b) :
    Equivalent (Exp a) (Exp b) :=
  fun k => IntRatio.mul_congr_left
    (Nat.rec (motive := fun j => IntRatio.Equivalent (scalarPow a j) (scalarPow b j))
      (IntRatio.equivalent_refl _) (fun _ ih => IntRatio.mul_congr h ih) k) _

private theorem exp_zero_parameter : Equivalent (Exp IntRatio.zero) one :=
  Nat.rec (motive := fun k => IntRatio.Equivalent (Exp IntRatio.zero k) (one k))
    (IntRatio.equivalent_refl _) (fun k _ =>
      (IntRatio.mul_congr_left
        (IntRatio.zero_mul (scalarPow_finite (a := IntRatio.zero) True.intro k)) _).trans
        (IntRatio.zero_mul True.intro))

/-- The exponential with opposite parameter is the multiplicative inverse. -/
theorem exp_inverse {a : IntRatio} (ha : IntRatio.Finite a) :
    Equivalent (mul (Exp a) (Exp a.neg)) one :=
  fun k => (exp_add a a.neg k).trans
    ((exp_congr (IntRatio.add_right_neg ha) k).trans (exp_zero_parameter k))

/-- Leibniz's rule gives derivative zero for `Cos² + Sin²`. -/
private theorem deriv_cos_sq_add_sin_sq :
    Equivalent (deriv (add (mul Cos Cos) (mul Sin Sin))) zero :=
  fun k =>
    let cross := mul Cos Sin k
    have sameSinCos := mul_comm Sin Cos k
    have left := (mul_congr deriv_cos (fun i => IntRatio.equivalent_refl (Cos i)) k).trans
      ((mul_comm (neg Sin) Cos k).trans (mul_neg Cos Sin k))
    have right := (mul_congr (fun i => IntRatio.equivalent_refl (Cos i)) deriv_cos k).trans
      (mul_neg Cos Sin k)
    have sineLeft := mul_congr deriv_sin (fun i => IntRatio.equivalent_refl (Sin i)) k
    have sineRight := (mul_congr (fun i => IntRatio.equivalent_refl (Sin i)) deriv_sin k).trans
      sameSinCos
    (deriv_add (mul Cos Cos) (mul Sin Sin) k).trans
      ((IntRatio.add_congr (deriv_mul Cos Cos k) (deriv_mul Sin Sin k)).trans
        ((IntRatio.add_congr (IntRatio.add_congr left right)
          (IntRatio.add_congr sineLeft sineRight)).trans
          (((IntRatio.add_congr_left (IntRatio.neg_add cross cross).symm (cross.add cross))).trans
            (IntRatio.add_left_neg (IntRatio.finite_add
              (finite_mul cos_finite sin_finite k) (finite_mul cos_finite sin_finite k))))))

/-- Pythagoras for the formal sine and cosine. -/
theorem cos_sq_add_sin_sq : Equivalent (add (mul Cos Cos) (mul Sin Sin)) one :=
  fun k => (constant_of_deriv_zero deriv_cos_sq_add_sin_sq k).trans
    (Nat.rec (motive := fun k => IntRatio.Equivalent
      (constant (add (mul Cos Cos) (mul Sin Sin) Nat.zero) k) (one k))
      (IntRatio.equivalent_refl IntRatio.one) (fun _ _ => IntRatio.equivalent_refl IntRatio.zero) k)

end Omega.JetSeq

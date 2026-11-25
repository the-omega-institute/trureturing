/- GID: D5/S0/Arithmetic/Exact/Int
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Integer squares, positive factors and arithmetic on explicit signs. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Int
public import D5.S0.Arithmetic.Exact.Ratio

/-!
Omega original.

Integer squares, positive factors and arithmetic on explicit signs.
-/

@[expose] public section

namespace Omega.Int

def zero : Int := ofNat Nat.zero
def one : Int := ofNat (Nat.succ Nat.zero)
def two : Int := ofNat (Nat.succ (Nat.succ Nat.zero))

noncomputable def square (a : Int) : Int := a.mul a

theorem square_nonneg (a : Int) : NonNeg (square a) :=
  Eq.subst (motive := NonNeg) natAbs_mul_self (NonNeg.mk (a.natAbs.mul a.natAbs))

theorem sum_of_two_squares_eq_zero (a b : Int) :
    Iff (Eq ((square a).add (square b)) zero) (And (Eq a zero) (Eq b zero)) :=
  have squares := Eq.map₂ Int.add (natAbs_mul_self (a := a)) (natAbs_mul_self (a := b))
  Iff.intro
    (fun e =>
      have h := Nat.eq_zero_of_add_eq_zero (ofNat_inj.mp (squares.trans e))
      have vanish : ∀ n : Nat, Eq (n.mul n) Nat.zero → Eq n Nat.zero :=
        fun _ hz => (Nat.mul_eq_zero.mp hz).elim (fun h => h) (fun h => h)
      And.intro (natAbs_eq_zero.mp (vanish _ h.left)) (natAbs_eq_zero.mp (vanish _ h.right)))
    (fun h =>
      have zeroSquare : Eq (square zero) zero := congrArg ofNat (Nat.mul_zero Nat.zero)
      (Eq.map₂ (fun (x y : Int) => (square x).add (square y)) h.left h.right).trans
        ((Eq.map₂ Int.add zeroSquare zeroSquare).trans (Int.add_zero zero)))

theorem ofNat_succ_ne_zero (k : Nat) : Not (Eq (ofNat k.succ) zero) :=
  fun e => Nat.succ_ne_zero k (ofNat_inj.mp e)

theorem nonneg_add {a b : Int} (ha : NonNeg a) (hb : NonNeg b) : NonNeg (a.add b) :=
  NonNeg.rec (motive := fun x _ => NonNeg (x.add b))
    (fun m => NonNeg.rec (motive := fun y _ => NonNeg ((ofNat m).add y))
      (fun n => NonNeg.mk (m.add n)) hb) ha

theorem nonneg_mul {a b : Int} (ha : NonNeg a) (hb : NonNeg b) : NonNeg (a.mul b) :=
  NonNeg.rec (motive := fun x _ => NonNeg (x.mul b))
    (fun m => NonNeg.rec (motive := fun y _ => NonNeg ((ofNat m).mul y))
      (fun n => NonNeg.mk (m.mul n)) hb) ha

theorem not_nonneg_negSucc (n : Nat) (h : NonNeg (negSucc n)) : False :=
  NonNeg.rec (motive := fun z _ => Int.rec (motive := fun _ => Prop)
    (fun _ => True) (fun _ => False) z) (fun _ => True.intro) h

theorem nonneg_mul_ofNat_succ (a : Int) (k : Nat) :
    Iff (NonNeg (a.mul (ofNat k.succ))) (NonNeg a) :=
  Int.rec (motive := fun a => Iff (NonNeg (a.mul (ofNat k.succ))) (NonNeg a))
    (fun n => Iff.intro (fun _ => NonNeg.mk n) (fun _ => NonNeg.mk (n.mul k.succ)))
    (fun n => Iff.intro
      (fun h =>
        have product := (Nat.succ_mul n k.succ).trans (Nat.add_succ (n.mul k.succ) k)
        False.elim (not_nonneg_negSucc _ (Eq.subst (motive := NonNeg) (congrArg negOfNat product) h)))
      (fun h => False.elim (not_nonneg_negSucc n h))) a

theorem le_mul_ofNat_succ (a b : Int) (k : Nat) :
    Iff ((a.mul (ofNat k.succ)).le (b.mul (ofNat k.succ))) (a.le b) :=
  let f := ofNat k.succ
  have same := Int.sub_mul b a f
  have equiv := nonneg_mul_ofNat_succ (b.sub a) k
  Iff.intro
    (fun h => equiv.mp (Eq.subst (motive := NonNeg) same.symm h))
    (fun h => Eq.subst (motive := NonNeg) same (equiv.mpr h))

theorem square_mul (a k : Int) : Eq (square (a.mul k)) ((square a).mul (square k)) :=
  (Int.mul_assoc (a.mul k) a k).symm.trans
    ((congrArg (fun t : Int => t.mul k) (Int.mul_right_comm a k a)).trans
      (Int.mul_assoc (square a) k k))

theorem mul_mul_mul_comm (a b c d : Int) :
    Eq ((a.mul b).mul (c.mul d)) ((a.mul c).mul (b.mul d)) :=
  (Int.mul_assoc a b (c.mul d)).trans
    ((congrArg a.mul ((Int.mul_assoc b c d).symm.trans
      ((congrArg (fun t : Int => t.mul d) (Int.mul_comm b c)).trans (Int.mul_assoc c b d)))).trans
      (Int.mul_assoc a c (b.mul d)).symm)

theorem add_add_add_comm (a b c d : Int) :
    Eq ((a.add b).add (c.add d)) ((a.add c).add (b.add d)) :=
  (Int.add_assoc a b (c.add d)).trans
    ((congrArg a.add ((Int.add_assoc b c d).symm.trans
      ((congrArg (fun t : Int => t.add d) (Int.add_comm b c)).trans (Int.add_assoc c b d)))).trans
      (Int.add_assoc a c (b.add d)).symm)

theorem eq_zero_or_ne_zero (a : Int) : Or (Eq a zero) (Not (Eq a zero)) :=
  Int.rec (motive := fun a => Or (Eq a zero) (Not (Eq a zero)))
    (fun n => Nat.rec (motive := fun n => Or (Eq (ofNat n) zero) (Not (Eq (ofNat n) zero)))
      (Or.inl rfl) (fun k _ => Or.inr (ofNat_succ_ne_zero k)) n)
    (fun k => Or.inr (negSucc_ne_zero k)) a

/-- The larger of two integers, selected by the sign of their difference. -/
noncomputable def max (a b : Int) : Int :=
  Int.rec (motive := fun _ => Int) (fun _ => b) (fun _ => a) (b.sub a)

/-- A common translation commutes with the integer maximum. -/
theorem max_add_common_right (a b c : Int) :
    Eq (max (a.add c) (b.add c)) ((max a b).add c) :=
  have sameDifference : Eq ((b.add c).sub (a.add c)) (b.sub a) :=
    (congrArg (b.add c).add (Int.neg_add (a := a) (b := c))).trans
      ((add_add_add_comm b c a.neg c.neg).trans
        ((congrArg (b.sub a).add (Int.add_right_neg c)).trans (Int.add_zero (b.sub a))))
  let choose (left right : Int) : Int → Int :=
    Int.rec (motive := fun _ => Int) (fun _ => right) (fun _ => left)
  have sameSelection := Int.rec (motive := fun difference =>
    Eq (choose (a.add c) (b.add c) difference) ((choose a b difference).add c))
    (fun _ => rfl) (fun _ => rfl) (b.sub a)
  (congrArg (choose (a.add c) (b.add c)) sameDifference).trans sameSelection

end Omega.Int

namespace Int
export _root_.Omega.Int (square square_nonneg sum_of_two_squares_eq_zero nonneg_add nonneg_mul
  nonneg_mul_ofNat_succ le_mul_ofNat_succ square_mul mul_mul_mul_comm add_add_add_comm
  eq_zero_or_ne_zero max max_add_common_right)
end Int

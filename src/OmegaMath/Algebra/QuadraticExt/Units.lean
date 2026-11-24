module
prelude
public import OmegaMath.Algebra.QuadraticExt.Operations

/-!
Omega original.

In a quadratic algebra an element is invertible exactly when its norm is
invertible. Over the strict integers this gives the golden integer unit
criteria of `D5.S0.Carrier.Units`, with inverse witnesses from conjugation.
-/

noncomputable section
@[expose] public section

namespace Omega.QuadPoly

variable {A : Type} {rel : A → A → Prop} {b c : A}

/-- A multiplicative inverse with respect to the coefficient equivalence. -/
def IsUnit (r : CommRingOps A rel) (z : QuadPoly A b c) : Prop :=
  Exists fun w => Equivalent r (mul r z w) (one r)

theorem isUnit_one {r : CommRingOps A rel} (law : r.Laws) :
    IsUnit r (one (b := b) (c := c) r) :=
  Exists.intro (one r) (mul_one law (one r))

theorem IsUnit.mul {r : CommRingOps A rel} (law : r.Laws) {z w : QuadPoly A b c}
    (hz : IsUnit r z) (hw : IsUnit r w) : IsUnit r (mul r z w) :=
  let l := ringLaws (b := b) (c := c) law
  hz.elim fun zi hzi =>
    hw.elim fun wi hwi =>
      have h : Equivalent r (QuadPoly.mul r w (QuadPoly.mul r wi zi)) zi :=
        l.trans (l.symm (l.mul_assoc w wi zi))
          (l.trans (l.mul_congr hwi (l.refl zi)) (l.one_mul zi))
      Exists.intro (QuadPoly.mul r wi zi) (l.trans (l.mul_assoc z w (QuadPoly.mul r wi zi))
        (l.trans (l.mul_congr (l.refl z) h) hzi))

theorem IsUnit.neg {r : CommRingOps A rel} (law : r.Laws) {z : QuadPoly A b c}
    (hz : IsUnit r z) : IsUnit r (neg r z) :=
  let l := ringLaws (b := b) (c := c) law
  hz.elim fun w hw =>
    Exists.intro (QuadPoly.neg r w) (l.trans (l.neg_mul z (QuadPoly.neg r w))
      (l.trans (l.neg_congr (l.mul_neg z w)) (l.trans (l.neg_neg (QuadPoly.mul r z w)) hw)))

theorem IsUnit.pow {r : CommRingOps A rel} (law : r.Laws) {z : QuadPoly A b c}
    (hz : IsUnit r z) (n : Nat) : IsUnit r (pow r z n) :=
  Nat.rec (motive := fun n => IsUnit r (QuadPoly.pow r z n))
    (isUnit_one law) (fun _ ih => hz.mul law ih) n

theorem isUnit_iff_norm_isUnit {r : CommRingOps A rel} (law : r.Laws)
    (z : QuadPoly A b c) :
    Iff (IsUnit r z) (Exists fun s => r.eqv (r.mul (norm r z) s) r.one) :=
  Iff.intro
    (fun h => h.elim fun w hw =>
      Exists.intro (norm r w) (law.trans (law.symm (norm_mul law z w))
        (law.trans (norm_congr law hw) (norm_one law))))
    (fun h => h.elim fun s hs => Exists.intro (scale r s (conj r z))
      (mul_scale_conj_eq_one law z s hs))

private theorem nat_eq_one_of_mul_eq_one {a b : Nat}
    (h : Eq (a.mul b) (.succ .zero)) : Eq a (.succ .zero) :=
  (Nat.rec (motive := fun a => ∀ b, Eq (a.mul b) (.succ .zero) → Eq a (.succ .zero))
    (fun b h => False.elim (Nat.succ_ne_zero .zero ((Nat.zero_mul b).symm.trans h).symm))
    (fun a _ b => Nat.rec
      (motive := fun b => Eq (a.succ.mul b) (.succ .zero) → Eq a.succ (.succ .zero))
      (fun h => False.elim (Nat.succ_ne_zero .zero h.symm))
      (fun _ _ h => congrArg Nat.succ
        (Nat.eq_zero_of_add_eq_zero (Nat.succ.inj h)).right) b) a) b h

private theorem int_natAbs_eq_one_iff (a : Int) :
    Iff (Eq a.natAbs (.succ .zero)) (Or (Eq a Int.one) (Eq a Int.one.neg)) :=
  Iff.intro
    (Int.rec (motive := fun a =>
        Eq a.natAbs (.succ .zero) → Or (Eq a Int.one) (Eq a Int.one.neg))
      (fun _ h => Or.inl (congrArg Int.ofNat h))
      (fun _ h => Or.inr (congrArg Int.negSucc (Nat.succ.inj h))) a)
    (fun h => h.elim (congrArg Int.natAbs) (congrArg Int.natAbs))

private theorem int_mul_self_eq_one_of_natAbs_eq_one {a : Int}
    (h : Eq a.natAbs (.succ .zero)) : Eq (a.mul a) Int.one :=
  Int.natAbs_mul_self.symm.trans (congrArg (fun (n : Nat) => Int.ofNat (n.mul n)) h)

/-- The absolute norm detects units in every integral quadratic algebra. -/
theorem isUnit_iff_norm_natAbs_eq_one {b c : Int} (z : IntQuadPoly b c) :
    Iff (IsUnit intRing z) (Eq (norm intRing z).natAbs (.succ .zero)) :=
  let normZ := norm intRing z
  let criterion := isUnit_iff_norm_isUnit intRingLaws z
  Iff.intro
    (fun h => (criterion.mp h).elim fun s hs =>
      nat_eq_one_of_mul_eq_one
        ((Int.natAbs_mul normZ s).symm.trans (congrArg Int.natAbs hs)))
    (fun h => criterion.mpr (Exists.intro normZ (int_mul_self_eq_one_of_natAbs_eq_one h)))

/-- In particular, a golden integer is a unit exactly when its norm is ±1. -/
theorem isUnit_iff_norm_eq_one_or_neg_one {b c : Int} (z : IntQuadPoly b c) :
    Iff (IsUnit intRing z) (Or (Eq (norm intRing z) Int.one) (Eq (norm intRing z) Int.one.neg)) :=
  let absCriterion := isUnit_iff_norm_natAbs_eq_one z
  let signCriterion := int_natAbs_eq_one_iff (norm intRing z)
  Iff.intro (fun h => signCriterion.mp (absCriterion.mp h))
    (fun h => absCriterion.mpr (signCriterion.mpr h))

/-- The golden generator has inverse minus its conjugate. -/
theorem golden_alpha_mul_neg_conj :
    let phi : IntQuadPoly Int.one Int.one := alpha intRing
    Equivalent intRing (mul intRing phi (neg intRing (conj intRing phi))) (one intRing) :=
  And.intro Eq.refl Eq.refl

/-- Compute `±φ^n` from the two constructors of the integer exponent. -/
def signedGoldenPower (negative : Bool) (n : Int) : IntQuadPoly Int.one Int.one :=
  let phi : IntQuadPoly Int.one Int.one := alpha intRing
  let phiInv := neg intRing (conj intRing phi)
  let power := Int.rec (pow intRing phi) (fun k => pow intRing phiInv k.succ) n
  Bool.rec power (neg intRing power) negative

theorem signedGoldenPower_isUnit (negative : Bool) (n : Int) :
    IsUnit intRing (signedGoldenPower negative n) :=
  let phi : IntQuadPoly Int.one Int.one := alpha intRing
  let phiInv := neg intRing (conj intRing phi)
  have phiUnit : IsUnit intRing phi := Exists.intro phiInv golden_alpha_mul_neg_conj
  have invUnit : IsUnit intRing phiInv :=
    Exists.intro phi (trans intRingLaws (mul_comm intRingLaws phiInv phi) golden_alpha_mul_neg_conj)
  have powerUnit : IsUnit intRing (signedGoldenPower .false n) :=
    Int.rec (motive := fun n => IsUnit intRing (signedGoldenPower .false n))
      (fun k => phiUnit.pow intRingLaws k) (fun k => invUnit.pow intRingLaws k.succ) n
  Bool.rec (motive := fun sign => IsUnit intRing (signedGoldenPower sign n))
    powerUnit (powerUnit.neg intRingLaws) negative

end Omega.QuadPoly

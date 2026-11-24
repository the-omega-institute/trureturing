/- GID: D5/S3/Quantum/AURICOmega/OmegaShadowBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaShadowBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact arithmetic and the real shadow of the projective circle. -/

module
prelude
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
public import OmegaMath.Projective.Circle

/-! Exact transport of Omega arithmetic and circle identities into Mathlib. -/

noncomputable section

namespace D5.S3.Quantum.AURICOmega.OmegaShadowBridge

open Omega (IntRatio)
open Omega.Projective.Circle (Nonzero cayleyX cayleyY kappa normSq)

private theorem ofOmegaEq {α : Sort*} {x y : α} (h : Omega.Eq x y) : x = y :=
  Omega.Eq.rec rfl h

/-- Read the Peano constructors as the corresponding standard natural constructors. -/
@[expose] public def toStdNat : Omega.Nat → ℕ :=
  Omega.Nat.rec 0 (fun _ n => n.succ)

public theorem toStdNat_add (a b : Omega.Nat) :
    toStdNat (a.add b) = toStdNat a + toStdNat b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change (toStdNat (a.add b)).succ = toStdNat a + (toStdNat b).succ
    rw [ih, Nat.add_succ]

public theorem toStdNat_mul (a b : Omega.Nat) :
    toStdNat (a.mul b) = toStdNat a * toStdNat b := by
  induction b with
  | zero => simp [toStdNat, Omega.Nat.mul]
  | succ b ih =>
    change toStdNat ((a.mul b).add a) = toStdNat a * (toStdNat b).succ
    rw [toStdNat_add, ih, Nat.mul_succ]

/-- Read the nonnegative and negative-successor branches in the standard integers. -/
@[expose] public def toStdInt : Omega.Int → ℤ :=
  Omega.Int.rec (fun n => Int.ofNat (toStdNat n)) (fun n => Int.negSucc (toStdNat n))

private theorem toStdInt_negOfNat (a : Omega.Nat) :
    toStdInt (Omega.Int.negOfNat a) = -(toStdNat a : ℤ) := by
  induction a using Omega.Nat.rec with
  | zero => rfl
  | succ n _ =>
    change Int.negSucc (toStdNat n) = -((toStdNat n).succ : ℤ)
    omega

public theorem toStdInt_neg (a : Omega.Int) :
    toStdInt a.neg = -toStdInt a := by
  induction a using Omega.Int.rec with
  | ofNat n => exact toStdInt_negOfNat n
  | negSucc n =>
    change ((toStdNat n).succ : ℤ) = -Int.negSucc (toStdNat n)
    omega

private theorem toStdInt_subNatNat (m n : Omega.Nat) :
    toStdInt (Omega.Int.subNatNat m n) = (toStdNat m : ℤ) - (toStdNat n : ℤ) := by
  induction m generalizing n with
  | zero =>
    change toStdInt (Omega.Int.negOfNat n) = 0 - (toStdNat n : ℤ)
    rw [toStdInt_negOfNat, zero_sub]
  | succ m ih =>
    induction n using Omega.Nat.rec with
    | zero => rfl
    | succ n _ =>
      change toStdInt (Omega.Int.subNatNat m n) =
        ((toStdNat m).succ : ℤ) - ((toStdNat n).succ : ℤ)
      rw [ih]
      omega

public theorem toStdInt_add (a b : Omega.Int) :
    toStdInt (a.add b) = toStdInt a + toStdInt b := by
  induction a using Omega.Int.rec with
  | ofNat m =>
    induction b using Omega.Int.rec with
    | ofNat n =>
      change (toStdNat (m.add n) : ℤ) = (toStdNat m : ℤ) + (toStdNat n : ℤ)
      rw [toStdNat_add, Nat.cast_add]
    | negSucc n =>
      change toStdInt (Omega.Int.subNatNat m n.succ) = (toStdNat m : ℤ) + Int.negSucc (toStdNat n)
      rw [toStdInt_subNatNat]
      change (toStdNat m : ℤ) - ((toStdNat n).succ : ℤ) = _
      omega
  | negSucc m =>
    induction b using Omega.Int.rec with
    | ofNat n =>
      change toStdInt (Omega.Int.subNatNat n m.succ) = Int.negSucc (toStdNat m) + (toStdNat n : ℤ)
      rw [toStdInt_subNatNat]
      change (toStdNat n : ℤ) - ((toStdNat m).succ : ℤ) = _
      omega
    | negSucc n =>
      change Int.negSucc ((toStdNat (m.add n)).succ) =
        Int.negSucc (toStdNat m) + Int.negSucc (toStdNat n)
      rw [toStdNat_add]
      omega

public theorem toStdInt_mul (a b : Omega.Int) :
    toStdInt (a.mul b) = toStdInt a * toStdInt b := by
  induction a using Omega.Int.rec with
  | ofNat m =>
    induction b using Omega.Int.rec with
    | ofNat n =>
      change (toStdNat (m.mul n) : ℤ) = (toStdNat m : ℤ) * (toStdNat n : ℤ)
      rw [toStdNat_mul, Nat.cast_mul]
    | negSucc n =>
      change toStdInt (Omega.Int.negOfNat (m.mul n.succ)) =
        (toStdNat m : ℤ) * Int.negSucc (toStdNat n)
      rw [toStdInt_negOfNat, toStdNat_mul, Nat.cast_mul]
      change -((toStdNat m : ℤ) * ((toStdNat n).succ : ℤ)) = _
      rw [← mul_neg, Int.negSucc_eq, Nat.cast_succ]
  | negSucc m =>
    induction b using Omega.Int.rec with
    | ofNat n =>
      change toStdInt (Omega.Int.negOfNat (m.succ.mul n)) =
        Int.negSucc (toStdNat m) * (toStdNat n : ℤ)
      rw [toStdInt_negOfNat, toStdNat_mul, Nat.cast_mul]
      change -(((toStdNat m).succ : ℤ) * (toStdNat n : ℤ)) = _
      rw [← neg_mul, Int.negSucc_eq, Nat.cast_succ]
    | negSucc n =>
      change (toStdNat (m.succ.mul n.succ) : ℤ) =
        Int.negSucc (toStdNat m) * Int.negSucc (toStdNat n)
      rw [toStdNat_mul, Nat.cast_mul]
      change ((toStdNat m).succ : ℤ) * ((toStdNat n).succ : ℤ) = _
      rw [Int.negSucc_eq, Int.negSucc_eq, neg_mul_neg, Nat.cast_succ, Nat.cast_succ]

/-- Read a finite fraction by division in ℚ. The undefined constructor maps to zero. -/
@[expose] public def toRat : IntRatio → ℚ :=
  IntRatio.rec 0 (fun a d => (toStdInt a : ℚ) / (toStdInt (IntRatio.denominator d) : ℚ))

/-- Embed the rational reading into ℝ. -/
@[expose] public noncomputable def toReal (x : IntRatio) : ℝ := (toRat x : ℝ)

private theorem denominator_pos (d : Omega.Nat) :
    0 < (toStdInt (IntRatio.denominator d) : ℚ) := by
  change 0 < ((toStdNat d).succ : ℚ)
  exact Nat.cast_pos.mpr (Nat.succ_pos _)

private theorem denominator_mul (b d : Omega.Nat) :
    (toStdInt (IntRatio.denominator (IntRatio.mulDenPred b d)) : ℚ) =
      (toStdInt (IntRatio.denominator b) : ℚ) * (toStdInt (IntRatio.denominator d) : ℚ) := by
  rw [ofOmegaEq (IntRatio.denominator_mul b d), toStdInt_mul, Int.cast_mul]

public theorem toRat_equivalent {x y : IntRatio} (h : IntRatio.Equivalent x y) :
    toRat x = toRat y := by
  induction x using IntRatio.rec with
  | undefined =>
    induction y using IntRatio.rec with
    | undefined => rfl
    | fraction _ _ => exact Omega.False.elim h
  | fraction a b =>
    induction y using IntRatio.rec with
    | undefined => exact Omega.False.elim h
    | fraction c d =>
      change Omega.Eq (a.mul (IntRatio.denominator d)) (c.mul (IntRatio.denominator b)) at h
      have cross := congrArg (fun z : Omega.Int => (toStdInt z : ℚ)) (ofOmegaEq h)
      simp only [toStdInt_mul, Int.cast_mul] at cross
      exact (div_eq_div_iff (denominator_pos b).ne' (denominator_pos d).ne').2 cross

public theorem toRat_add (a c : Omega.Int) (b d : Omega.Nat) :
    toRat ((IntRatio.fraction a b).add (IntRatio.fraction c d)) =
      toRat (IntRatio.fraction a b) + toRat (IntRatio.fraction c d) := by
  simp only [toRat, IntRatio.add, IntRatio.map₂, toStdInt_add, toStdInt_mul,
    Int.cast_add, Int.cast_mul, denominator_mul]
  have h := (div_add_div (toStdInt a : ℚ) (toStdInt c : ℚ)
    (denominator_pos b).ne' (denominator_pos d).ne').symm
  rw [mul_comm (toStdInt (IntRatio.denominator b) : ℚ) (toStdInt c : ℚ)] at h
  exact h

public theorem toRat_mul (x y : IntRatio) :
    toRat (x.mul y) = toRat x * toRat y := by
  induction x using IntRatio.rec <;> induction y using IntRatio.rec <;>
    simp [toRat, IntRatio.mul, IntRatio.map₂, toStdInt_mul, denominator_mul, div_mul_div_comm]

public theorem toRat_inv (x : IntRatio) : toRat x.inv = (toRat x)⁻¹ := by
  induction x using IntRatio.rec with
  | undefined => exact inv_zero.symm
  | fraction a b =>
    induction a using Omega.Int.rec with
    | ofNat n =>
      induction n using Omega.Nat.rec with
      | zero =>
        change 0 = ((0 : ℚ) / _)⁻¹
        simp
      | succ n _ =>
        change (toStdInt (IntRatio.denominator b) : ℚ) / (toStdInt (IntRatio.denominator n) : ℚ) =
          ((toStdInt (IntRatio.denominator n) : ℚ) / (toStdInt (IntRatio.denominator b) : ℚ))⁻¹
        rw [inv_div]
    | negSucc n =>
      change (toStdInt (IntRatio.denominator b).neg : ℚ) / (toStdInt (IntRatio.denominator n) : ℚ) =
        ((toStdInt (IntRatio.denominator n).neg : ℚ) / (toStdInt (IntRatio.denominator b) : ℚ))⁻¹
      rw [toStdInt_neg, toStdInt_neg, Int.cast_neg, Int.cast_neg, inv_div, neg_div, div_neg]

private theorem toStdInt_nonneg (a : Omega.Int) :
    Omega.Int.NonNeg a → 0 ≤ toStdInt a := by
  induction a using Omega.Int.rec with
  | ofNat n => exact fun _ => Int.natCast_nonneg _
  | negSucc _ => exact Omega.False.elim

private theorem toStdInt_le {a b : Omega.Int} (h : a.le b) : toStdInt a ≤ toStdInt b := by
  have h' := toStdInt_nonneg (b.sub a) h
  rwa [Omega.Int.sub, toStdInt_add, toStdInt_neg, ← sub_eq_add_neg, sub_nonneg] at h'

private theorem toRat_le {x y : IntRatio} (h : IntRatio.Le x y) : toRat x ≤ toRat y := by
  induction x using IntRatio.rec with
  | undefined => exact Omega.False.elim h
  | fraction a b =>
    induction y using IntRatio.rec with
    | undefined => exact Omega.False.elim h
    | fraction c d =>
      change (a.mul (IntRatio.denominator d)).le (c.mul (IntRatio.denominator b)) at h
      have cross := toStdInt_le h
      rw [toStdInt_mul, toStdInt_mul] at cross
      apply (div_le_div_iff₀ (denominator_pos b) (denominator_pos d)).2
      exact_mod_cast cross

private theorem toRat_ofInt (a : Omega.Int) : toRat (IntRatio.ofInt a) = (toStdInt a : ℚ) := by
  change (toStdInt a : ℚ) / 1 = _
  exact div_one _

/-- The real reading of the rational Cayley image of every projective pair has unit norm. -/
public theorem cayley_circle_unit (p q : Omega.Int) (h : Nonzero p q) :
    toReal (cayleyX p q) ^ 2 + toReal (cayleyY p q) ^ 2 = 1 := by
  have den : Omega.Not (Omega.Eq (normSq p q) Omega.Nat.zero) := by
    intro hz
    have both := (Omega.Projective.Circle.kappa_undefined_iff p q).mp
      ((IntRatio.value_undefined_iff _ _).mpr hz)
    exact h.elim (fun hp => hp both.left) (fun hq => hq both.right)
  have unit := toRat_equivalent (Omega.Projective.Circle.cayley_circle_unit p q h)
  have rational : toRat (cayleyX p q) ^ 2 + toRat (cayleyY p q) ^ 2 = 1 := by
    revert unit
    generalize hden : normSq p q = d at den
    induction d using Omega.Nat.rec with
    | zero => exact Omega.False.elim (den Omega.Eq.refl)
    | succ d _ =>
      intro unit
      dsimp only [cayleyX, cayleyY] at unit ⊢
      rw [hden] at unit ⊢
      let x := IntRatio.fraction ((Omega.Int.square q).sub (Omega.Int.square p)) d
      let y := IntRatio.fraction ((p.mul q).add (q.mul p)) d
      change toRat x ^ 2 + toRat y ^ 2 = 1
      have add : toRat ((x.mul x).add (y.mul y)) = toRat (x.mul x) + toRat (y.mul y) :=
        toRat_add _ _ _ _
      change toRat ((x.mul x).add (y.mul y)) = _ at unit
      rw [add, toRat_mul, toRat_mul] at unit
      simpa only [pow_two, toRat_ofInt, show (toStdInt Omega.Int.one : ℚ) = 1 from rfl] using unit
  unfold toReal
  have mapped := congrArg (fun x : ℚ => (x : ℝ)) rational
  simpa only [Rat.cast_add, Rat.cast_pow, Rat.cast_one] using mapped

private theorem kappa_unit_interval_of_nonzero (p q : Omega.Int) (h : Nonzero p q) :
    0 ≤ toReal (kappa p q) ∧ toReal (kappa p q) ≤ 1 := by
  have bounds := (Omega.Projective.Circle.kappa_spread_unit_interval p q h).left
  have lower : (0 : ℚ) ≤ toRat (kappa p q) := by
    simpa only [toRat_ofInt, show (toStdInt Omega.Int.zero : ℚ) = 0 from rfl] using
      toRat_le bounds.left
  have upper : toRat (kappa p q) ≤ (1 : ℚ) := by
    simpa only [toRat_ofInt, show (toStdInt Omega.Int.one : ℚ) = 1 from rfl] using
      toRat_le bounds.right
  unfold toReal
  exact ⟨by simpa only [Rat.cast_zero] using (Rat.cast_le (K := ℝ)).mpr lower,
    by simpa only [Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr upper⟩

/-- The real reading of overlap lies in the closed unit interval, including at the origin. -/
public theorem kappa_unit_interval (p q : Omega.Int) :
    0 ≤ toReal (kappa p q) ∧ toReal (kappa p q) ≤ 1 := by
  by_cases hp : p = Omega.Int.zero
  · subst p
    by_cases hq : q = Omega.Int.zero
    · subst q
      change 0 ≤ ((0 : ℚ) : ℝ) ∧ ((0 : ℚ) : ℝ) ≤ 1
      simp
    · exact kappa_unit_interval_of_nonzero _ _
        (Omega.Or.inr (fun e => False.elim (hq (ofOmegaEq e))))
  · exact kappa_unit_interval_of_nonzero _ _ (Omega.Or.inl (fun e => False.elim (hp (ofOmegaEq e))))

end D5.S3.Quantum.AURICOmega.OmegaShadowBridge

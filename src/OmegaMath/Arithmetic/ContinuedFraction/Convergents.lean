/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Arithmetic.Euclidean.Division
public import OmegaInit.Data.Int

/-!
Omega original.

Finite simple continued fractions in coefficient order, with signed determinants
and denominator bounds over the strict natural numbers and integers.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic.ContinuedFraction

/-- A numerator and denominator in the continuant recurrence. -/
structure Convergent where
  numerator : Nat
  denominator : Nat

/-- The current continuant and its immediate predecessor. -/
structure ConvergentPair where
  current : Convergent
  previous : Convergent

namespace ConvergentPair

/-- The initial continuants, at indices minus one and minus two. -/
def initial : ConvergentPair :=
  ⟨⟨Nat.one, Nat.zero⟩, ⟨Nat.zero, Nat.one⟩⟩

/-- One coefficient sends each coordinate to its current multiple plus its predecessor. -/
def step (pair : ConvergentPair) (a : Nat) : ConvergentPair :=
  ⟨⟨(a.mul pair.current.numerator).add pair.previous.numerator,
    (a.mul pair.current.denominator).add pair.previous.denominator⟩, pair.current⟩

/-- The signed cross product, with the current numerator first. -/
def determinant (pair : ConvergentPair) : Int :=
  Int.subNatNat (pair.current.numerator.mul pair.previous.denominator)
    (pair.previous.numerator.mul pair.current.denominator)

end ConvergentPair

def appendCoefficient (coeffs : NatList) (a : Nat) : NatList :=
  NatList.rec (motive := fun _ => NatList) (.cons a .nil)
    (fun b _ rest => .cons b rest) coeffs

def coefficientCount (coeffs : NatList) : Nat :=
  NatList.rec (motive := fun _ => Nat) Nat.zero (fun _ _ n => n.succ) coeffs

/-- Apply the coefficients from left to right to a pair of continuants. -/
def ConvergentPair.run (coeffs : NatList) : ConvergentPair → ConvergentPair :=
  NatList.rec (motive := fun _ => ConvergentPair → ConvergentPair)
    (fun pair => pair) (fun a _ rest pair => rest (pair.step a)) coeffs

/-- The last two continuants of a coefficient list. On a nonempty list, the
current continuant is the convergent of the whole list. -/
def convergentPair (coeffs : NatList) : ConvergentPair :=
  ConvergentPair.run coeffs ConvergentPair.initial

private theorem run_append (coeffs : NatList) (a : Nat) :
    ∀ pair : ConvergentPair, Eq (ConvergentPair.run (appendCoefficient coeffs a) pair)
      ((ConvergentPair.run coeffs pair).step a) :=
  NatList.rec (motive := fun coeffs => ∀ pair : ConvergentPair,
    Eq (ConvergentPair.run (appendCoefficient coeffs a) pair)
      ((ConvergentPair.run coeffs pair).step a))
    (fun _ => Eq.refl) (fun b _ ih pair => ih (pair.step b)) coeffs

theorem convergentPair_appendCoefficient (coeffs : NatList) (a : Nat) :
    Eq (convergentPair (appendCoefficient coeffs a)) ((convergentPair coeffs).step a) :=
  run_append coeffs a ConvergentPair.initial

private theorem count_append (coeffs : NatList) (a : Nat) :
    Eq (coefficientCount (appendCoefficient coeffs a)) (coefficientCount coeffs).succ :=
  NatList.rec (motive := fun coeffs =>
    Eq (coefficientCount (appendCoefficient coeffs a)) (coefficientCount coeffs).succ)
    Eq.refl (fun _ _ ih => congrArg Nat.succ ih) coeffs

private theorem append_induction (P : NatList → Prop) (empty : P .nil)
    (append : ∀ coeffs a, P coeffs → P (appendCoefficient coeffs a))
    (coeffs : NatList) : P coeffs :=
  (NatList.rec (motive := fun coeffs => ∀ prepend : NatList → NatList,
    P (prepend .nil) →
    (∀ xs a, P (prepend xs) → P (prepend (appendCoefficient xs a))) →
    P (prepend coeffs))
    (fun _ base _ => base)
    (fun b _ ih prepend base step =>
      ih (fun xs => prepend (.cons b xs)) (step .nil b base)
        (fun xs a h => step (.cons b xs) a h)) coeffs)
    (fun xs => xs) empty append

/-- The integer `(-1)^n`. -/
def alternatingSign (n : Nat) : Int :=
  Nat.rec (motive := fun _ => Int) (Int.ofNat Nat.one) (fun _ s => s.neg) n

private theorem subNatNat_swap (m n : Nat) :
    Eq (Int.subNatNat n m) (Int.subNatNat m n).neg :=
  Int.subNatNat_elim m n (fun m n diff => Eq (Int.subNatNat n m) diff.neg)
    (fun i n => Nat.rec (motive := fun i =>
      Eq (Int.subNatNat n (n.add i)) (Int.ofNat i).neg)
      (Int.subNatNat_self n) (fun j _ => Int.subNatNat_add_right n j) i)
    (fun i m => Int.subNatNat_add_left m i.succ)

private theorem scaled_cross (a x y z : Nat) :
    Eq (((a.mul x).add z).mul y) ((z.mul y).add (a.mul (x.mul y))) :=
  (Nat.add_mul (a.mul x) z y).trans
    ((Nat.add_comm ((a.mul x).mul y) (z.mul y)).trans
      (congrArg ((z.mul y).add) (Nat.mul_assoc a x y)))

private theorem determinant_step (pair : ConvergentPair) (a : Nat) :
    Eq (pair.step a).determinant pair.determinant.neg :=
  let p := pair.current.numerator
  let q := pair.current.denominator
  let r := pair.previous.numerator
  let s := pair.previous.denominator
  let common := a.mul (p.mul q)
  have left : Eq (((a.mul p).add r).mul q) ((r.mul q).add common) :=
    scaled_cross a p q r
  have right : Eq (p.mul ((a.mul q).add s)) ((p.mul s).add common) :=
    (Nat.mul_comm p ((a.mul q).add s)).trans
      ((scaled_cross a q p s).trans
        ((congrArg (fun x : Nat => x.add (a.mul (q.mul p))) (Nat.mul_comm s p)).trans
          (congrArg (fun x => (p.mul s).add (a.mul x)) (Nat.mul_comm q p))))
  (congrArg (fun x => Int.subNatNat x (p.mul ((a.mul q).add s))) left).trans
    ((congrArg (Int.subNatNat ((r.mul q).add common)) right).trans
      ((Int.subNatNat_add_add (r.mul q) (p.mul s) common).trans
        (subNatNat_swap (p.mul s) (r.mul q))))

/-- For a list of length `n`, the last two continuants have determinant `(-1)^n`.
The first convergent uses the initial continuant as its predecessor. -/
theorem eulerWallis (coeffs : NatList) :
    Eq (convergentPair coeffs).determinant (alternatingSign (coefficientCount coeffs)) :=
  append_induction
    (fun xs => Eq (convergentPair xs).determinant (alternatingSign (coefficientCount xs)))
    Eq.refl
    (fun xs a ih =>
      (congrArg ConvergentPair.determinant (convergentPair_appendCoefficient xs a)).trans
        ((determinant_step (convergentPair xs) a).trans
          ((congrArg Int.neg ih).trans (congrArg alternatingSign (count_append xs a)).symm)))
    coeffs

/-- Adjacent convergents at indices `n` and `n+1` have determinant `(-1)^n`,
where `n` is the length of the tail of the first prefix. -/
theorem eulerWallis_next (head : Nat) (tail : NatList) (a : Nat) :
    Eq (convergentPair (appendCoefficient (.cons head tail) a)).determinant
      (alternatingSign (coefficientCount tail)) :=
  (eulerWallis (appendCoefficient (.cons head tail) a)).trans
    ((congrArg alternatingSign (count_append (.cons head tail) a)).trans
      (Int.neg_neg (alternatingSign (coefficientCount tail))))

private theorem alternatingSign_abs (n : Nat) : Eq (alternatingSign n).natAbs Nat.one :=
  Nat.rec (motive := fun n => Eq (alternatingSign n).natAbs Nat.one) Eq.refl
    (fun n ih => (Int.natAbs_neg (alternatingSign n)).trans ih) n

/-- Every common divisor of the numerator and denominator divides one. -/
theorem convergent_dvd_one (coeffs : NatList) (d : Nat)
    (hn : Dvd d (convergentPair coeffs).current.numerator)
    (hd : Dvd d (convergentPair coeffs).current.denominator) : Dvd d Nat.one :=
  let pair := convergentPair coeffs
  have unit : Eq pair.determinant.natAbs Nat.one :=
    (congrArg Int.natAbs (eulerWallis coeffs)).trans
      (alternatingSign_abs (coefficientCount coeffs))
  hn.elim fun n hn => hd.elim fun q hd =>
    let r := pair.previous.numerator
    let s := pair.previous.denominator
    let diff := Int.subNatNat (n.mul s) (q.mul r)
    have left : Eq (pair.current.numerator.mul s) (d.mul (n.mul s)) :=
      (congrArg (fun x : Nat => x.mul s) hn).trans (Nat.mul_assoc d n s)
    have right : Eq (r.mul pair.current.denominator) (d.mul (q.mul r)) :=
      (Nat.mul_comm r pair.current.denominator).trans
        ((congrArg (fun x : Nat => x.mul r) hd).trans (Nat.mul_assoc d q r))
    have factored : Eq pair.determinant ((Int.ofNat d).mul diff) :=
      (congrArg (fun x => Int.subNatNat x (r.mul pair.current.denominator)) left).trans
        ((congrArg (Int.subNatNat (d.mul (n.mul s))) right).trans
          (Int.ofNat_mul_subNatNat d (n.mul s) (q.mul r)).symm)
    Exists.intro diff.natAbs (unit.symm.trans
      ((congrArg Int.natAbs factored).trans (Int.natAbs_mul (Int.ofNat d) diff)))

/-- A common divisor of the coordinates is one, including at the first convergent. -/
theorem convergent_coprime (coeffs : NatList) (d : Nat)
    (hn : Dvd d (convergentPair coeffs).current.numerator)
    (hd : Dvd d (convergentPair coeffs).current.denominator) : Eq d Nat.one :=
  dvd_one (convergent_dvd_one coeffs d hn hd)

/-- Strict positivity of each coefficient in a list. For a regular continued
fraction this is required of the tail after the integer part. -/
def PositiveCoefficients (coeffs : NatList) : Prop :=
  NatList.rec (motive := fun _ => Prop) True
    (fun a _ rest => And (Nat.lt Nat.zero a) rest) coeffs

private theorem positive_append (coeffs : NatList) (a : Nat) :
    PositiveCoefficients (appendCoefficient coeffs a) →
      And (PositiveCoefficients coeffs) (Nat.lt Nat.zero a) :=
  NatList.rec (motive := fun coeffs =>
    PositiveCoefficients (appendCoefficient coeffs a) →
      And (PositiveCoefficients coeffs) (Nat.lt Nat.zero a))
    (fun h => And.intro True.intro h.left)
    (fun _ _ ih h =>
      let rest := ih h.right
      And.intro (And.intro h.left rest.left) rest.right) coeffs

private theorem le_positive_mul (q : Nat) {a : Nat} (ha : Nat.lt Nat.zero a) :
    Nat.le q (a.mul q) :=
  Eq.subst (fun x => Nat.le x (a.mul q)) (Nat.one_mul q) (mul_le_mul_right ha q)

/-- Appending a positive coefficient weakly increases the denominator. -/
theorem denominator_le_next (coeffs : NatList) (a : Nat) (ha : Nat.lt Nat.zero a) :
    Nat.le (convergentPair coeffs).current.denominator
      (convergentPair (appendCoefficient coeffs a)).current.denominator :=
  let pair := convergentPair coeffs
  let q := pair.current.denominator
  let previous := pair.previous.denominator
  Eq.subst (fun p : ConvergentPair => Nat.le q p.current.denominator)
    (convergentPair_appendCoefficient coeffs a).symm
    (Nat.le_trans (le_positive_mul q ha)
      (Nat.add_le_add_left (Nat.zero_le previous) (a.mul q)))

/-- The Fibonacci numbers, starting with zero and one. -/
def fibonacci (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Bool → Nat) (Bool.rec Nat.zero Nat.one)
    (fun _ pair => Bool.rec (pair .true) ((pair .true).add (pair .false))) n .false

theorem fibonacci_step (n : Nat) :
    Eq (fibonacci n.succ.succ) ((fibonacci n.succ).add (fibonacci n)) :=
  Eq.refl

private theorem fibonacci_succ_pos (n : Nat) : Nat.lt Nat.zero (fibonacci n.succ) :=
  Nat.rec (motive := fun n => Nat.lt Nat.zero (fibonacci n.succ)) (Nat.le.refl Nat.one)
    (fun n ih => Eq.subst (Nat.le Nat.one) (fibonacci_step n).symm
      (Nat.le_trans ih
        (Nat.add_le_add_left (Nat.zero_le (fibonacci n)) (fibonacci n.succ)))) n

private def DenominatorBounds (head : Nat) (tail : NatList) : Prop :=
  let pair := convergentPair (.cons head tail)
  let n := coefficientCount tail
  And (Nat.le (fibonacci n.succ) pair.current.denominator)
    (Nat.le (fibonacci n) pair.previous.denominator)

private theorem denominator_bounds (head : Nat) (tail : NatList)
    (h : PositiveCoefficients tail) : DenominatorBounds head tail :=
  append_induction (fun xs => PositiveCoefficients xs → DenominatorBounds head xs)
    (fun _ => And.intro (Nat.le.refl Nat.one) (Nat.le.refl Nat.zero))
    (fun xs a ih h =>
      let positive := positive_append xs a h
      let pair := convergentPair (.cons head xs)
      let q := pair.current.denominator
      let previous := pair.previous.denominator
      let n := coefficientCount xs
      have old := ih positive.left
      have currentBound : Nat.le (fibonacci n.succ.succ) ((a.mul q).add previous) :=
        Nat.le_trans (add_le_add_right (Nat.le_trans old.left (le_positive_mul q positive.right))
          (fibonacci n))
          (Nat.add_le_add_left old.right (a.mul q))
      have shifted : And (Nat.le (fibonacci n.succ.succ) (pair.step a).current.denominator)
          (Nat.le (fibonacci n.succ) (pair.step a).previous.denominator) :=
        And.intro currentBound old.left
      Eq.subst (fun p : ConvergentPair =>
        And (Nat.le (fibonacci (coefficientCount (appendCoefficient xs a)).succ) p.current.denominator)
          (Nat.le (fibonacci (coefficientCount (appendCoefficient xs a))) p.previous.denominator))
        (convergentPair_appendCoefficient (.cons head xs) a).symm
        (Eq.subst (fun k : Nat =>
          And (Nat.le (fibonacci k.succ) (pair.step a).current.denominator)
            (Nat.le (fibonacci k) (pair.step a).previous.denominator))
          (count_append xs a).symm shifted))
    tail h

/-- A list of length `n + 1` with positive tail has denominator at least `F_(n + 1)`. -/
theorem fibonacci_le_denominator (head : Nat) (tail : NatList) (h : PositiveCoefficients tail) :
    Nat.le (fibonacci (coefficientCount (.cons head tail)))
      (convergentPair (.cons head tail)).current.denominator :=
  (denominator_bounds head tail h).left

/-- Every nonempty list with positive tail has a positive denominator. -/
theorem denominator_positive (head : Nat) (tail : NatList) (h : PositiveCoefficients tail) :
    Nat.lt Nat.zero (convergentPair (.cons head tail)).current.denominator :=
  Nat.le_trans (fibonacci_succ_pos (coefficientCount tail)) (fibonacci_le_denominator head tail h)

/-- After two or more coefficients, appending a positive coefficient strictly
increases the denominator of a regular continued fraction. -/
theorem denominator_lt_next (head second : Nat) (tail : NatList) (a : Nat)
    (h : PositiveCoefficients (.cons second tail)) (ha : Nat.lt Nat.zero a) :
    Nat.lt (convergentPair (.cons head (.cons second tail))).current.denominator
      (convergentPair (appendCoefficient (.cons head (.cons second tail)) a)).current.denominator :=
  let coeffs := NatList.cons head (.cons second tail)
  let pair := convergentPair coeffs
  let q := pair.current.denominator
  let previous := pair.previous.denominator
  have previousPositive : Nat.le Nat.one previous :=
    Nat.le_trans (fibonacci_succ_pos (coefficientCount tail))
      (denominator_bounds head (.cons second tail) h).right
  have increases : Nat.lt q ((a.mul q).add previous) :=
    Nat.le_trans (Nat.succ_le_succ (le_positive_mul q ha))
      (Nat.add_le_add_left previousPositive (a.mul q))
  Eq.subst (fun p : ConvergentPair => Nat.lt q p.current.denominator)
    (convergentPair_appendCoefficient coeffs a).symm increases

end Omega.Arithmetic.ContinuedFraction

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Harmonic.ChebyshevHecke.S5
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

Exact matrices and spectral margins for the six-generator sum on the
symmetric powers of degrees one through four.
-/

noncomputable section
@[expose] public section

namespace Omega.Chebyshev.S5

def powFive (n : Nat) : Nat := Nat.rec n1 (fun _ p => p.mul n5) n

/-- The four nonconstant shells, named by their symmetric-power degree. -/
inductive Shell where | degreeOne | degreeTwo | degreeThree | degreeFour

def Shell.degree : Shell → Nat := Shell.rec n1 n2 n3 n4

def i18 := i6.mul (Int.ofNat n3)
def i54 := i18.mul (Int.ofNat n3)
def i74 := i54.add (i5.mul i4)
def i10 := Int.two.mul i5
def i64 := (i4.square).mul i4
def i20 := i4.mul i5

/-- On degree four the outer monomials couple to one another.
The three interior monomials already form individual eigenlines. -/
def matrixEntry (shell : Shell) (row column : Nat) : Int :=
  let delta := fun (r c : Nat) =>
    (Nat.rec (motive := fun _ => Nat → Int)
      (fun c => Nat.rec Int.one (fun _ _ => Int.zero) c)
      (fun _ smaller c => Nat.rec Int.zero (fun k _ => smaller k) c) r) c
  let entry := fun (r c : Nat) => (delta row r).mul (delta column c)
  Shell.rec (i6.mul (delta row column))
    (Int.two.neg.mul (delta row column)) (i18.neg.mul (delta row column))
    (((i10.neg.mul ((entry .zero .zero).add (entry n4 n4))).add
      (i64.mul ((entry .zero n4).add (entry n4 .zero)))).add
      ((i74.neg.mul ((entry n1 n1).add (entry n3 n3))).add (i54.mul (entry n2 n2)))) shell

/-- The first rows of a column agree as Gaussian integers. -/
def ColumnMatches (shell : Shell) (left right rows : Nat) : Prop :=
  Nat.rec (motive := fun _ => Prop) True
    (fun row previous => And previous
      (Eq (coefficient left right row) (Gaussian.ofInt (matrixEntry shell row right)))) rows

/-- Checks all entries in the monomial basis of each symmetric power. -/
def MatrixMatches (shell : Shell) : Prop :=
  let rows := shell.degree.succ
  let col := fun left right => ColumnMatches shell left right rows
  (Nat.rec (motive := fun _ => Nat → Prop) (col .zero)
    (fun l previous r => And (col l.succ r) (previous r.succ)) shell.degree) Nat.zero

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem matrices_match (shell : Shell) : MatrixMatches shell :=
  have row2 {p q : Prop} (hp : p) (hq : q) : And (And True p) q :=
    And.intro (And.intro True.intro hp) hq
  have row3 {p q r : Prop} (hp : p) (hq : q) (hr : r) : And (And (And True p) q) r :=
    And.intro (row2 hp hq) hr
  have row4 {p q r s : Prop} (hp : p) (hq : q) (hr : r) (hs : s) :
      And (And (And (And True p) q) r) s :=
    And.intro (row3 hp hq hr) hs
  have row5 {p q r s t : Prop} (hp : p) (hq : q) (hr : r) (hs : s) (ht : t) :
      And (And (And (And (And True p) q) r) s) t :=
    And.intro (row4 hp hq hr hs) ht
  Shell.rec (motive := MatrixMatches)
    (And.intro (row2 Eq.refl Eq.refl) (row2 Eq.refl Eq.refl))
    (And.intro (row3 Eq.refl Eq.refl Eq.refl)
      (And.intro (row3 Eq.refl Eq.refl Eq.refl) (row3 Eq.refl Eq.refl Eq.refl)))
    (And.intro (row4 Eq.refl Eq.refl Eq.refl Eq.refl)
      (And.intro (row4 Eq.refl Eq.refl Eq.refl Eq.refl)
        (And.intro (row4 Eq.refl Eq.refl Eq.refl Eq.refl) (row4 Eq.refl Eq.refl Eq.refl Eq.refl))))
    (And.intro (row5 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
      (And.intro (row5 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
        (And.intro (row5 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
          (And.intro (row5 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)
            (row5 Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl))))) shell

/-- The diagonal values in the eigenbasis. The negative branch only
distinguishes an additional eigenvalue in degree four. -/
def scaledEigenvalue (shell : Shell) (negativeBranch : Bool) : Int :=
  Shell.rec i6 Int.two.neg i18.neg (Bool.rec i54 i74.neg negativeBranch) shell

/-- Squared eigenvalues of the unnormalized sum. Each generator has scalar
normalization by the positive square root of five before taking symmetric powers. -/
def squaredEigenvalue (shell : Shell) (negativeBranch : Bool) : IntRatio :=
  IntRatio.value (scaledEigenvalue shell negativeBranch).square (powFive shell.degree)

/-- The exact margin after clearing the denominator. -/
def marginNumerator (shell : Shell) (negativeBranch : Bool) : Int :=
  (i20.mul (Int.ofNat (powFive shell.degree))).sub (scaledEigenvalue shell negativeBranch).square

def margin (shell : Shell) (negativeBranch : Bool) : IntRatio :=
  IntRatio.value (marginNumerator shell negativeBranch) (powFive shell.degree)

private theorem positiveFraction (num den : Nat) :
    IntRatio.Lt (IntRatio.ofInt Int.zero) (IntRatio.fraction (Int.ofNat num.succ) den) :=
  let a := Int.ofNat num.succ
  let d := IntRatio.denominator den
  have nz : Not (Eq (Int.zero.mul d) (a.mul Int.one)) :=
    fun h => Int.ofNat_succ_ne_zero num
      ((Int.mul_one a).symm.trans (h.symm.trans (Int.zero_mul d)))
  have nn : Int.NonNeg ((a.mul Int.one).sub (Int.zero.mul d)) :=
    Eq.subst Int.NonNeg
      (Eq.map₂ Int.sub (Int.mul_one a) (Int.zero_mul d)).symm
      (Eq.subst Int.NonNeg (Int.add_zero a).symm (Int.NonNeg.mk num.succ))
  And.intro nn nz

set_option maxRecDepth 25000 in
set_option maxHeartbeats 2000000 in
theorem margin_positive (shell : Shell) (negativeBranch : Bool) :
    IntRatio.Lt (IntRatio.ofInt Int.zero) (margin shell negativeBranch) :=
  Shell.rec (motive := fun shell => IntRatio.Lt (IntRatio.ofInt Int.zero) (margin shell negativeBranch))
    (positiveFraction _ _) (positiveFraction _ _) (positiveFraction _ _)
    (Bool.rec (motive := fun branch => IntRatio.Lt (IntRatio.ofInt Int.zero)
      (margin .degreeFour branch)) (positiveFraction _ _) (positiveFraction _ _) negativeBranch) shell


/-- The degree-four monomial coordinates, in increasing powers of the second variable. -/
structure DegreeFourVector where
  at0 : Int
  at1 : Int
  at2 : Int
  at3 : Int
  at4 : Int

def DegreeFourVector.scale (v : DegreeFourVector) (a : Int) : DegreeFourVector :=
  ⟨a.mul v.at0, a.mul v.at1, a.mul v.at2, a.mul v.at3, a.mul v.at4⟩

def degreeFourAction (v : DegreeFourVector) : DegreeFourVector :=
  let entry := matrixEntry .degreeFour
  let row := fun (r : Nat) =>
    (((((entry r .zero).mul v.at0).add ((entry r n1).mul v.at1)).add
      ((entry r n2).mul v.at2)).add ((entry r n3).mul v.at3)).add ((entry r n4).mul v.at4)
  ⟨row .zero, row n1, row n2, row n3, row n4⟩

inductive DegreeFourLine where
  | outerSum | middle | outerDifference | firstInterior | lastInterior

def DegreeFourLine.vector : DegreeFourLine → DegreeFourVector :=
  let z := Int.zero
  let u := Int.one
  DegreeFourLine.rec ⟨u, z, z, z, u⟩ ⟨z, z, u, z, z⟩ ⟨u, z, z, z, u.neg⟩
    ⟨z, u, z, z, z⟩ ⟨z, z, z, u, z⟩

def DegreeFourLine.negativeBranch : DegreeFourLine → Bool :=
  DegreeFourLine.rec .false .false .true .true .true

set_option maxRecDepth 4000 in
theorem degree_four_eigenline (line : DegreeFourLine) :
    Eq (degreeFourAction line.vector)
      (line.vector.scale (scaledEigenvalue .degreeFour line.negativeBranch)) :=
  DegreeFourLine.rec (motive := fun line =>
    Eq (degreeFourAction line.vector)
      (line.vector.scale (scaledEigenvalue .degreeFour line.negativeBranch)))
    Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl line

/-- Replace the outer two coordinates by their sum and difference. The three
interior coordinates are doubled so the two basis changes compose to (2I). -/
def doubledEigenCoordinates (v : DegreeFourVector) : DegreeFourVector :=
  ⟨v.at0.add v.at4, Int.two.mul v.at1, Int.two.mul v.at2, Int.two.mul v.at3,
    v.at0.sub v.at4⟩

/-- Linear combination of the five eigenvectors, stored with their outer
sum and difference coefficients at slots 0 and 4. -/
def fromEigenCoordinates (v : DegreeFourVector) : DegreeFourVector :=
  ⟨v.at0.add v.at4, v.at1, v.at2, v.at3, v.at0.sub v.at4⟩

theorem degree_four_basis_change (v : DegreeFourVector) :
    And (Eq (fromEigenCoordinates (doubledEigenCoordinates v)) (v.scale Int.two))
      (Eq (doubledEigenCoordinates (fromEigenCoordinates v)) (v.scale Int.two)) :=
  let a := Polynomial.e0
  let b := Polynomial.e1
  let vars := Polynomial.Variables.cons v.at0
    (.cons v.at4 (Polynomial.Variables.nil intRing))
  have left : Eq ((v.at0.add v.at4).add (v.at0.sub v.at4)) (Int.two.mul v.at0) :=
    Polynomial.prove intRing intRingLaws vars ((a.add b).add (a.sub b))
      (Polynomial.Expr.two.mul a) Eq.refl
  have right : Eq ((v.at0.add v.at4).sub (v.at0.sub v.at4)) (Int.two.mul v.at4) :=
    Polynomial.prove intRing intRingLaws vars ((a.add b).sub (a.sub b))
      (Polynomial.Expr.two.mul b) Eq.refl
  have h : Eq (fromEigenCoordinates (doubledEigenCoordinates v)) (v.scale Int.two) :=
    (congrArg (fun x => DegreeFourVector.mk x (Int.two.mul v.at1) (Int.two.mul v.at2)
      (Int.two.mul v.at3) ((v.at0.add v.at4).sub (v.at0.sub v.at4))) left).trans
      (congrArg (DegreeFourVector.mk (Int.two.mul v.at0) (Int.two.mul v.at1) (Int.two.mul v.at2)
        (Int.two.mul v.at3)) right)
  And.intro h h

private theorem value_sub_ofInt (z a : Int) (d : Nat) :
    Eq ((IntRatio.ofInt z).sub (IntRatio.value a d))
      (IntRatio.value ((z.mul (Int.ofNat d)).sub a) d) :=
  Nat.rec (motive := fun d => Eq ((IntRatio.ofInt z).sub (IntRatio.value a d))
      (IntRatio.value ((z.mul (Int.ofNat d)).sub a) d)) Eq.refl
    (fun k _ => Eq.map₂ IntRatio.fraction
      (congrArg ((z.mul (Int.ofNat k.succ)).add) (Int.mul_one a.neg)) (Nat.one_mul k)) d

theorem margin_eq_difference (shell : Shell) (negativeBranch : Bool) :
    Eq (margin shell negativeBranch)
      ((IntRatio.ofInt i20).sub (squaredEigenvalue shell negativeBranch)) :=
  (value_sub_ofInt i20 (scaledEigenvalue shell negativeBranch).square
    (powFive shell.degree)).symm

end Omega.Chebyshev.S5

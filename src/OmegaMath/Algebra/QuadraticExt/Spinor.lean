module
prelude
import all OmegaInit.Prelude
public import OmegaMath.Algebra.QuadraticExt.Operations

/-!
Omega original.

The exact right-angle spinor and the CHSH square in the square-root-two algebra.
-/

noncomputable section
@[expose] public section

namespace Omega

abbrev QSqrt (d : Int) := RatQuadPoly Int.zero d
abbrev QSqrt2 := QSqrt Int.two
abbrev QPhi := RatQuadPoly Int.one Int.one

namespace QSqrt2

open QuadPoly

def scalarRing : CommRingOps QSqrt2 (Equivalent rationalRing) := ring rationalRing
theorem scalarRingLaws : scalarRing.Laws := ringLaws rationalRingLaws

def delta : QSqrt2 := alpha rationalRing

def halfDelta : QSqrt2 := pair FiniteRatio.zero ⟨Int.one, .succ .zero⟩
def half : QSqrt2 := ofScalar rationalRing ⟨Int.one, .succ .zero⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem halfDelta_sq :
    scalarRing.eqv (scalarRing.square halfDelta) half :=
  And.intro rfl rfl

abbrev Spinor := QuadPoly QSqrt2 scalarRing.zero (scalarRing.neg scalarRing.one)

def spinorRing : CommRingOps Spinor (Equivalent scalarRing) := ring scalarRing
theorem spinorRingLaws : spinorRing.Laws := ringLaws scalarRingLaws

def u90 : Spinor := pair halfDelta halfDelta

def i : Spinor := alpha scalarRing

def normSq (z : Spinor) : QSqrt2 :=
  scalarRing.add (scalarRing.square z.scalar) (scalarRing.square z.linear)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem u90_normSq : scalarRing.eqv (normSq u90) scalarRing.one :=
  scalarRingLaws.trans (scalarRingLaws.add_congr halfDelta_sq halfDelta_sq)
    (And.intro rfl rfl)

private theorem same_coordinates_square (h : QSqrt2) :
    Equivalent scalarRing (square scalarRing (pair h h : Spinor))
      (pair scalarRing.zero (scalarRing.add (scalarRing.square h) (scalarRing.square h))) :=
  let vars := Polynomial.Variables.cons h (Polynomial.Variables.nil scalarRing)
  let x := Polynomial.e0
  let s := x.square
  let z := Polynomial.Expr.zero
  let o := Polynomial.Expr.one
  And.intro
    (Polynomial.prove scalarRing scalarRingLaws vars (s.add (o.neg.mul s)) z rfl)
    (Polynomial.prove scalarRing scalarRingLaws vars ((s.add s).add (z.mul s)) (s.add s) rfl)

theorem u90_sq : spinorRing.eqv (spinorRing.square u90) i :=
  spinorRingLaws.trans (same_coordinates_square halfDelta)
    (And.intro (scalarRingLaws.refl scalarRing.zero) u90_normSq)

private theorem i_sq : spinorRing.eqv (spinorRing.square i) (spinorRing.neg spinorRing.one) :=
  let law := scalarRingLaws
  QuadPoly.trans law (alpha_sq law) (And.intro (law.refl _) (law.symm law.neg_zero))

private theorem neg_one_sq :
    spinorRing.eqv (spinorRing.square (spinorRing.neg spinorRing.one)) spinorRing.one :=
  Polynomial.prove spinorRing spinorRingLaws (Polynomial.Variables.nil spinorRing)
    Polynomial.Expr.one.neg.square Polynomial.Expr.one rfl

def twoNat : Nat := .succ (.succ .zero)
def fourNat : Nat := twoNat.add twoNat

private theorem u90_pow_two :
    spinorRing.eqv (pow scalarRing u90 twoNat) i :=
  spinorRingLaws.trans
    (spinorRingLaws.mul_congr (spinorRingLaws.refl u90) (spinorRingLaws.mul_one u90)) u90_sq

private theorem u90_pow_four :
    spinorRing.eqv (pow scalarRing u90 fourNat) (spinorRing.neg spinorRing.one) :=
  spinorRingLaws.trans (pow_add scalarRingLaws u90 twoNat twoNat)
    (spinorRingLaws.trans (spinorRingLaws.mul_congr u90_pow_two u90_pow_two) i_sq)

theorem u90_pow_eight :
    spinorRing.eqv (pow scalarRing u90 (Nat.add fourNat fourNat)) spinorRing.one :=
  spinorRingLaws.trans (pow_add scalarRingLaws u90 fourNat fourNat)
    (spinorRingLaws.trans (spinorRingLaws.mul_congr u90_pow_four u90_pow_four) neg_one_sq)

def bell : QSqrt2 := scalarRing.add delta delta

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem bell_square :
    scalarRing.eqv (scalarRing.square bell)
      (ofScalar rationalRing (FiniteRatio.ofInt (Int.two.mul (Int.two.mul Int.two)))) :=
  And.intro rfl rfl

end QSqrt2
end Omega

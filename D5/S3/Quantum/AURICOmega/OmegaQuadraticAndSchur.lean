/- GID: D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quadratic norms, golden powers, rational Gram identity and Schur completion. -/

module
prelude
public import OmegaMath.Algebra.QuadraticExt.Fibonacci
public import OmegaMath.Algebra.QuadraticExt.Spinor
public import OmegaMath.Matrix.LagrangeSchur.Gram
public import OmegaMath.Matrix.LagrangeSchur.Schur

namespace D5.S3.Quantum.AURICOmega.OmegaQuadraticAndSchur

open Omega Omega.QuadPoly Omega.LagrangeSchur

/-- The quadratic norm multiplies for all integral parameters. -/
public theorem quadratic_norm_mul (b c : Int) (z w : RatQuadPoly b c) :
    FiniteRatio.Equivalent (norm rationalRing (mul rationalRing z w))
      ((norm rationalRing z).mul (norm rationalRing w)) :=
  norm_mul rationalRingLaws z w

/-- Nonzero norm gives an exact inverse in the rational quadratic algebra. -/
public theorem quadratic_mul_inv (b c : Int) (z : RatQuadPoly b c)
    (h : Not (Eq (norm rationalRing z).num Int.zero)) :
    Equivalent rationalRing (mul rationalRing z z.inv) (QuadPoly.one rationalRing) :=
  RatQuadPoly.mul_inv z h

/-- Every positive power of the golden generator has Fibonacci coefficients. -/
public theorem phi_fibonacci (n : Nat) :
    Equivalent rationalRing (pow rationalRing (alpha (b := rationalRing.one) (c := rationalRing.one) rationalRing) n.succ)
      (pair (fibonacci rationalRing n) (fibonacci rationalRing n.succ)) :=
  phi_pow rationalRing rationalRingLaws n

/-- The norm of the golden generator's nth power is minus one to the nth power. -/
public theorem phi_power_norm (n : Nat) :
    FiniteRatio.Equivalent (norm rationalRing (pow rationalRing (alpha (b := rationalRing.one) (c := rationalRing.one) rationalRing) n))
      (negOnePow rationalRing n) :=
  norm_phi_pow rationalRing rationalRingLaws n

/-- The right-angle spinor is unit and its eighth power is the identity. -/
public theorem sqrt_two_spinor :
    And (QSqrt2.scalarRing.eqv (QSqrt2.normSq QSqrt2.u90) QSqrt2.scalarRing.one)
      (QSqrt2.spinorRing.eqv (pow QSqrt2.scalarRing QSqrt2.u90 (Nat.add QSqrt2.fourNat QSqrt2.fourNat))
        QSqrt2.spinorRing.one) :=
  And.intro QSqrt2.u90_normSq QSqrt2.u90_pow_eight

/-- The squared CHSH value is eight in the square-root-two algebra. -/
public theorem sqrt_two_bell :
    QSqrt2.scalarRing.eqv (QSqrt2.scalarRing.square QSqrt2.bell)
      (ofScalar rationalRing (FiniteRatio.ofInt (Int.two.mul (Int.two.mul Int.two)))) :=
  QSqrt2.bell_square

/-- The rational Gram determinant equals the sum of squared two-coordinate minors. -/
public theorem rational_lagrange_gram (xs : Sequence (CoordinatePair FiniteRatio)) :
    FiniteRatio.Equivalent (gramDet rationalRing xs) (minorSquares rationalRing xs) :=
  lagrange_gram rationalRing rationalRingLaws xs

/-- Every finite rational coordinate sequence satisfies Cauchy–Schwarz. -/
public theorem rational_cauchy_schwarz (xs : Sequence (CoordinatePair FiniteRatio)) :
    (FiniteRatio.square (sumUV rationalRing xs)).Le
      ((sumU2 rationalRing xs).mul (sumV2 rationalRing xs)) :=
  Omega.LagrangeSchur.rational_cauchy_schwarz xs

/-- Completion of the square holds for either sign of the nonzero pivot. -/
public theorem rational_schur_complete (a b c x y : FiniteRatio) (hc : Not (Eq c.num Int.zero)) :
    FiniteRatio.Equivalent (scalarForm a b c x y)
      ((schurValue a b c x).add (schurSquare b c x y)) :=
  scalar_schur_complete a b c x y hc

/-- A positive pivot makes the Schur residual an attained global minimum. -/
public theorem rational_schur_min (a b c x : FiniteRatio) (hc : FiniteRatio.zero.Lt c) :
    And (∀ y : FiniteRatio, (schurValue a b c x).Le (scalarForm a b c x y))
      (FiniteRatio.Equivalent (scalarForm a b c x (schurMinPoint b c x)) (schurValue a b c x)) :=
  scalar_schur_min a b c x hc

end D5.S3.Quantum.AURICOmega.OmegaQuadraticAndSchur

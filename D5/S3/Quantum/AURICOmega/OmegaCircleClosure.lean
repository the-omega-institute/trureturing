/- GID: D5/S3/Quantum/AURICOmega/OmegaCircleClosure
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaCircleClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed projective overlap, antipodal closure and Cayley circle composition. -/

module
prelude
public import OmegaMath.Projective.Circle

namespace D5.S3.Quantum.AURICOmega.OmegaCircleClosure

open Omega Omega.Projective.Circle

/-- Every nonzero signed scale preserves the overlap. -/
public theorem kappa_scale (p q k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (kappa (k.mul p) (k.mul q)) (kappa p q) :=
  Omega.Projective.Circle.kappa_scale p q k hk

/-- The overlap and spread sum to one at every projective point. -/
public theorem kappa_add_spread_eq_one (p q : Int) (h : Nonzero p q) :
    IntRatio.Equivalent ((kappa p q).add (spread p q)) (IntRatio.ofInt Int.one) :=
  Omega.Projective.Circle.kappa_add_spread_eq_one p q h

/-- The Cayley image of every nonzero homogeneous pair is a unit vector. -/
public theorem cayley_circle_unit (p q : Int) (h : Nonzero p q) :
    IntRatio.Equivalent (((cayleyX p q).mul (cayleyX p q)).add
      ((cayleyY p q).mul (cayleyY p q))) (IntRatio.ofInt Int.one) :=
  Omega.Projective.Circle.cayley_circle_unit p q h

/-- The projective point at infinity has a finite reading and maps to the antipode. -/
public theorem cayley_antipodal_closure (p : Int) (hp : Not (Eq p Int.zero)) :
    And (IntRatio.Equivalent (kappa p Int.zero) (IntRatio.ofInt Int.zero))
      (And (IntRatio.Equivalent (spread p Int.zero) (IntRatio.ofInt Int.one))
        (And (IntRatio.Equivalent (cayleyX p Int.zero) (IntRatio.ofInt Int.one.neg))
          (IntRatio.Equivalent (cayleyY p Int.zero) (IntRatio.ofInt Int.zero)))) :=
  Omega.Projective.Circle.cayley_antipodal_closure p hp

/-- Homogeneous multiplication multiplies the two squared norms. -/
public theorem projective_circle_mul_normSq (p₁ q₁ p₂ q₂ : Int) :
    Eq ((normSq p₁ q₁).mul (normSq p₂ q₂)) (projectiveMul p₁ q₁ p₂ q₂).normSq :=
  Omega.Projective.Circle.projective_circle_mul_normSq p₁ q₁ p₂ q₂

end D5.S3.Quantum.AURICOmega.OmegaCircleClosure

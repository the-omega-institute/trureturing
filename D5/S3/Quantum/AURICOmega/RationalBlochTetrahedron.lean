/- GID: D5/S3/Quantum/AURICOmega/RationalBlochTetrahedron
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/RationalBlochTetrahedron
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three rational Bloch unit vectors cannot share the tetrahedral inner product. -/

module
prelude
public import OmegaMath.Geometry.BargmannGram.PureTetrahedron

namespace D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron

open Omega Omega.Geometry.BargmannGram

/-- Three Bloch unit vectors with rational coordinates and common inner product
`-1/3` are impossible. The coordinates are cleared by a common denominator. -/
public theorem no_rational_bloch_tetrahedral_triangle
    (a b : Quad4) (denominator : Nat) (c : Quad4) (hden : Not (Eq denominator Nat.zero))
    (ha : Eq a.w Int.zero) (hb : Eq b.w Int.zero) (hc : Eq c.w Int.zero)
    (haa : Eq (a.dot a) (Int.ofNat (denominator.mul denominator)))
    (hbb : Eq (b.dot b) (Int.ofNat (denominator.mul denominator)))
    (hcc : Eq (c.dot c) (Int.ofNat (denominator.mul denominator)))
    (hab : Eq ((Int.ofNat Nat.one.succ.succ).mul (a.dot b))
      (Int.ofNat (denominator.mul denominator)).neg)
    (hbc : Eq ((Int.ofNat Nat.one.succ.succ).mul (b.dot c))
      (Int.ofNat (denominator.mul denominator)).neg)
    (hca : Eq ((Int.ofNat Nat.one.succ.succ).mul (c.dot a))
      (Int.ofNat (denominator.mul denominator)).neg) :
    False :=
  no_pure_tetrahedral_gram a b c denominator hden ha hb hc haa hbb hcc hab hbc hca

end D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron

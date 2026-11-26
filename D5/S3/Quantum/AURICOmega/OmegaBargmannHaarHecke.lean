/- GID: D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational Gram doubling, Haar characters, the norm-five Hecke sum and quaternion divisibility. -/

module
prelude
public import OmegaMath.Geometry.BargmannGram
public import OmegaMath.Harmonic.PiFreeHaar
public import OmegaMath.Computability.QuaternionFractran

namespace D5.S3.Quantum.AURICOmega.OmegaBargmannHaarHecke

open Omega
open Omega.Geometry.BargmannGram
open Omega.Harmonic.PiFreeHaar
open Omega.Computability.QuaternionFractran
open Omega.IntRatio (Equivalent)

/-- The normalized Gram determinant is nonnegative on three nonzero integer quaternions. -/
public theorem detGram3_nonneg (a b c : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero)) :
    IntRatio.Le (IntRatio.ofInt Int.zero) (detGram3 a b c) :=
  Omega.Geometry.BargmannGram.detGram3_nonneg a b c ha hb hc

/-- The quaternion triad for great-circle doubling has zero Gram determinant. -/
public theorem geodesic_doubling_detGram3_zero (a b : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) :
    Equivalent (detGram3 a b (triad b a b)) (IntRatio.ofInt Int.zero) :=
  Omega.Geometry.BargmannGram.geodesic_doubling_detGram3_zero a b ha hb

/-- Projective fidelity after doubling is the square of twice the original fidelity minus one. -/
public theorem geodesic_doubling_kappa (a b : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) :
    Equivalent (kappa a (triad b a b))
      ((doublingReadout a b).mul (doublingReadout a b)) :=
  Omega.Geometry.BargmannGram.geodesic_doubling_kappa a b ha hb

/-- The consecutive even scalar-coordinate moments satisfy the factorial ratio recurrence. -/
public theorem haarKappaMoment_succ (k : Nat) :
    Equivalent (haarKappaMoment k.succ) ((haarKappaMoment k).mul (haarKappaStep k)) :=
  Omega.Harmonic.PiFreeHaar.haarKappaMoment_succ k

/-- The first three even characters have identity Gram matrix under the rational moment functional. -/
public theorem peter_weyl_chi012_orthonormal :
    And (Equivalent (haarInner chi0 chi0) (IntRatio.ofInt Int.one))
      (And (Equivalent (haarInner chi0 chi1) (IntRatio.ofInt Int.zero))
      (And (Equivalent (haarInner chi0 chi2) (IntRatio.ofInt Int.zero))
      (And (Equivalent (haarInner chi1 chi1) (IntRatio.ofInt Int.one))
      (And (Equivalent (haarInner chi1 chi2) (IntRatio.ofInt Int.zero))
           (Equivalent (haarInner chi2 chi2) (IntRatio.ofInt Int.one)))))) :=
  Omega.Harmonic.PiFreeHaar.peter_weyl_chi012_orthonormal

/-- The unnormalized six-spinor sum acts on the first even character by −2/5. -/
public theorem heckeT5_chi1_eigenvalue (q : Quad4) (hq : Not (Eq q Quad4.zero)) :
    Equivalent (heckeT5Chi1 q)
      ((IntRatio.value Int.two.neg Nat.one.succ.succ.succ.succ).mul (evalChi1 q)) :=
  Omega.Harmonic.PiFreeHaar.heckeT5_chi1_eigenvalue q hq

/-- The difference between twenty and the squared eigenvalue is strictly positive. -/
public theorem heckeT5_ramanujan_margin :
    let four := Nat.one.succ.succ.succ
    let five := four.succ
    let nine := five.succ.succ.succ.succ
    let ten := nine.succ
    let fourNinetySix := (((four.mul ten).add nine).mul ten).add five.succ
    let eigenvalue := IntRatio.value Int.two.neg five
    let margin := IntRatio.value (Int.ofNat fourNinetySix) (five.mul five)
    And (Equivalent ((IntRatio.ofInt (Int.ofNat (four.mul five))).sub (eigenvalue.mul eigenvalue)) margin)
      (IntRatio.Lt (IntRatio.ofInt Int.zero) margin) :=
  Omega.Harmonic.PiFreeHaar.heckeT5_ramanujan_margin

/-- Two outputs for the same state, rotor and nonzero denominator agree. -/
public theorem quaternion_fractran_deterministic {psi A q₁ q₂ : Quad4} {p : Int}
    (hp : Not (Eq p Int.zero))
    (h₁ : Eq (psi.mul A) (Quad4.scale p q₁))
    (h₂ : Eq (psi.mul A) (Quad4.scale p q₂)) : Eq q₁ q₂ :=
  Omega.Computability.QuaternionFractran.quaternion_fractran_deterministic hp h₁ h₂

/-- The two opposite words have equal norm, while the Y-unwind gate accepts only XY. -/
public theorem quaternion_fractran_order_separation :
    And (Eq psiXY.normSq (unwindDenominator.mul unwindDenominator))
      (And (Eq psiYX.normSq (unwindDenominator.mul unwindDenominator))
        (And (Step psiXY gateUnwindY unwindDenominator psiX)
          (Not (Enabled psiYX gateUnwindY unwindDenominator)))) :=
  Omega.Computability.QuaternionFractran.quaternion_fractran_order_separation

end D5.S3.Quantum.AURICOmega.OmegaBargmannHaarHecke

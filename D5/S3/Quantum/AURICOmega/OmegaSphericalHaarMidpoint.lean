/- GID: D5/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaSphericalHaarMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-degree rational Haar orthonormality, spherical triangle laws, and Cayley midpoint drift. -/

module
prelude
public import D5.S3.Fourier.AllDegreeHaar
public import D5.S3.Geometry.BargmannGram.SphericalLaws
public import D5.S3.Calculus.MidpointDrift

namespace D5.S3.Quantum.AURICOmega.OmegaSphericalHaarMidpoint

open Omega
open Omega.IntRatio (Equivalent)
open Omega.Calculus.MidpointDrift (RationalQuaternion alphaSample midpointStep)
open Omega.Harmonic.PiFreeHaar (haarKappaPoly haarInner)
open Omega.Harmonic.AllDegreeHaar (Poly evenCharPoly evenCharProductSum zeroDelta degreeDelta)
open Omega.Geometry.BargmannGram (Quad4 kappa)
open Omega.Geometry.SphericalLaws (spread vertexSpread)

/-- The product of the degree-`2m` and degree-`2n` characters is the inclusive
sum from index `|m - n|` to `m + n`, coefficientwise. -/
public theorem evenChar_product_sum (m n : Nat) :
    Poly.RatioSame ((evenCharPoly m).mul (evenCharPoly n)) (evenCharProductSum m n) :=
  Omega.Harmonic.AllDegreeHaar.evenChar_product_sum m n

/-- The factorial moment functional sends the trivial character to one and
every positive-degree even character to zero. -/
public theorem haar_evenChar_expectation (r : Nat) :
    Equivalent (haarKappaPoly (evenCharPoly r)) (zeroDelta r) :=
  Omega.Harmonic.AllDegreeHaar.haar_evenChar_expectation r

/-- Every pair of even characters has the Kronecker-delta Haar inner product. -/
public theorem all_degree_peter_weyl_orthonormal (m n : Nat) :
    Equivalent (haarInner (evenCharPoly m) (evenCharPoly n)) (degreeDelta m n) :=
  Omega.Harmonic.AllDegreeHaar.all_degree_peter_weyl_orthonormal m n

/-- Vertex spread divided by opposite edge spread is invariant under cycling. -/
public theorem rational_spherical_sine_law (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (sab : Not (Equivalent (spread a b) IntRatio.zero))
    (sbc : Not (Equivalent (spread b c) IntRatio.zero))
    (sca : Not (Equivalent (spread c a) IntRatio.zero)) :
    And (Equivalent ((vertexSpread a b c).mul (spread b c).inv)
          ((vertexSpread b c a).mul (spread c a).inv))
        (Equivalent ((vertexSpread b c a).mul (spread c a).inv)
          ((vertexSpread c a b).mul (spread a b).inv)) :=
  Omega.Geometry.SphericalLaws.rational_spherical_sine_law a b c ha hb hc sab sbc sca

/-- At a right vertex, the opposite fidelity is the product of the two
incident fidelities. -/
public theorem rational_spherical_pythagorean (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (right : Eq ((a.dot a).mul (b.dot c)) ((a.dot b).mul (a.dot c))) :
    Equivalent (kappa b c) ((kappa a b).mul (kappa c a)) :=
  Omega.Geometry.SphericalLaws.rational_spherical_pythagorean a b c ha hb hc right

/-- For a pure generator and unit initial quaternion, the exact squared-norm
drift is the squared displacement times `1 - 2α`. -/
public theorem alpha_sampling_norm_drift (weight : IntRatio) (a x₀ : RationalQuaternion)
    (finite : weight.Finite) (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) :
    let x := alphaSample weight a x₀ finite
    Equivalent (x.normSq.sub IntRatio.one)
      ((IntRatio.one.sub (IntRatio.two.mul weight)).mul (x.sub x₀).normSq) :=
  Omega.Calculus.MidpointDrift.alpha_sampling_norm_drift weight a x₀ finite pure unit

/-- Sampling at one half preserves the unit norm for every rational pure generator. -/
public theorem midpoint_unit_norm (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) : (midpointStep a x₀).IsUnit :=
  Omega.Calculus.MidpointDrift.midpoint_unit_norm a x₀ pure unit

/-- The two legs of the midpoint triad have equal projective fidelity. -/
public theorem midpoint_half_step_fidelity (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) :
    let h := (midpointStep a x₀).num
    Equivalent (Ternion.kappa x₀.num h) (Ternion.kappa h (Ternion.triad h x₀.num h)) :=
  Omega.Calculus.MidpointDrift.midpoint_half_step_fidelity a x₀ pure unit

end D5.S3.Quantum.AURICOmega.OmegaSphericalHaarMidpoint

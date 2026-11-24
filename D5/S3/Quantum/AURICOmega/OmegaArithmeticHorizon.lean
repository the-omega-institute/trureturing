/- GID: D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaArithmeticHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive prime escape, Bézout coefficients, continued fractions, Machin's rational chain and the integer quarter-depth bound. -/

module
prelude
public import OmegaMath.Arithmetic.Euclidean
public import OmegaMath.Arithmetic.ContinuedFraction
public import OmegaMath.Arithmetic.DepthBudget

namespace D5.S3.Quantum.AURICOmega.OmegaArithmeticHorizon

open Omega Omega.Arithmetic Omega.Arithmetic.ContinuedFraction

/-- A finite list with positive product admits an escaping prime divisor. -/
public theorem euclid_prime_escape (s : NatList) (hs : Nat.lt Nat.zero s.prod) :
    Exists (fun p => And (IsPrime p) (And (Dvd p s.prod.succ) (Not (NatList.Mem p s)))) :=
  Omega.Arithmetic.prime_escape s hs

/-- Every pair of natural numbers admits signed Bézout coefficients. -/
public theorem bezout_identity (a b : Nat) :
    Exists (fun x : Int => Exists (fun y : Int =>
      Eq (((Int.ofNat a).mul x).add ((Int.ofNat b).mul y)) (Int.ofNat (gcd a b)))) :=
  Omega.Arithmetic.bezout_identity a b

/-- The current and preceding continuants have alternating unit determinant. -/
public theorem cf_convergent_determinant (coeffs : NatList) :
    Eq (convergentPair coeffs).determinant (alternatingSign (coefficientCount coeffs)) :=
  eulerWallis coeffs

/-- A common divisor of a convergent's numerator and denominator equals one. -/
public theorem cf_convergent_coprime (coeffs : NatList) (d : Nat)
    (hn : Dvd d (convergentPair coeffs).current.numerator)
    (hd : Dvd d (convergentPair coeffs).current.denominator) : Eq d Nat.one :=
  convergent_coprime coeffs d hn hd

/-- Two rational tangent doublings and the Machin correction give one. -/
public theorem machin_rational_chain :
    IntRatio.Equivalent machinChain (IntRatio.ofInt Int.one) :=
  machin_chain_to_one

/-- The computed depth certifies strict integer decay at every admissible depth. -/
public theorem quarterDepth_integer_sound (c d p q N : Nat)
    (hd : Nat.lt Nat.zero d) (hp : Nat.lt Nat.zero p) (h : Nat.le (quarterDepth c d p q) N) :
    Nat.lt (c.mul q) ((d.mul p).mul (pow4 N.succ)) :=
  Omega.Arithmetic.quarterDepth_integer_sound c d p q N hd hp h

end D5.S3.Quantum.AURICOmega.OmegaArithmeticHorizon

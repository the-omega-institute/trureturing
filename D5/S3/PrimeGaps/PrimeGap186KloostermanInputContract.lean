/- GID: D5/S3/PrimeGaps/PrimeGap186KloostermanInputContract
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isolate the two finite-field Kloosterman estimates used by the conditional DHL[40,2] source. -/

import Mathlib

namespace D5.S3.PrimeGaps.PrimeGap186KloostermanInputContract

open scoped BigOperators
open AddChar

/-- The rank-three hyper-Kloosterman sum in the exact normalization used by the 186 source. -/
noncomputable def normalizedKloosterman3 (p : Nat) [Fact p.Prime]
    (c : ZMod p) : Complex :=
  (p : Complex)⁻¹ *
    ∑ u : ZMod p, ∑ v : ZMod p, ∑ w : ZMod p,
      if u * v * w = c then ZMod.stdAddChar (u + v + w) else 0

/-- The unnormalized classical rank-two Kloosterman sum over units. -/
noncomputable def unnormalizedKloosterman2 (p : Nat) [Fact p.Prime]
    (c : ZMod p) : Complex :=
  ∑ u : (ZMod p)ˣ,
    ZMod.stdAddChar ((u : ZMod p) + c / (u : ZMod p))

/-- First exact analytic input of the upstream conditional proof. This is a proposition, not a
repository axiom. -/
def Kloosterman3Bound : Prop :=
  ∀ (p : Nat) [Fact p.Prime] (c : ZMod p),
    c ≠ 0 → ‖normalizedKloosterman3 p c‖ ≤ (3 : Real)

/-- Second exact analytic input of the upstream conditional proof. -/
def Kloosterman2CorrelationBound : Prop :=
  ∀ (p : Nat) [Fact p.Prime] (A B : ZMod p),
    A ≠ 0 → B ≠ 0 →
      ‖∑ t : ZMod p, if t ≠ 0 ∧ t ≠ -1 then
        unnormalizedKloosterman2 p (A / t) *
          unnormalizedKloosterman2 p (B / (t + 1)) else 0‖ ≤
        8 * (p : Real) * Real.sqrt (p : Real)

/-- The algebraic-geometric finite-field input pair can now be tracked independently of the
numerical physical-integral certificate. -/
def KloostermanInputPackage : Prop :=
  Kloosterman3Bound ∧ Kloosterman2CorrelationBound

#print axioms normalizedKloosterman3
#print axioms unnormalizedKloosterman2
#print axioms Kloosterman3Bound
#print axioms Kloosterman2CorrelationBound
#print axioms KloostermanInputPackage

end D5.S3.PrimeGaps.PrimeGap186KloostermanInputContract

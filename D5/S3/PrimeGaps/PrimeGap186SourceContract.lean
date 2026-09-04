/- GID: D5/S3/PrimeGaps/PrimeGap186SourceContract
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stabilize the public theorem surface of the 2026 conditional PrimeGaps186 formalization without importing its unproved inputs as repository axioms. -/

import D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

/-!
# PrimeGaps186 external source contract

This module copies only the public mathematical surface of
`openai/PrimeGaps186` commit `61340d0b74163003b32756bb16e91d9209a5e330`.
The upstream solution proves its three headline declarations conditionally on
three explicit project axioms: a rank-three hyper-Kloosterman estimate, a
rank-two Kloosterman correlation estimate, and a finite physical-integral/cap
certificate. Those inputs are not introduced here as axioms.

The purpose of this module is to give downstream trureturing nodes a stable,
axiom-free contract. A later proof-body port can discharge the contract after
its Lean/mathlib pin and source-bound admission have been reconciled.
-/

namespace D5.S3.PrimeGaps.PrimeGap186SourceContract

open D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

/-- Admissibility in the exact form used by the upstream `DHL[40,2]` theorem. The generic
owner is `DirectTupleAdmissible`; this fixed-source name is only a compatibility alias. -/
abbrev AdmissibleIntegerTuple := DirectTupleAdmissible

/-- The exact theorem-level `DHL[40,2]` proposition exported by the upstream source. -/
def DHL40Two : Prop :=
  ∀ H : Finset Int, H.card = 40 → AdmissibleIntegerTuple H →
    Set.Infinite {n : Int | 2 ≤ (H.filter fun h => (n + h).toNat.Prime).card}

/-- The extended-real lower limit of consecutive prime gaps used by the source. -/
noncomputable def primeGapLiminf : EReal :=
  Filter.liminf
    (fun n : Nat =>
      (Nat.nth Nat.Prime (n + 1) : EReal) - (Nat.nth Nat.Prime n : EReal))
    Filter.atTop

/-- The exact final source-level conclusion, represented as a proposition rather than a new
repository axiom. -/
def PrimeGapLiminfAtMost186 : Prop :=
  primeGapLiminf ≤ (186 : EReal)

#print axioms AdmissibleIntegerTuple
#print axioms DHL40Two
#print axioms primeGapLiminf
#print axioms PrimeGapLiminfAtMost186

end D5.S3.PrimeGaps.PrimeGap186SourceContract

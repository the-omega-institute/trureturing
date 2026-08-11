/- GID: D5/S1/Dynamics/OnticStateCoordinates
   generality: I
   mirror-B: D5/B/S1/Dynamics/OnticStateCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: States are equivalent to five coordinates with a canonical prime-ledger code. -/

import D5.S1.Digit.PrimeAxisEncoding

/- Provenance: repository-local constrained-coordinate equivalence built from
   `D5.S1.Digit.primeAxisEncoding`; bundled bijectivity is exposed through
   pinned Mathlib's `Equiv.bijective`. -/

namespace D5.S1.Dynamics.OnticStateCoordinates

open D5.S1.Digit

universe u v w

/-- A state stores a prime-exponent ledger together with its phase, finite
readout, and ledger coordinates. Its positive-natural code is derived
canonically rather than stored independently. -/
structure OnticState (Phase : Type u) (Readout : Type v) (Ledger : Type w) where
  primeLedger : PrimeAxisTable
  phase : Phase
  readout : Readout
  ledger : Ledger

/-- The five-coordinate presentation, with a proof that the code coordinate
is exactly the canonical encoding of the prime ledger. -/
structure CanonicalFiveCoordinates
    (Phase : Type u) (Readout : Type v) (Ledger : Type w) where
  primeLedger : PrimeAxisTable
  code : ℕ+
  code_eq : code = primeAxisEncoding primeLedger
  phase : Phase
  readout : Readout
  ledger : Ledger

/-- Forgetting the dependent code coordinate and recomputing it canonically
gives an equivalence between states and their constrained five coordinates. -/
noncomputable def onticStateEquivCoordinates
    {Phase : Type u} {Readout : Type v} {Ledger : Type w} :
    OnticState Phase Readout Ledger ≃ CanonicalFiveCoordinates Phase Readout Ledger where
  toFun state :=
    { primeLedger := state.primeLedger
      code := primeAxisEncoding state.primeLedger
      code_eq := rfl
      phase := state.phase
      readout := state.readout
      ledger := state.ledger }
  invFun coordinates :=
    { primeLedger := coordinates.primeLedger
      phase := coordinates.phase
      readout := coordinates.readout
      ledger := coordinates.ledger }
  left_inv state := by
    cases state
    rfl
  right_inv coordinates := by
    cases coordinates with
    | mk primeLedger code code_eq phase readout ledger =>
        cases code_eq
        rfl

/-- The constrained five-coordinate presentation is lossless: every state has
one such presentation and every valid presentation recovers one state. -/
theorem canonical_five_coordinates_bijective
    {Phase : Type u} {Readout : Type v} {Ledger : Type w} :
    Function.Bijective
      (onticStateEquivCoordinates :
        OnticState Phase Readout Ledger →
          CanonicalFiveCoordinates Phase Readout Ledger) :=
  onticStateEquivCoordinates.bijective

end D5.S1.Dynamics.OnticStateCoordinates

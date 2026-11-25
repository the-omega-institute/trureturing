/- GID: D5/S0/Carrier/TraceConjugation
   generality: G
   mirror-B: D5/B/S0/Carrier/TraceConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden trace is invariant under Galois conjugation. -/

module
prelude
public import D5.S0.Carrier.QuadraticExtension.Basic

namespace D5.S0.Carrier

open Omega Omega.QuadPoly

/-- Conjugation preserves the integral trace of a golden integer. -/
public theorem trace_conj (x : IntQuadPoly Int.one Int.one) :
    Eq (trace intRing (conj intRing x)) (trace intRing x) :=
  QuadPoly.trace_conj intRingLaws x

end D5.S0.Carrier

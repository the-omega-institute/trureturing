/- GID: D5/S0/Carrier/TraceConjugation
   generality: G
   mirror-B: D5/B/S0/Carrier/TraceConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden trace is invariant under Galois conjugation. -/

import D5.S0.Carrier.Conj

namespace D5.S0.Carrier

@[simp] theorem trace_conj (x : GoldenInt) : trace (conj x) = trace x := by
  simp [trace]
  ring

end D5.S0.Carrier

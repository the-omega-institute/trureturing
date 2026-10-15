/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group15
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket05
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16281 (e 13) (e 15) (e 19)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x15 x17 x19 : Fin 4),
    (-1227987909 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16281 x13 x15 x19 ≤ PreparedEJMCompleteMiniCut01137Tables.normal16273 x13 x15 x17 x19 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-1227987909 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group15.normalizedAt e := by
  exact receipt (e 13) (e 15) (e 17) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket05

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket02
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group06
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket06
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16299 (e 15) (e 16) (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x14 x15 x16 x18 : Fin 4),
    (0 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16299 x15 x16 x18 ≤ PreparedEJMCompleteMiniCut01137Tables.normal16292 x14 x16 x18 + PreparedEJMCompleteMiniCut01137Tables.normal16278 x14 x15 x16 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (0 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group06.normalizedAt e + PreparedEJMCompleteMiniCut01137Bucket02.lowerAt e := by
  exact receipt (e 14) (e 15) (e 16) (e 18)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket06

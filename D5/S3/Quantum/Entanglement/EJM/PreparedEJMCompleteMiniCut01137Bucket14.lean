/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket04
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket13
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket14
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16305 (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x15 x18 : Fin 4),
    (-848005158 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16305 x18 ≤ PreparedEJMCompleteMiniCut01137Tables.normal16298 x15 x18 + PreparedEJMCompleteMiniCut01137Tables.normal16304 x15 x18 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-848005158 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Bucket04.lowerAt e + PreparedEJMCompleteMiniCut01137Bucket13.lowerAt e := by
  exact receipt (e 15) (e 18)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket14

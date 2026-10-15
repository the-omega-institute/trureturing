/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket09
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket11
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket12
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Group04
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket13
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16304 (e 15) (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x15 x18 : Fin 4),
    (-1006414852 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16304 x15 x18 ≤ PreparedEJMCompleteMiniCut01137Tables.normal1871 x13 x15 x18 + PreparedEJMCompleteMiniCut01137Tables.normal16285 x13 x18 + PreparedEJMCompleteMiniCut01137Tables.normal16302 x13 x15 x18 + PreparedEJMCompleteMiniCut01137Tables.normal16303 x13 x15 x18 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-1006414852 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group04.normalizedAt e + PreparedEJMCompleteMiniCut01137Bucket09.lowerAt e + PreparedEJMCompleteMiniCut01137Bucket11.lowerAt e + PreparedEJMCompleteMiniCut01137Bucket12.lowerAt e := by
  exact receipt (e 13) (e 15) (e 18)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket13

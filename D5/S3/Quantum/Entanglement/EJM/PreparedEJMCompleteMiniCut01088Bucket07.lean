/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket00
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group10
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group11
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket07
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal15489 (e 13) (e 16) (e 19)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x14 x16 x19 : Fin 4),
    (0 : ℤ) + PreparedEJMCompleteMiniCut01088Tables.normal15489 x13 x16 x19 ≤ PreparedEJMCompleteMiniCut01088Tables.normal117 x14 x19 + PreparedEJMCompleteMiniCut01088Tables.normal15478 x13 x14 x16 x19 + PreparedEJMCompleteMiniCut01088Tables.normal2174 x14 x19 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (0 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01088Group10.normalizedAt e + PreparedEJMCompleteMiniCut01088Group11.normalizedAt e + PreparedEJMCompleteMiniCut01088Bucket00.lowerAt e := by
  exact receipt (e 13) (e 14) (e 16) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket07

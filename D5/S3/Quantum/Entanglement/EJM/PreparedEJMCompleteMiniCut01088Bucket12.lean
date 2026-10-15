/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket01
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket06
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket10
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group00
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group05
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Group07
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket12
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal15494 (e 13) (e 15) (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x15 x16 x18 : Fin 4),
    (-1331469095 : ℤ) + PreparedEJMCompleteMiniCut01088Tables.normal15494 x13 x15 x18 ≤ PreparedEJMCompleteMiniCut01088Tables.normal1868 x13 x15 x16 + PreparedEJMCompleteMiniCut01088Tables.normal765 x13 x16 x18 + PreparedEJMCompleteMiniCut01088Tables.normal35 x15 x16 x18 + PreparedEJMCompleteMiniCut01088Tables.normal15483 x13 x16 + PreparedEJMCompleteMiniCut01088Tables.normal15488 x15 x16 x18 + PreparedEJMCompleteMiniCut01088Tables.normal15492 x13 x15 x16 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-1331469095 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01088Group00.normalizedAt e + PreparedEJMCompleteMiniCut01088Group05.normalizedAt e + PreparedEJMCompleteMiniCut01088Group07.normalizedAt e + PreparedEJMCompleteMiniCut01088Bucket01.lowerAt e + PreparedEJMCompleteMiniCut01088Bucket06.lowerAt e + PreparedEJMCompleteMiniCut01088Bucket10.lowerAt e := by
  exact receipt (e 13) (e 15) (e 16) (e 18)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket12

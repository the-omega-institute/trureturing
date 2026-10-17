/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Bucket00
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Bucket00
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Bucket00.inequality_at
   digest: Scoped finite integer inequalities eliminate only their stated outcome variables. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Group01
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Group13
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Group14
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01088.PreparedEJMCompleteMiniCut01088Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket00
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01088Tables.normal2174 (e 14) (e 19)

set_option trace.profiler true in
theorem receipt : ∀ (x14 x17 x19 : Fin 4),
    (-1427477024 : ℤ) + PreparedEJMCompleteMiniCut01088Tables.normal2174 x14 x19 ≤ PreparedEJMCompleteMiniCut01088Tables.normal545 x14 x17 + PreparedEJMCompleteMiniCut01088Tables.normal1877 x17 x19 + PreparedEJMCompleteMiniCut01088Tables.normal1878 x14 x17 x19 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-1427477024 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01088Group01.normalizedAt e + PreparedEJMCompleteMiniCut01088Group13.normalizedAt e + PreparedEJMCompleteMiniCut01088Group14.normalizedAt e := by
  exact receipt (e 14) (e 17) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Bucket00

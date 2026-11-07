/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket11
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket11
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket11.inequality_at
   digest: Scoped finite integer inequalities eliminate only their stated outcome variables. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Bucket08
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group16
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket11
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16302 (e 13) (e 15) (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x15 x18 x19 : Fin 4),
    (-732920220 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16302 x13 x15 x18 ≤ PreparedEJMCompleteMiniCut01137Tables.normal16295 x13 x18 x19 + PreparedEJMCompleteMiniCut01137Tables.normal16284 x15 x18 x19 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-732920220 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group16.normalizedAt e + PreparedEJMCompleteMiniCut01137Bucket08.lowerAt e := by
  exact receipt (e 13) (e 15) (e 18) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket11

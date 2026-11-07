/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket03
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket03
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Bucket03.inequality_at
   digest: Scoped finite integer inequalities eliminate only their stated outcome variables. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Group08
import D5.S3.Quantum.Entanglement.EJM.Semantic.Cut01137.PreparedEJMCompleteMiniCut01137Tables
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket03
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

def lowerAt (e : Assignment) : ℤ := PreparedEJMCompleteMiniCut01137Tables.normal16279 (e 13) (e 14) (e 18)

set_option trace.profiler true in
theorem receipt : ∀ (x13 x14 x17 x18 : Fin 4),
    (-403379955 : ℤ) + PreparedEJMCompleteMiniCut01137Tables.normal16279 x13 x14 x18 ≤ PreparedEJMCompleteMiniCut01137Tables.normal16269 x13 x14 x17 x18 := by
  decide +kernel

theorem inequality_at (e : Assignment) :
    (-403379955 : ℤ) + lowerAt e ≤ PreparedEJMCompleteMiniCut01137Group08.normalizedAt e := by
  exact receipt (e 13) (e 14) (e 17) (e 18)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Bucket03

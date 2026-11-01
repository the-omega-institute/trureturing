/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor07
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor07
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor07.bound
   digest: An original triangle or singleton factor is bounded on the exact cut prefix. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.EJMAnchor13674Common
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor07
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (trianglePartialAct)
private def state (x13 x16 x17 : Fin 4) : Fin 41294 × LocalSym :=
  (EJMCacheState.triangleStep (EJMCacheState.triangleStep (EJMCacheState.triangleStep (mkTriangle (28979, (6, 13))) (7 : Fin 10) x13) (5 : Fin 10) x16) (8 : Fin 10) x17).state

private def completedPartial (x13 x16 x17 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (prefixPartial 13 17589) (13 : Fin 20) (some x13)) (16 : Fin 20) (some x16)) (17 : Fin 20) (some x17)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x16 x17 : Fin 4),
    EJMTriangleCacheData.assignment (state x13 x16 x17).1 =
      trianglePartialAct (state x13 x16 x17).2
        ((completedPartial x13 x16 x17) ∘ (EJMInflationScore.lhsTriangle 7)) := by
  decide +kernel

def table (x13 x16 x17 : Fin 4) : ℤ :=
  (mkTriangle (state x13 x16 x17)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 16) (e 17)
def score (e : Assignment) : ℤ := EJMInflationScore.triangleBlock F1 7 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 13) (e 16) (e 17)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 13) 16) 17
  have valid := triangle_from_assignment (state (e 13) (e 16) (e 17))
    ((completedPartial (e 13) (e 16) (e 17)) ∘ (EJMInflationScore.lhsTriangle 7))
    (assignment_receipt (e 13) (e 16) (e 17))
  have projected := compatible_project (completedPartial (e 13) (e 16) (e 17)) e
    (EJMInflationScore.lhsTriangle 7) compatible
  exact EJMCacheSoundness.triangle_valid_lower
    (mkTriangle (state (e 13) (e 16) (e 17))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor07

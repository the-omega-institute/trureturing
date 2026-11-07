/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor17
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor17
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor17.bound
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
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor17
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (singletonPartialAct)
private def state (x14 x16 x18 : Fin 4) : Fin 8689 × LocalSym :=
  (EJMCacheState.singletonStep (EJMCacheState.singletonStep (EJMCacheState.singletonStep (mkSingleton (6464, (0, 3))) (4 : Fin 9) x14) (5 : Fin 9) x16) (6 : Fin 9) x18).state

private def completedPartial (x14 x16 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (prefixPartial 13 17589) (14 : Fin 20) (some x14)) (16 : Fin 20) (some x16)) (18 : Fin 20) (some x18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x14 x16 x18 : Fin 4),
    EJMSingletonCacheData.assignment (state x14 x16 x18).1 =
      singletonPartialAct (state x14 x16 x18).2
        ((completedPartial x14 x16 x18) ∘ (EJMInflationScore.lhsSingleton 1)) := by
  decide +kernel

def table (x14 x16 x18 : Fin 4) : ℤ :=
  (mkSingleton (state x14 x16 x18)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 16) (e 18)
def score (e : Assignment) : ℤ := EJMInflationScore.singletonBlock F2 1 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 14) (e 16) (e 18)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 14) 16) 18
  have valid := singleton_from_assignment (state (e 14) (e 16) (e 18))
    ((completedPartial (e 14) (e 16) (e 18)) ∘ (EJMInflationScore.lhsSingleton 1))
    (assignment_receipt (e 14) (e 16) (e 18))
  have projected := compatible_project (completedPartial (e 14) (e 16) (e 18)) e
    (EJMInflationScore.lhsSingleton 1) compatible
  exact EJMCacheSoundness.singleton_valid_lower
    (mkSingleton (state (e 14) (e 16) (e 18))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor17

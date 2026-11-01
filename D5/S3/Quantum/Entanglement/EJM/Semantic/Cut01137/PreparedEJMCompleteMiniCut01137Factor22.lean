/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor22
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor22
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01137/PreparedEJMCompleteMiniCut01137Factor22.bound
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
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor22
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (singletonPartialAct)
private def state (x13 x15 x17 x19 : Fin 4) : Fin 8689 × LocalSym :=
  (EJMCacheState.singletonStep (EJMCacheState.singletonStep (EJMCacheState.singletonStep (EJMCacheState.singletonStep (mkSingleton (7952, (0, 9))) (3 : Fin 9) x13) (4 : Fin 9) x15) (5 : Fin 9) x17) (6 : Fin 9) x19).state

private def completedPartial (x13 x15 x17 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (Function.update (prefixPartial 13 17589) (13 : Fin 20) (some x13)) (15 : Fin 20) (some x15)) (17 : Fin 20) (some x17)) (19 : Fin 20) (some x19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x15 x17 x19 : Fin 4),
    EJMSingletonCacheData.assignment (state x13 x15 x17 x19).1 =
      singletonPartialAct (state x13 x15 x17 x19).2
        ((completedPartial x13 x15 x17 x19) ∘ (EJMInflationScore.lhsSingleton 6)) := by
  decide +kernel

def table (x13 x15 x17 x19 : Fin 4) : ℤ :=
  (mkSingleton (state x13 x15 x17 x19)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 15) (e 17) (e 19)
def score (e : Assignment) : ℤ := EJMInflationScore.singletonBlock F2 6 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 13) (e 15) (e 17) (e 19)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 13) 15) 17) 19
  have valid := singleton_from_assignment (state (e 13) (e 15) (e 17) (e 19))
    ((completedPartial (e 13) (e 15) (e 17) (e 19)) ∘ (EJMInflationScore.lhsSingleton 6))
    (assignment_receipt (e 13) (e 15) (e 17) (e 19))
  have projected := compatible_project (completedPartial (e 13) (e 15) (e 17) (e 19)) e
    (EJMInflationScore.lhsSingleton 6) compatible
  exact EJMCacheSoundness.singleton_valid_lower
    (mkSingleton (state (e 13) (e 15) (e 17) (e 19))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor22

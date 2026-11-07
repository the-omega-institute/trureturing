/- GID: D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor27
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor27
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; premises=D5/S3/Quantum/Entanglement/EJM/Semantic/Cut01088/PreparedEJMCompleteMiniCut01088Factor27.bound
   digest: An original triangle or singleton factor is bounded on the exact cut prefix. -/

/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.Semantic.EJMAnchor13674Common
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor27
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (singletonPartialAct)
private def state (x15 x16 x18 : Fin 4) : Fin 8689 × LocalSym :=
  (EJMCacheState.singletonStep (EJMCacheState.singletonStep (EJMCacheState.singletonStep (mkSingleton (7216, (2, 0))) (0 : Fin 9) x15) (5 : Fin 9) x16) (6 : Fin 9) x18).state

private def completedPartial (x15 x16 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (prefixPartial 13 17540) (15 : Fin 20) (some x15)) (16 : Fin 20) (some x16)) (18 : Fin 20) (some x18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x15 x16 x18 : Fin 4),
    EJMSingletonCacheData.assignment (state x15 x16 x18).1 =
      singletonPartialAct (state x15 x16 x18).2
        ((completedPartial x15 x16 x18) ∘ (EJMInflationScore.lhsSingleton 11)) := by
  decide +kernel

def table (x15 x16 x18 : Fin 4) : ℤ :=
  (mkSingleton (state x15 x16 x18)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 15) (e 16) (e 18)
def score (e : Assignment) : ℤ := EJMInflationScore.singletonBlock F2 11 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 15) (e 16) (e 18)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 15) 16) 18
  have valid := singleton_from_assignment (state (e 15) (e 16) (e 18))
    ((completedPartial (e 15) (e 16) (e 18)) ∘ (EJMInflationScore.lhsSingleton 11))
    (assignment_receipt (e 15) (e 16) (e 18))
  have projected := compatible_project (completedPartial (e 15) (e 16) (e 18)) e
    (EJMInflationScore.lhsSingleton 11) compatible
  exact EJMCacheSoundness.singleton_valid_lower
    (mkSingleton (state (e 15) (e 16) (e 18))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor27

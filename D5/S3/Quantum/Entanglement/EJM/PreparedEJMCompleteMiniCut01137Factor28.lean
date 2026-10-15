/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17589, index=43927; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor28
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (singletonPartialAct)
private def state (x13 x15 x16 : Fin 4) : Fin 8689 × LocalSym :=
  (EJMCacheState.singletonStep (EJMCacheState.singletonStep (EJMCacheState.singletonStep (mkSingleton (7312, (0, 2))) (5 : Fin 9) x13) (6 : Fin 9) x15) (0 : Fin 9) x16).state

private def completedPartial (x13 x15 x16 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (prefixPartial 13 17589) (13 : Fin 20) (some x13)) (15 : Fin 20) (some x15)) (16 : Fin 20) (some x16)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x15 x16 : Fin 4),
    EJMSingletonCacheData.assignment (state x13 x15 x16).1 =
      singletonPartialAct (state x13 x15 x16).2
        ((completedPartial x13 x15 x16) ∘ (EJMInflationScore.lhsSingleton 12)) := by
  decide +kernel

def table (x13 x15 x16 : Fin 4) : ℤ :=
  (mkSingleton (state x13 x15 x16)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 15) (e 16)
def score (e : Assignment) : ℤ := EJMInflationScore.singletonBlock F2 12 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17589) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 13) (e 15) (e 16)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 13) 15) 16
  have valid := singleton_from_assignment (state (e 13) (e 15) (e 16))
    ((completedPartial (e 13) (e 15) (e 16)) ∘ (EJMInflationScore.lhsSingleton 12))
    (assignment_receipt (e 13) (e 15) (e 16))
  have projected := compatible_project (completedPartial (e 13) (e 15) (e 16)) e
    (EJMInflationScore.lhsSingleton 12) compatible
  exact EJMCacheSoundness.singleton_valid_lower
    (mkSingleton (state (e 13) (e 15) (e 16))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01137Factor28

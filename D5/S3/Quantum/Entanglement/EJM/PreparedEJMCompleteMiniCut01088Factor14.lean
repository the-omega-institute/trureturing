/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor14
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (trianglePartialAct)
private def state (x15 x17 x18 : Fin 4) : Fin 41294 × LocalSym :=
  (EJMCacheState.triangleStep (EJMCacheState.triangleStep (EJMCacheState.triangleStep (mkTriangle (34801, (6, 0))) (5 : Fin 10) x15) (0 : Fin 10) x17) (1 : Fin 10) x18).state

private def completedPartial (x15 x17 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (prefixPartial 13 17540) (15 : Fin 20) (some x15)) (17 : Fin 20) (some x17)) (18 : Fin 20) (some x18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x15 x17 x18 : Fin 4),
    EJMTriangleCacheData.assignment (state x15 x17 x18).1 =
      trianglePartialAct (state x15 x17 x18).2
        ((completedPartial x15 x17 x18) ∘ (EJMInflationScore.lhsTriangle 14)) := by
  decide +kernel

def table (x15 x17 x18 : Fin 4) : ℤ :=
  (mkTriangle (state x15 x17 x18)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 15) (e 17) (e 18)
def score (e : Assignment) : ℤ := EJMInflationScore.triangleBlock F1 14 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 15) (e 17) (e 18)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 15) 17) 18
  have valid := triangle_from_assignment (state (e 15) (e 17) (e 18))
    ((completedPartial (e 15) (e 17) (e 18)) ∘ (EJMInflationScore.lhsTriangle 14))
    (assignment_receipt (e 15) (e 17) (e 18))
  have projected := compatible_project (completedPartial (e 15) (e 17) (e 18)) e
    (EJMInflationScore.lhsTriangle 14) compatible
  exact EJMCacheSoundness.triangle_valid_lower
    (mkTriangle (state (e 15) (e 17) (e 18))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor14

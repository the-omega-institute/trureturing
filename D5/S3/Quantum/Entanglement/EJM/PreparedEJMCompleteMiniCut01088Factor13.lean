/- Prepared actual complete-cut source, uncompiled.
Original cut depth=13, code=17540, index=42672; Fin20/Fin4,
all 32 original factors, F1/F2 and scale 6987435 remain unchanged.
Saved producer cells are untrusted until every explicit kernel goal passes. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor13
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Event Partial Compatible)
open EJMOriginalReplayAssembly (prefixPartial)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)
open EJMPartialBoundData (LocalSym scale)
abbrev Assignment := Fin 20 → Fin 4

open TransientEJMAnchor13674Common
open EJMPartialBoundTransport (trianglePartialAct)
private def state (x13 x14 x16 x19 : Fin 4) : Fin 41294 × LocalSym :=
  (EJMCacheState.triangleStep (EJMCacheState.triangleStep (EJMCacheState.triangleStep (EJMCacheState.triangleStep (mkTriangle (39014, (6, 2))) (8 : Fin 10) x13) (5 : Fin 10) x14) (0 : Fin 10) x16) (1 : Fin 10) x19).state

private def completedPartial (x13 x14 x16 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  Function.update (Function.update (Function.update (Function.update (prefixPartial 13 17540) (13 : Fin 20) (some x13)) (14 : Fin 20) (some x14)) (16 : Fin 20) (some x16)) (19 : Fin 20) (some x19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x14 x16 x19 : Fin 4),
    EJMTriangleCacheData.assignment (state x13 x14 x16 x19).1 =
      trianglePartialAct (state x13 x14 x16 x19).2
        ((completedPartial x13 x14 x16 x19) ∘ (EJMInflationScore.lhsTriangle 13)) := by
  decide +kernel

def table (x13 x14 x16 x19 : Fin 4) : ℤ :=
  (mkTriangle (state x13 x14 x16 x19)).row.lower

def lowerAt (e : Assignment) : ℤ := table (e 13) (e 14) (e 16) (e 19)
def score (e : Assignment) : ℤ := EJMInflationScore.triangleBlock F1 13 e

theorem bound (e : Assignment)
    (hp : Compatible (prefixPartial 13 17540) e) : lowerAt e ≤ score e := by
  have compatible : Compatible (completedPartial (e 13) (e 14) (e 16) (e 19)) e := by
    unfold completedPartial
    exact compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ (hp) 13) 14) 16) 19
  have valid := triangle_from_assignment (state (e 13) (e 14) (e 16) (e 19))
    ((completedPartial (e 13) (e 14) (e 16) (e 19)) ∘ (EJMInflationScore.lhsTriangle 13))
    (assignment_receipt (e 13) (e 14) (e 16) (e 19))
  have projected := compatible_project (completedPartial (e 13) (e 14) (e 16) (e 19)) e
    (EJMInflationScore.lhsTriangle 13) compatible
  exact EJMCacheSoundness.triangle_valid_lower
    (mkTriangle (state (e 13) (e 14) (e 16) (e 19))) _ _ valid projected

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteMiniCut01088Factor13

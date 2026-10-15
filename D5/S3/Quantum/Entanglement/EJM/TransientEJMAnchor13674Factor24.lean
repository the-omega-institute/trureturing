/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor24
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x17 x19 : Fin 4) : Fin 8689 × LocalSym :=
  ![![(4, (1, 0)), (31, (0, 0)), (41, (0, 0)), (41, (0, 1))], ![(51, (0, 0)), (58, (0, 0)), (68, (0, 0)), (68, (0, 1))], ![(84, (0, 0)), (94, (0, 0)), (110, (0, 0)), (126, (0, 0))], ![(84, (0, 1)), (94, (0, 1)), (126, (0, 1)), (110, (0, 1))]] x17 x19
def table (x17 x19 : Fin 4) : ℤ :=
  ![![1693600988588145, 1600976283908820, 2405781947974860, 2405781947974860], ![2223855098895885, 2497112013709950, 2034992284263120, 2034992284263120], ![2216980664694705, 2832071682914565, 2280259602747945, 2185883860832490], ![2216980664694705, 2832071682914565, 2185883860832490, 2280259602747945]] x17 x19
private def completedPartial (x17 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (prefixPartial 13 4) (17 : Fin 20) (some x17)) (19 : Fin 20) (some x19))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 17) (e 19)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ hp 17) 19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x17 x19 : Fin 4),
    EJMSingletonCacheData.assignment (state x17 x19).1 =
      singletonPartialAct (state x17 x19).2 ((completedPartial x17 x19) ∘ lhsSingleton 8) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x17 x19 : Fin 4),
    (mkSingleton (state x17 x19)).row.lower = table x17 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 17) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 8 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 17) (e 19)) ((completedPartial (e 17) (e 19)) ∘ lhsSingleton 8)
    (assignment_receipt (e 17) (e 19))
  have compatible := compatible_project (completedPartial (e 17) (e 19)) e (lhsSingleton 8)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 17) (e 19)))
    ((completedPartial (e 17) (e 19)) ∘ lhsSingleton 8) (e ∘ lhsSingleton 8) valid compatible
  change (mkSingleton (state (e 17) (e 19))).row.lower ≤ singletonBlock F2 8 e at lower
  rw [lower_receipt (e 17) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor24

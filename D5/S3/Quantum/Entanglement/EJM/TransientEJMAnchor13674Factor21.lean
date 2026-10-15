/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor21
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x14 x16 x18 : Fin 4) : Fin 8689 × LocalSym :=
  ![![![(0, (0, 0)), (4, (0, 0)), (4, (0, 2)), (4, (0, 3))], ![(4, (6, 0)), (14, (0, 0)), (21, (0, 0)), (21, (0, 1))], ![(4, (6, 2)), (21, (0, 2)), (14, (0, 2)), (21, (0, 4))], ![(4, (6, 3)), (21, (0, 3)), (21, (0, 5)), (14, (0, 3))]], ![![(4, (1, 0)), (31, (0, 0)), (41, (0, 0)), (41, (0, 1))], ![(51, (0, 0)), (58, (0, 0)), (68, (0, 0)), (68, (0, 1))], ![(84, (0, 0)), (94, (0, 0)), (110, (0, 0)), (126, (0, 0))], ![(84, (0, 1)), (94, (0, 1)), (126, (0, 1)), (110, (0, 1))]], ![![(4, (1, 2)), (41, (0, 2)), (31, (0, 2)), (41, (0, 4))], ![(84, (0, 2)), (110, (0, 2)), (94, (0, 2)), (126, (0, 2))], ![(51, (0, 2)), (68, (0, 2)), (58, (0, 2)), (68, (0, 4))], ![(84, (0, 4)), (126, (0, 4)), (94, (0, 4)), (110, (0, 4))]], ![![(4, (1, 3)), (41, (0, 3)), (41, (0, 5)), (31, (0, 3))], ![(84, (0, 3)), (110, (0, 3)), (126, (0, 3)), (94, (0, 3))], ![(84, (0, 5)), (126, (0, 5)), (110, (0, 5)), (94, (0, 5))], ![(51, (0, 3)), (68, (0, 3)), (68, (0, 5)), (58, (0, 3))]]] x14 x16 x18
def table (x14 x16 x18 : Fin 4) : ℤ :=
  ![![![342684662906040, 1693600988588145, 1693600988588145, 1693600988588145], ![1693600988588145, 3044532442067025, 3044532106670145, 3044532106670145], ![1693600988588145, 3044532106670145, 3044532442067025, 3044532106670145], ![1693600988588145, 3044532106670145, 3044532106670145, 3044532442067025]], ![![1693600988588145, 1600976283908820, 2405781947974860, 2405781947974860], ![2223855098895885, 2497112013709950, 2034992284263120, 2034992284263120], ![2216980664694705, 2832071682914565, 2280259602747945, 2185883860832490], ![2216980664694705, 2832071682914565, 2185883860832490, 2280259602747945]], ![![1693600988588145, 2405781947974860, 1600976283908820, 2405781947974860], ![2216980664694705, 2280259602747945, 2832071682914565, 2185883860832490], ![2223855098895885, 2034992284263120, 2497112013709950, 2034992284263120], ![2216980664694705, 2185883860832490, 2832071682914565, 2280259602747945]], ![![1693600988588145, 2405781947974860, 2405781947974860, 1600976283908820], ![2216980664694705, 2280259602747945, 2185883860832490, 2832071682914565], ![2216980664694705, 2185883860832490, 2280259602747945, 2832071682914565], ![2223855098895885, 2034992284263120, 2034992284263120, 2497112013709950]]] x14 x16 x18
private def completedPartial (x14 x16 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (14 : Fin 20) (some x14)) (16 : Fin 20) (some x16)) (18 : Fin 20) (some x18))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 14) (e 16) (e 18)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 14) 16) 18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x14 x16 x18 : Fin 4),
    EJMSingletonCacheData.assignment (state x14 x16 x18).1 =
      singletonPartialAct (state x14 x16 x18).2 ((completedPartial x14 x16 x18) ∘ lhsSingleton 5) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x14 x16 x18 : Fin 4),
    (mkSingleton (state x14 x16 x18)).row.lower = table x14 x16 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 16) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 5 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 14) (e 16) (e 18)) ((completedPartial (e 14) (e 16) (e 18)) ∘ lhsSingleton 5)
    (assignment_receipt (e 14) (e 16) (e 18))
  have compatible := compatible_project (completedPartial (e 14) (e 16) (e 18)) e (lhsSingleton 5)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 14) (e 16) (e 18)))
    ((completedPartial (e 14) (e 16) (e 18)) ∘ lhsSingleton 5) (e ∘ lhsSingleton 5) valid compatible
  change (mkSingleton (state (e 14) (e 16) (e 18))).row.lower ≤ singletonBlock F2 5 e at lower
  rw [lower_receipt (e 14) (e 16) (e 18)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor21

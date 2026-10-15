/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor26
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x14 x17 x19 : Fin 4) : Fin 8689 × LocalSym :=
  ![![![(4, (1, 0)), (31, (0, 0)), (41, (0, 0)), (41, (0, 1))], ![(51, (0, 0)), (58, (0, 0)), (68, (0, 0)), (68, (0, 1))], ![(84, (0, 0)), (94, (0, 0)), (110, (0, 0)), (126, (0, 0))], ![(84, (0, 1)), (94, (0, 1)), (126, (0, 1)), (110, (0, 1))]], ![![(497, (8, 6)), (259, (9, 6)), (540, (8, 6)), (540, (8, 7))], ![(453, (9, 6)), (62, (11, 6)), (524, (8, 6)), (524, (8, 7))], ![(508, (8, 6)), (371, (9, 6)), (556, (8, 6)), (572, (8, 7))], ![(508, (8, 7)), (371, (9, 7)), (572, (8, 6)), (556, (8, 7))]], ![![(953, (1, 8)), (989, (0, 8)), (540, (10, 8)), (1004, (0, 8))], ![(1014, (0, 8)), (1024, (0, 8)), (645, (11, 14)), (1035, (0, 8))], ![(508, (4, 8)), (793, (5, 14)), (154, (4, 8)), (883, (4, 16))], ![(1050, (0, 8)), (1061, (0, 8)), (899, (10, 16)), (1077, (0, 8))]], ![![(953, (1, 9)), (989, (0, 9)), (1004, (0, 9)), (540, (10, 9))], ![(1014, (0, 9)), (1024, (0, 9)), (1035, (0, 9)), (645, (11, 15))], ![(1050, (0, 9)), (1061, (0, 9)), (1077, (0, 9)), (899, (10, 17))], ![(508, (4, 9)), (793, (5, 15)), (883, (4, 17)), (154, (4, 9))]]] x14 x17 x19
def table (x14 x17 x19 : Fin 4) : ℤ :=
  ![![![1693600988588145, 1600976283908820, 2405781947974860, 2405781947974860], ![2223855098895885, 2497112013709950, 2034992284263120, 2034992284263120], ![2216980664694705, 2832071682914565, 2280259602747945, 2185883860832490], ![2216980664694705, 2832071682914565, 2185883860832490, 2280259602747945]], ![![(-594470238080355), (-775232281744830), (-880826071055385), (-880826071055385)], ![(-197936376301755), 330812444858805, (-640828466424510), (-640828466424510)], ![(-864678751614405), (-617554368554760), (-1379582934588495), (-1917671049571095)], ![(-864678751614405), (-617554368554760), (-1917671049571095), (-1379582934588495)]], ![![(-549565382241330), (-412872008069430), (-880826071055385), (-644129819838960)], ![(-1012959368284500), (-1413962239765530), (-256013539331550), (-1138150299469365)], ![(-864678751614405), (-753331256777190), (-1199454204082680), 374378578026180], ![(-487623182428200), (-1461186071557485), (-642591403262445), 298777528935795]], ![![(-549565382241330), (-412872008069430), (-644129819838960), (-880826071055385)], ![(-1012959368284500), (-1413962239765530), (-1138150299469365), (-256013539331550)], ![(-487623182428200), (-1461186071557485), 298777528935795, (-642591403262445)], ![(-864678751614405), (-753331256777190), 374378578026180, (-1199454204082680)]]] x14 x17 x19
private def completedPartial (x14 x17 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (14 : Fin 20) (some x14)) (17 : Fin 20) (some x17)) (19 : Fin 20) (some x19))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 14) (e 17) (e 19)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 14) 17) 19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x14 x17 x19 : Fin 4),
    EJMSingletonCacheData.assignment (state x14 x17 x19).1 =
      singletonPartialAct (state x14 x17 x19).2 ((completedPartial x14 x17 x19) ∘ lhsSingleton 10) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x14 x17 x19 : Fin 4),
    (mkSingleton (state x14 x17 x19)).row.lower = table x14 x17 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 17) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 10 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 14) (e 17) (e 19)) ((completedPartial (e 14) (e 17) (e 19)) ∘ lhsSingleton 10)
    (assignment_receipt (e 14) (e 17) (e 19))
  have compatible := compatible_project (completedPartial (e 14) (e 17) (e 19)) e (lhsSingleton 10)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 14) (e 17) (e 19)))
    ((completedPartial (e 14) (e 17) (e 19)) ∘ lhsSingleton 10) (e ∘ lhsSingleton 10) valid compatible
  change (mkSingleton (state (e 14) (e 17) (e 19))).row.lower ≤ singletonBlock F2 10 e at lower
  rw [lower_receipt (e 14) (e 17) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor26

/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor28
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x13 x15 x16 : Fin 4) : Fin 8689 × LocalSym :=
  ![![![(4, (1, 0)), (497, (8, 6)), (953, (1, 8)), (953, (1, 9))], ![(31, (0, 0)), (259, (9, 6)), (989, (0, 8)), (989, (0, 9))], ![(41, (0, 0)), (540, (8, 6)), (540, (10, 8)), (1004, (0, 9))], ![(41, (0, 1)), (540, (8, 7)), (1004, (0, 8)), (540, (10, 9))]], ![![(51, (0, 0)), (453, (5, 6)), (1014, (0, 8)), (1014, (0, 9))], ![(58, (0, 0)), (62, (11, 6)), (1024, (0, 8)), (1024, (0, 9))], ![(68, (0, 0)), (524, (8, 6)), (645, (11, 14)), (1035, (0, 9))], ![(68, (0, 1)), (524, (8, 7)), (1035, (0, 8)), (645, (11, 15))]], ![![(84, (0, 0)), (508, (8, 6)), (508, (4, 8)), (1050, (0, 9))], ![(94, (0, 0)), (371, (9, 6)), (793, (5, 14)), (1061, (0, 9))], ![(110, (0, 0)), (556, (8, 6)), (154, (4, 8)), (1077, (0, 9))], ![(126, (0, 0)), (572, (8, 7)), (883, (4, 16)), (899, (10, 17))]], ![![(84, (0, 1)), (508, (8, 7)), (1050, (0, 8)), (508, (4, 9))], ![(94, (0, 1)), (371, (9, 7)), (1061, (0, 8)), (793, (5, 15))], ![(126, (0, 1)), (572, (8, 6)), (899, (10, 16)), (883, (4, 17))], ![(110, (0, 1)), (556, (8, 7)), (1077, (0, 8)), (154, (4, 9))]]] x13 x15 x16
def table (x13 x15 x16 : Fin 4) : ℤ :=
  ![![![1693600988588145, (-594470238080355), (-549565382241330), (-549565382241330)], ![1600976283908820, (-775232281744830), (-412872008069430), (-412872008069430)], ![2405781947974860, (-880826071055385), (-880826071055385), (-644129819838960)], ![2405781947974860, (-880826071055385), (-644129819838960), (-880826071055385)]], ![![2223855098895885, (-197936376301755), (-1012959368284500), (-1012959368284500)], ![2497112013709950, 330812444858805, (-1413962239765530), (-1413962239765530)], ![2034992284263120, (-640828466424510), (-256013539331550), (-1138150299469365)], ![2034992284263120, (-640828466424510), (-1138150299469365), (-256013539331550)]], ![![2216980664694705, (-864678751614405), (-864678751614405), (-487623182428200)], ![2832071682914565, (-617554368554760), (-753331256777190), (-1461186071557485)], ![2280259602747945, (-1379582934588495), (-1199454204082680), 298777528935795], ![2185883860832490, (-1917671049571095), 374378578026180, (-642591403262445)]], ![![2216980664694705, (-864678751614405), (-487623182428200), (-864678751614405)], ![2832071682914565, (-617554368554760), (-1461186071557485), (-753331256777190)], ![2185883860832490, (-1917671049571095), (-642591403262445), 374378578026180], ![2280259602747945, (-1379582934588495), 298777528935795, (-1199454204082680)]]] x13 x15 x16
private def completedPartial (x13 x15 x16 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (13 : Fin 20) (some x13)) (15 : Fin 20) (some x15)) (16 : Fin 20) (some x16))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 13) (e 15) (e 16)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 13) 15) 16)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x15 x16 : Fin 4),
    EJMSingletonCacheData.assignment (state x13 x15 x16).1 =
      singletonPartialAct (state x13 x15 x16).2 ((completedPartial x13 x15 x16) ∘ lhsSingleton 12) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x13 x15 x16 : Fin 4),
    (mkSingleton (state x13 x15 x16)).row.lower = table x13 x15 x16 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 15) (e 16)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 12 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 13) (e 15) (e 16)) ((completedPartial (e 13) (e 15) (e 16)) ∘ lhsSingleton 12)
    (assignment_receipt (e 13) (e 15) (e 16))
  have compatible := compatible_project (completedPartial (e 13) (e 15) (e 16)) e (lhsSingleton 12)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 13) (e 15) (e 16)))
    ((completedPartial (e 13) (e 15) (e 16)) ∘ lhsSingleton 12) (e ∘ lhsSingleton 12) valid compatible
  change (mkSingleton (state (e 13) (e 15) (e 16))).row.lower ≤ singletonBlock F2 12 e at lower
  rw [lower_receipt (e 13) (e 15) (e 16)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor28

/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor23
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x14 x16 x18 : Fin 4) : Fin 8689 × LocalSym :=
  ![![![(944, (0, 6)), (497, (10, 6)), (953, (0, 6)), (953, (0, 7))], ![(497, (4, 6)), (145, (4, 6)), (867, (4, 12)), (867, (4, 13))], ![(953, (6, 6)), (867, (10, 12)), (968, (0, 6)), (978, (0, 6))], ![(953, (6, 7)), (867, (10, 13)), (978, (0, 7)), (968, (0, 7))]], ![![(497, (8, 6)), (259, (9, 6)), (540, (8, 6)), (540, (8, 7))], ![(453, (9, 6)), (62, (11, 6)), (524, (8, 6)), (524, (8, 7))], ![(508, (8, 6)), (371, (9, 6)), (556, (8, 6)), (572, (8, 7))], ![(508, (8, 7)), (371, (9, 7)), (572, (8, 6)), (556, (8, 7))]], ![![(953, (1, 6)), (540, (10, 6)), (989, (0, 6)), (1004, (0, 6))], ![(508, (4, 6)), (154, (4, 6)), (793, (5, 12)), (883, (4, 13))], ![(1014, (0, 6)), (645, (11, 12)), (1024, (0, 6)), (1035, (0, 6))], ![(1050, (0, 6)), (899, (10, 13)), (1061, (0, 6)), (1077, (0, 6))]], ![![(953, (1, 7)), (540, (10, 7)), (1004, (0, 7)), (989, (0, 7))], ![(508, (4, 7)), (154, (4, 7)), (883, (4, 12)), (793, (5, 13))], ![(1050, (0, 7)), (899, (10, 12)), (1077, (0, 7)), (1061, (0, 7))], ![(1014, (0, 7)), (645, (11, 13)), (1035, (0, 7)), (1024, (0, 7))]]] x14 x16 x18
def table (x14 x16 x18 : Fin 4) : ℤ :=
  ![![![(-114228225626970), (-594470238080355), (-549565382241330), (-549565382241330)], ![(-594470238080355), (-749342940678150), (-948365394964260), (-948365394964260)], ![(-549565382241330), (-948365394964260), (-1147594754188155), (-1147801330716495)], ![(-549565382241330), (-948365394964260), (-1147801330716495), (-1147594754188155)]], ![![(-594470238080355), (-775232281744830), (-880826071055385), (-880826071055385)], ![(-197936376301755), 330812444858805, (-640828466424510), (-640828466424510)], ![(-864678751614405), (-617554368554760), (-1379582934588495), (-1917671049571095)], ![(-864678751614405), (-617554368554760), (-1917671049571095), (-1379582934588495)]], ![![(-549565382241330), (-880826071055385), (-412872008069430), (-644129819838960)], ![(-864678751614405), (-1199454204082680), (-753331256777190), 374378578026180], ![(-1012959368284500), (-256013539331550), (-1413962239765530), (-1138150299469365)], ![(-487623182428200), (-642591403262445), (-1461186071557485), 298777528935795]], ![![(-549565382241330), (-880826071055385), (-644129819838960), (-412872008069430)], ![(-864678751614405), (-1199454204082680), 374378578026180, (-753331256777190)], ![(-487623182428200), (-642591403262445), 298777528935795, (-1461186071557485)], ![(-1012959368284500), (-256013539331550), (-1138150299469365), (-1413962239765530)]]] x14 x16 x18
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
      singletonPartialAct (state x14 x16 x18).2 ((completedPartial x14 x16 x18) ∘ lhsSingleton 7) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x14 x16 x18 : Fin 4),
    (mkSingleton (state x14 x16 x18)).row.lower = table x14 x16 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 16) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 7 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 14) (e 16) (e 18)) ((completedPartial (e 14) (e 16) (e 18)) ∘ lhsSingleton 7)
    (assignment_receipt (e 14) (e 16) (e 18))
  have compatible := compatible_project (completedPartial (e 14) (e 16) (e 18)) e (lhsSingleton 7)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 14) (e 16) (e 18)))
    ((completedPartial (e 14) (e 16) (e 18)) ∘ lhsSingleton 7) (e ∘ lhsSingleton 7) valid compatible
  change (mkSingleton (state (e 14) (e 16) (e 18))).row.lower ≤ singletonBlock F2 7 e at lower
  rw [lower_receipt (e 14) (e 16) (e 18)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor23

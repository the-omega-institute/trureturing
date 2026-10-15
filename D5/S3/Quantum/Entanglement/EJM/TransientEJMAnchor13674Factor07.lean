/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor07
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x13 x16 x17 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(1236, (0, 0)), (1239, (0, 0)), (1242, (0, 0)), (1242, (0, 1))], ![(1282, (0, 0)), (1285, (0, 0)), (1288, (0, 0)), (1288, (0, 1))], ![(1370, (0, 0)), (1374, (0, 0)), (1378, (0, 0)), (1382, (0, 0))], ![(1370, (0, 1)), (1374, (0, 1)), (1382, (0, 1)), (1378, (0, 1))]], ![![(1239, (1, 0)), (1246, (0, 0)), (1249, (0, 0)), (1249, (0, 1))], ![(1292, (0, 0)), (1295, (0, 0)), (1298, (0, 0)), (1298, (0, 1))], ![(1386, (0, 0)), (1390, (0, 0)), (1394, (0, 0)), (1398, (0, 0))], ![(1386, (0, 1)), (1390, (0, 1)), (1398, (0, 1)), (1394, (0, 1))]], ![![(1242, (1, 0)), (1249, (1, 0)), (1253, (0, 0)), (1257, (0, 0))], ![(1302, (0, 0)), (1306, (0, 0)), (1310, (0, 0)), (1314, (0, 0))], ![(1402, (0, 0)), (1406, (0, 0)), (1410, (0, 0)), (1414, (0, 0))], ![(1418, (0, 1)), (1422, (0, 1)), (1430, (0, 1)), (1426, (0, 1))]], ![![(1242, (1, 1)), (1249, (1, 1)), (1257, (0, 1)), (1253, (0, 1))], ![(1302, (0, 1)), (1306, (0, 1)), (1314, (0, 1)), (1310, (0, 1))], ![(1418, (0, 0)), (1422, (0, 0)), (1426, (0, 0)), (1430, (0, 0))], ![(1402, (0, 1)), (1406, (0, 1)), (1414, (0, 1)), (1410, (0, 1))]]] x13 x16 x17
def table (x13 x16 x17 : Fin 4) : ℤ :=
  ![![![6370619825206455, 3681851609011485, 3688719419124285, 3688719419124285], ![11096759638118700, 5068457838116400, 2335601052213975, 2335601052213975], ![5798533471801980, 3988689759114060, 3381579300030750, 4123691272636845], ![5798533471801980, 3988689759114060, 4123691272636845, 3381579300030750]], ![![3681851609011485, 2213127248015775, 3089281575929640, 3089281575929640], ![7557446336757135, 598495608547200, 1328249463863595, 1328249463863595], ![5876128650992145, 3704512063352100, 5603478776581140, 4166368513235565], ![5876128650992145, 3704512063352100, 4166368513235565, 5603478776581140]], ![![3688719419124285, 3089281575929640, 3769144851873765, 4333892560832835], ![8338750804328490, 1317444485675955, 3985822786583820, 1870601276746020], ![5419639815914415, 3031001714397930, 3351520905871320, 3842991356035650], ![3801849017333640, 3718660508224935, 3919853001286950, 3887528099824005]], ![![3688719419124285, 3089281575929640, 4333892560832835, 3769144851873765], ![8338750804328490, 1317444485675955, 1870601276746020, 3985822786583820], ![3801849017333640, 3718660508224935, 3887528099824005, 3919853001286950], ![5419639815914415, 3031001714397930, 3842991356035650, 3351520905871320]]] x13 x16 x17
private def completedPartial (x13 x16 x17 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (13 : Fin 20) (some x13)) (16 : Fin 20) (some x16)) (17 : Fin 20) (some x17))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 13) (e 16) (e 17)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 13) 16) 17)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x16 x17 : Fin 4),
    EJMTriangleCacheData.assignment (state x13 x16 x17).1 =
      trianglePartialAct (state x13 x16 x17).2 ((completedPartial x13 x16 x17) ∘ lhsTriangle 7) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x13 x16 x17 : Fin 4),
    (mkTriangle (state x13 x16 x17)).row.lower = table x13 x16 x17 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 16) (e 17)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 7 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 13) (e 16) (e 17)) ((completedPartial (e 13) (e 16) (e 17)) ∘ lhsTriangle 7)
    (assignment_receipt (e 13) (e 16) (e 17))
  have compatible := compatible_project (completedPartial (e 13) (e 16) (e 17)) e (lhsTriangle 7)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 13) (e 16) (e 17)))
    ((completedPartial (e 13) (e 16) (e 17)) ∘ lhsTriangle 7) (e ∘ lhsTriangle 7) valid compatible
  change (mkTriangle (state (e 13) (e 16) (e 17))).row.lower ≤ triangleBlock F1 7 e at lower
  rw [lower_receipt (e 13) (e 16) (e 17)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor07

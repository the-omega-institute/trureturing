/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor08
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x13 x18 x19 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(2, (1, 0)), (5, (0, 0)), (8, (0, 0)), (8, (0, 1))], ![(26, (0, 0)), (29, (0, 0)), (32, (0, 0)), (32, (0, 1))], ![(36, (0, 2)), (43, (0, 2)), (39, (0, 2)), (47, (0, 2))], ![(36, (0, 3)), (43, (0, 3)), (47, (0, 3)), (39, (0, 3))]], ![![(1239, (1, 0)), (1246, (0, 0)), (1249, (0, 0)), (1249, (0, 1))], ![(1292, (0, 0)), (1295, (0, 0)), (1298, (0, 0)), (1298, (0, 1))], ![(1386, (0, 0)), (1390, (0, 0)), (1394, (0, 0)), (1398, (0, 0))], ![(1386, (0, 1)), (1390, (0, 1)), (1398, (0, 1)), (1394, (0, 1))]], ![![(1242, (1, 2)), (1253, (0, 2)), (1249, (1, 2)), (1257, (0, 2))], ![(1402, (0, 2)), (1410, (0, 2)), (1406, (0, 2)), (1414, (0, 2))], ![(1302, (0, 2)), (1310, (0, 2)), (1306, (0, 2)), (1314, (0, 2))], ![(1418, (0, 4)), (1430, (0, 4)), (1422, (0, 4)), (1426, (0, 4))]], ![![(1242, (1, 3)), (1253, (0, 3)), (1257, (0, 3)), (1249, (1, 3))], ![(1402, (0, 3)), (1410, (0, 3)), (1414, (0, 3)), (1406, (0, 3))], ![(1418, (0, 5)), (1430, (0, 5)), (1426, (0, 5)), (1422, (0, 5))], ![(1302, (0, 3)), (1310, (0, 3)), (1314, (0, 3)), (1306, (0, 3))]]] x13 x18 x19
def table (x13 x18 x19 : Fin 4) : ℤ :=
  ![![![(-3842827060476495), (-5890623365193840), (-4072016675335245), (-4072016675335245)], ![(-4039106876650755), (-4908738021733455), (-5580512894469240), (-5580512894469240)], ![(-4456228796410755), (-6261360113060325), (-5563169626615965), (-5776976536083480)], ![(-4456228796410755), (-6261360113060325), (-5776976536083480), (-5563169626615965)]], ![![3681851609011485, 2213127248015775, 3089281575929640, 3089281575929640], ![7557446336757135, 598495608547200, 1328249463863595, 1328249463863595], ![5876128650992145, 3704512063352100, 5603478776581140, 4166368513235565], ![5876128650992145, 3704512063352100, 4166368513235565, 5603478776581140]], ![![3688719419124285, 3769144851873765, 3089281575929640, 4333892560832835], ![5419639815914415, 3351520905871320, 3031001714397930, 3842991356035650], ![8338750804328490, 3985822786583820, 1317444485675955, 1870601276746020], ![3801849017333640, 3919853001286950, 3718660508224935, 3887528099824005]], ![![3688719419124285, 3769144851873765, 4333892560832835, 3089281575929640], ![5419639815914415, 3351520905871320, 3842991356035650, 3031001714397930], ![3801849017333640, 3919853001286950, 3887528099824005, 3718660508224935], ![8338750804328490, 3985822786583820, 1870601276746020, 1317444485675955]]] x13 x18 x19
private def completedPartial (x13 x18 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (13 : Fin 20) (some x13)) (18 : Fin 20) (some x18)) (19 : Fin 20) (some x19))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 13) (e 18) (e 19)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 13) 18) 19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x18 x19 : Fin 4),
    EJMTriangleCacheData.assignment (state x13 x18 x19).1 =
      trianglePartialAct (state x13 x18 x19).2 ((completedPartial x13 x18 x19) ∘ lhsTriangle 8) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x13 x18 x19 : Fin 4),
    (mkTriangle (state x13 x18 x19)).row.lower = table x13 x18 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 18) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 8 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 13) (e 18) (e 19)) ((completedPartial (e 13) (e 18) (e 19)) ∘ lhsTriangle 8)
    (assignment_receipt (e 13) (e 18) (e 19))
  have compatible := compatible_project (completedPartial (e 13) (e 18) (e 19)) e (lhsTriangle 8)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 13) (e 18) (e 19)))
    ((completedPartial (e 13) (e 18) (e 19)) ∘ lhsTriangle 8) (e ∘ lhsTriangle 8) valid compatible
  change (mkTriangle (state (e 13) (e 18) (e 19))).row.lower ≤ triangleBlock F1 8 e at lower
  rw [lower_receipt (e 13) (e 18) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor08

/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor14
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x15 x17 x18 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(2, (7, 0)), (1282, (1, 0)), (1370, (1, 2)), (1370, (1, 3))], ![(1239, (7, 0)), (631, (2, 6)), (3983, (2, 12)), (3983, (2, 13))], ![(1242, (7, 2)), (4422, (2, 14)), (1044, (7, 8)), (4547, (7, 17))], ![(1242, (7, 3)), (4422, (2, 15)), (4547, (7, 16)), (1044, (7, 9))]], ![![(5, (6, 0)), (1530, (0, 0)), (1874, (0, 2)), (1874, (0, 3))], ![(1246, (6, 0)), (415, (3, 6)), (3253, (3, 12)), (3253, (3, 13))], ![(1253, (6, 2)), (4314, (3, 14)), (1048, (6, 8)), (4551, (6, 17))], ![(1253, (6, 3)), (4314, (3, 15)), (4551, (6, 16)), (1048, (6, 9))]], ![![(8, (6, 0)), (1618, (0, 0)), (1618, (1, 2)), (2034, (0, 3))], ![(1249, (6, 0)), (718, (2, 6)), (3673, (3, 12)), (4092, (2, 13))], ![(1249, (7, 2)), (3673, (5, 14)), (718, (4, 8)), (4092, (4, 16))], ![(1257, (6, 3)), (4467, (2, 15)), (4467, (4, 17)), (1052, (6, 9))]], ![![(8, (6, 1)), (1618, (0, 1)), (2034, (0, 2)), (1618, (1, 3))], ![(1249, (6, 1)), (718, (2, 7)), (4092, (2, 12)), (3673, (3, 13))], ![(1257, (6, 2)), (4467, (2, 14)), (1052, (6, 8)), (4467, (4, 16))], ![(1249, (7, 3)), (3673, (5, 15)), (4092, (4, 17)), (718, (4, 9))]]] x15 x17 x18
def table (x15 x17 x18 : Fin 4) : ℤ :=
  ![![![(-3842827060476495), 11096759638118700, 5798533471801980, 5798533471801980], ![3681851609011485, 6805683703237965, 3990933291731295, 3990933291731295], ![3688719419124285, 4954118393486535, 4033680001408785, 3707204259170685], ![3688719419124285, 4954118393486535, 3707204259170685, 4033680001408785]], ![![(-5890623365193840), 11244498574852725, 4295547446084895, 4295547446084895], ![2213127248015775, 439693612713810, 1689813414509220, 1689813414509220], ![3769144851873765, 714690049471125, 6919552949391810, 1585698452929500], ![3769144851873765, 714690049471125, 1585698452929500, 6919552949391810]], ![![(-4072016675335245), 9993397513585395, 9993397513585395, 5101857176496990], ![3089281575929640, 8889085076929785, 4122695199802725, 2829091262389665], ![3089281575929640, 4122695199802725, 8889085076929785, 2829091262389665], ![4333892560832835, 4400735475045000, 4400735475045000, 3923441391543765]], ![![(-4072016675335245), 9993397513585395, 5101857176496990, 9993397513585395], ![3089281575929640, 8889085076929785, 2829091262389665, 4122695199802725], ![4333892560832835, 4400735475045000, 3923441391543765, 4400735475045000], ![3089281575929640, 4122695199802725, 2829091262389665, 8889085076929785]]] x15 x17 x18
private def completedPartial (x15 x17 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (15 : Fin 20) (some x15)) (17 : Fin 20) (some x17)) (18 : Fin 20) (some x18))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 15) (e 17) (e 18)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 15) 17) 18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x15 x17 x18 : Fin 4),
    EJMTriangleCacheData.assignment (state x15 x17 x18).1 =
      trianglePartialAct (state x15 x17 x18).2 ((completedPartial x15 x17 x18) ∘ lhsTriangle 14) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x15 x17 x18 : Fin 4),
    (mkTriangle (state x15 x17 x18)).row.lower = table x15 x17 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 17) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 14 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 15) (e 17) (e 18)) ((completedPartial (e 15) (e 17) (e 18)) ∘ lhsTriangle 14)
    (assignment_receipt (e 15) (e 17) (e 18))
  have compatible := compatible_project (completedPartial (e 15) (e 17) (e 18)) e (lhsTriangle 14)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 15) (e 17) (e 18)))
    ((completedPartial (e 15) (e 17) (e 18)) ∘ lhsTriangle 14) (e ∘ lhsTriangle 14) valid compatible
  change (mkTriangle (state (e 15) (e 17) (e 18))).row.lower ≤ triangleBlock F1 14 e at lower
  rw [lower_receipt (e 15) (e 17) (e 18)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor14

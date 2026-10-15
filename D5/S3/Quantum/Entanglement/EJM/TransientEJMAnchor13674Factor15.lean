/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor15
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x13 x18 x19 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(0, (0, 0)), (1236, (0, 0)), (1236, (0, 2)), (1236, (0, 3))], ![(1236, (6, 0)), (1041, (0, 6)), (4543, (0, 12)), (4543, (0, 13))], ![(1236, (6, 2)), (4543, (0, 14)), (1041, (0, 8)), (4543, (0, 16))], ![(1236, (6, 3)), (4543, (0, 15)), (4543, (0, 17)), (1041, (0, 9))]], ![![(2, (0, 0)), (1239, (0, 0)), (1242, (0, 2)), (1242, (0, 3))], ![(1282, (6, 0)), (631, (10, 6)), (4422, (10, 14)), (4422, (10, 15))], ![(1370, (6, 2)), (3983, (10, 12)), (1044, (0, 8)), (4547, (0, 16))], ![(1370, (6, 3)), (3983, (10, 13)), (4547, (0, 17)), (1044, (0, 9))]], ![![(2, (0, 2)), (1242, (0, 0)), (1239, (0, 2)), (1242, (0, 5))], ![(1370, (6, 0)), (1044, (0, 6)), (3983, (10, 14)), (4547, (0, 13))], ![(1282, (6, 2)), (4422, (10, 12)), (631, (10, 8)), (4422, (10, 17))], ![(1370, (6, 5)), (4547, (0, 15)), (3983, (10, 16)), (1044, (0, 11))]], ![![(2, (0, 3)), (1242, (0, 1)), (1242, (0, 4)), (1239, (0, 3))], ![(1370, (6, 1)), (1044, (0, 7)), (4547, (0, 12)), (3983, (10, 15))], ![(1370, (6, 4)), (4547, (0, 14)), (1044, (0, 10)), (3983, (10, 17))], ![(1282, (6, 3)), (4422, (10, 13)), (4422, (10, 16)), (631, (10, 9))]]] x13 x18 x19
def table (x13 x18 x19 : Fin 4) : ℤ :=
  ![![![(-333398033381595), 6370619825206455, 6370619825206455, 6370619825206455], ![6370619825206455, 11289968965730910, 10510869690720945, 10510869690720945], ![6370619825206455, 10510869690720945, 11289968965730910, 10510869690720945], ![6370619825206455, 10510869690720945, 10510869690720945, 11289968965730910]], ![![(-3842827060476495), 3681851609011485, 3688719419124285, 3688719419124285], ![11096759638118700, 6805683703237965, 4954118393486535, 4954118393486535], ![5798533471801980, 3990933291731295, 4033680001408785, 3707204259170685], ![5798533471801980, 3990933291731295, 3707204259170685, 4033680001408785]], ![![(-3842827060476495), 3688719419124285, 3681851609011485, 3688719419124285], ![5798533471801980, 4033680001408785, 3990933291731295, 3707204259170685], ![11096759638118700, 4954118393486535, 6805683703237965, 4954118393486535], ![5798533471801980, 3707204259170685, 3990933291731295, 4033680001408785]], ![![(-3842827060476495), 3688719419124285, 3688719419124285, 3681851609011485], ![5798533471801980, 4033680001408785, 3707204259170685, 3990933291731295], ![5798533471801980, 3707204259170685, 4033680001408785, 3990933291731295], ![11096759638118700, 4954118393486535, 4954118393486535, 6805683703237965]]] x13 x18 x19
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
      trianglePartialAct (state x13 x18 x19).2 ((completedPartial x13 x18 x19) ∘ lhsTriangle 15) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x13 x18 x19 : Fin 4),
    (mkTriangle (state x13 x18 x19)).row.lower = table x13 x18 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 18) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 15 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 13) (e 18) (e 19)) ((completedPartial (e 13) (e 18) (e 19)) ∘ lhsTriangle 15)
    (assignment_receipt (e 13) (e 18) (e 19))
  have compatible := compatible_project (completedPartial (e 13) (e 18) (e 19)) e (lhsTriangle 15)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 13) (e 18) (e 19)))
    ((completedPartial (e 13) (e 18) (e 19)) ∘ lhsTriangle 15) (e ∘ lhsTriangle 15) valid compatible
  change (mkTriangle (state (e 13) (e 18) (e 19))).row.lower ≤ triangleBlock F1 15 e at lower
  rw [lower_receipt (e 13) (e 18) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor15

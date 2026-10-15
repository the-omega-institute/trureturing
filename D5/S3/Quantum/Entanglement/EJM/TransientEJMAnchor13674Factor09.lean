/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor09
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x15 x17 x18 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(0, (6, 0)), (2, (6, 0)), (2, (6, 2)), (2, (6, 3))], ![(2, (0, 0)), (20, (6, 0)), (23, (6, 0)), (23, (6, 1))], ![(2, (0, 2)), (23, (6, 2)), (20, (6, 2)), (23, (6, 4))], ![(2, (0, 3)), (23, (6, 3)), (23, (6, 5)), (20, (6, 3))]], ![![(1236, (0, 0)), (1282, (0, 0)), (1370, (0, 0)), (1370, (0, 1))], ![(1239, (0, 0)), (1285, (0, 0)), (1374, (0, 0)), (1374, (0, 1))], ![(1242, (0, 0)), (1288, (0, 0)), (1378, (0, 0)), (1382, (0, 1))], ![(1242, (0, 1)), (1288, (0, 1)), (1382, (0, 0)), (1378, (0, 1))]], ![![(1236, (0, 2)), (1370, (0, 2)), (1282, (0, 2)), (1370, (0, 4))], ![(1242, (0, 2)), (1378, (0, 2)), (1288, (0, 2)), (1382, (0, 4))], ![(1239, (0, 2)), (1374, (0, 2)), (1285, (0, 2)), (1374, (0, 4))], ![(1242, (0, 4)), (1382, (0, 2)), (1288, (0, 4)), (1378, (0, 4))]], ![![(1236, (0, 3)), (1370, (0, 3)), (1370, (0, 5)), (1282, (0, 3))], ![(1242, (0, 3)), (1378, (0, 3)), (1382, (0, 5)), (1288, (0, 3))], ![(1242, (0, 5)), (1382, (0, 3)), (1378, (0, 5)), (1288, (0, 5))], ![(1239, (0, 3)), (1374, (0, 3)), (1374, (0, 5)), (1285, (0, 3))]]] x15 x17 x18
def table (x15 x17 x18 : Fin 4) : ℤ :=
  ![![![(-333398033381595), (-3842827060476495), (-3842827060476495), (-3842827060476495)], ![(-3842827060476495), (-6757394161834680), (-6497698621579620), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6757394161834680), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6497698621579620), (-6757394161834680)]], ![![6370619825206455, 11096759638118700, 5798533471801980, 5798533471801980], ![3681851609011485, 5068457838116400, 3988689759114060, 3988689759114060], ![3688719419124285, 2335601052213975, 3381579300030750, 4123691272636845], ![3688719419124285, 2335601052213975, 4123691272636845, 3381579300030750]], ![![6370619825206455, 5798533471801980, 11096759638118700, 5798533471801980], ![3688719419124285, 3381579300030750, 2335601052213975, 4123691272636845], ![3681851609011485, 3988689759114060, 5068457838116400, 3988689759114060], ![3688719419124285, 4123691272636845, 2335601052213975, 3381579300030750]], ![![6370619825206455, 5798533471801980, 5798533471801980, 11096759638118700], ![3688719419124285, 3381579300030750, 4123691272636845, 2335601052213975], ![3688719419124285, 4123691272636845, 3381579300030750, 2335601052213975], ![3681851609011485, 3988689759114060, 3988689759114060, 5068457838116400]]] x15 x17 x18
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
      trianglePartialAct (state x15 x17 x18).2 ((completedPartial x15 x17 x18) ∘ lhsTriangle 9) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x15 x17 x18 : Fin 4),
    (mkTriangle (state x15 x17 x18)).row.lower = table x15 x17 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 17) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 9 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 15) (e 17) (e 18)) ((completedPartial (e 15) (e 17) (e 18)) ∘ lhsTriangle 9)
    (assignment_receipt (e 15) (e 17) (e 18))
  have compatible := compatible_project (completedPartial (e 15) (e 17) (e 18)) e (lhsTriangle 9)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 15) (e 17) (e 18)))
    ((completedPartial (e 15) (e 17) (e 18)) ∘ lhsTriangle 9) (e ∘ lhsTriangle 9) valid compatible
  change (mkTriangle (state (e 15) (e 17) (e 18))).row.lower ≤ triangleBlock F1 9 e at lower
  rw [lower_receipt (e 15) (e 17) (e 18)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor09

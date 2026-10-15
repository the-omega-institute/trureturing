/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor06
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x15 x16 x19 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(0, (6, 0)), (2, (6, 0)), (2, (6, 2)), (2, (6, 3))], ![(2, (0, 0)), (20, (6, 0)), (23, (6, 0)), (23, (6, 1))], ![(2, (0, 2)), (23, (6, 2)), (20, (6, 2)), (23, (6, 4))], ![(2, (0, 3)), (23, (6, 3)), (23, (6, 5)), (20, (6, 3))]], ![![(2, (7, 0)), (5, (6, 0)), (8, (6, 0)), (8, (6, 1))], ![(26, (6, 0)), (29, (6, 0)), (32, (6, 0)), (32, (6, 1))], ![(36, (6, 2)), (43, (6, 2)), (39, (6, 2)), (47, (6, 2))], ![(36, (6, 3)), (43, (6, 3)), (47, (6, 3)), (39, (6, 3))]], ![![(2, (7, 2)), (8, (6, 2)), (5, (6, 2)), (8, (6, 4))], ![(36, (6, 0)), (39, (6, 0)), (43, (6, 0)), (47, (6, 0))], ![(26, (6, 2)), (32, (6, 2)), (29, (6, 2)), (32, (6, 4))], ![(36, (6, 5)), (47, (6, 5)), (43, (6, 5)), (39, (6, 5))]], ![![(2, (7, 3)), (8, (6, 3)), (8, (6, 5)), (5, (6, 3))], ![(36, (6, 1)), (39, (6, 1)), (47, (6, 1)), (43, (6, 1))], ![(36, (6, 4)), (47, (6, 4)), (39, (6, 4)), (43, (6, 4))], ![(26, (6, 3)), (32, (6, 3)), (32, (6, 5)), (29, (6, 3))]]] x15 x16 x19
def table (x15 x16 x19 : Fin 4) : ℤ :=
  ![![![(-333398033381595), (-3842827060476495), (-3842827060476495), (-3842827060476495)], ![(-3842827060476495), (-6757394161834680), (-6497698621579620), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6757394161834680), (-6497698621579620)], ![(-3842827060476495), (-6497698621579620), (-6497698621579620), (-6757394161834680)]], ![![(-3842827060476495), (-5890623365193840), (-4072016675335245), (-4072016675335245)], ![(-4039106876650755), (-4908738021733455), (-5580512894469240), (-5580512894469240)], ![(-4456228796410755), (-6261360113060325), (-5563169626615965), (-5776976536083480)], ![(-4456228796410755), (-6261360113060325), (-5776976536083480), (-5563169626615965)]], ![![(-3842827060476495), (-4072016675335245), (-5890623365193840), (-4072016675335245)], ![(-4456228796410755), (-5563169626615965), (-6261360113060325), (-5776976536083480)], ![(-4039106876650755), (-5580512894469240), (-4908738021733455), (-5580512894469240)], ![(-4456228796410755), (-5776976536083480), (-6261360113060325), (-5563169626615965)]], ![![(-3842827060476495), (-4072016675335245), (-4072016675335245), (-5890623365193840)], ![(-4456228796410755), (-5563169626615965), (-5776976536083480), (-6261360113060325)], ![(-4456228796410755), (-5776976536083480), (-5563169626615965), (-6261360113060325)], ![(-4039106876650755), (-5580512894469240), (-5580512894469240), (-4908738021733455)]]] x15 x16 x19
private def completedPartial (x15 x16 x19 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (15 : Fin 20) (some x15)) (16 : Fin 20) (some x16)) (19 : Fin 20) (some x19))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 15) (e 16) (e 19)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 15) 16) 19)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x15 x16 x19 : Fin 4),
    EJMTriangleCacheData.assignment (state x15 x16 x19).1 =
      trianglePartialAct (state x15 x16 x19).2 ((completedPartial x15 x16 x19) ∘ lhsTriangle 6) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x15 x16 x19 : Fin 4),
    (mkTriangle (state x15 x16 x19)).row.lower = table x15 x16 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 16) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 6 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 15) (e 16) (e 19)) ((completedPartial (e 15) (e 16) (e 19)) ∘ lhsTriangle 6)
    (assignment_receipt (e 15) (e 16) (e 19))
  have compatible := compatible_project (completedPartial (e 15) (e 16) (e 19)) e (lhsTriangle 6)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 15) (e 16) (e 19)))
    ((completedPartial (e 15) (e 16) (e 19)) ∘ lhsTriangle 6) (e ∘ lhsTriangle 6) valid compatible
  change (mkTriangle (state (e 15) (e 16) (e 19))).row.lower ≤ triangleBlock F1 6 e at lower
  rw [lower_receipt (e 15) (e 16) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor06

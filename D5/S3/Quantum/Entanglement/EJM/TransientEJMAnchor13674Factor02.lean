/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor02
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (trianglePartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (triangle_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x15 x16 x19 : Fin 4) : Fin 41294 × LocalSym :=
  ![![![(2, (9, 0)), (5, (8, 0)), (8, (8, 0)), (8, (8, 1))], ![(26, (8, 0)), (29, (8, 0)), (32, (8, 0)), (32, (8, 1))], ![(36, (8, 2)), (43, (8, 2)), (39, (8, 2)), (47, (8, 2))], ![(36, (8, 3)), (43, (8, 3)), (47, (8, 3)), (39, (8, 3))]], ![![(5, (10, 0)), (11, (6, 0)), (14, (6, 0)), (14, (6, 1))], ![(51, (6, 0)), (54, (6, 0)), (57, (6, 0)), (57, (6, 1))], ![(77, (6, 2)), (85, (6, 2)), (81, (6, 2)), (89, (6, 2))], ![(77, (6, 3)), (85, (6, 3)), (89, (6, 3)), (81, (6, 3))]], ![![(8, (10, 0)), (14, (7, 0)), (14, (9, 2)), (18, (6, 0))], ![(61, (6, 0)), (65, (6, 0)), (69, (6, 0)), (73, (6, 0))], ![(61, (8, 2)), (69, (8, 2)), (65, (8, 2)), (73, (8, 2))], ![(93, (6, 3)), (99, (6, 3)), (99, (8, 5)), (96, (6, 3))]], ![![(8, (10, 1)), (14, (7, 1)), (18, (6, 1)), (14, (9, 3))], ![(61, (6, 1)), (65, (6, 1)), (73, (6, 1)), (69, (6, 1))], ![(93, (6, 2)), (99, (6, 2)), (96, (6, 2)), (99, (8, 4))], ![(61, (8, 3)), (69, (8, 3)), (73, (8, 3)), (65, (8, 3))]]] x15 x16 x19
def table (x15 x16 x19 : Fin 4) : ℤ :=
  ![![![(-3842827060476495), (-5890623365193840), (-4072016675335245), (-4072016675335245)], ![(-4039106876650755), (-4908738021733455), (-5580512894469240), (-5580512894469240)], ![(-4456228796410755), (-6261360113060325), (-5563169626615965), (-5776976536083480)], ![(-4456228796410755), (-6261360113060325), (-5776976536083480), (-5563169626615965)]], ![![(-5890623365193840), (-7347687178510770), (-4486204137917775), (-4486204137917775)], ![(-2329296604048050), (-5101477835638275), (-2612890883924685), (-2612890883924685)], ![(-5153971954253850), (-6230613337767000), (-4398755829897975), (-5636217557794005)], ![(-5153971954253850), (-6230613337767000), (-5636217557794005), (-4398755829897975)]], ![![(-4072016675335245), (-4486204137917775), (-4486204137917775), (-1356771041569125)], ![(-1619449056654975), (-3254722808902110), (-4168908417908325), (-4663584633376305)], ![(-1619449056654975), (-4168908417908325), (-3254722808902110), (-4663584633376305)], ![(-2559144931391685), (-4990724908632645), (-4990724908632645), (-1551060423996720)]], ![![(-4072016675335245), (-4486204137917775), (-1356771041569125), (-4486204137917775)], ![(-1619449056654975), (-3254722808902110), (-4663584633376305), (-4168908417908325)], ![(-2559144931391685), (-4990724908632645), (-1551060423996720), (-4990724908632645)], ![(-1619449056654975), (-4168908417908325), (-4663584633376305), (-3254722808902110)]]] x15 x16 x19
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
      trianglePartialAct (state x15 x16 x19).2 ((completedPartial x15 x16 x19) ∘ lhsTriangle 2) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x15 x16 x19 : Fin 4),
    (mkTriangle (state x15 x16 x19)).row.lower = table x15 x16 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 16) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  triangleBlock F1 2 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := triangle_from_assignment (state (e 15) (e 16) (e 19)) ((completedPartial (e 15) (e 16) (e 19)) ∘ lhsTriangle 2)
    (assignment_receipt (e 15) (e 16) (e 19))
  have compatible := compatible_project (completedPartial (e 15) (e 16) (e 19)) e (lhsTriangle 2)
    (completedCompatible e hp)
  have lower := triangle_valid_lower (mkTriangle (state (e 15) (e 16) (e 19)))
    ((completedPartial (e 15) (e 16) (e 19)) ∘ lhsTriangle 2) (e ∘ lhsTriangle 2) valid compatible
  change (mkTriangle (state (e 15) (e 16) (e 19))).row.lower ≤ triangleBlock F1 2 e at lower
  rw [lower_receipt (e 15) (e 16) (e 19)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor02

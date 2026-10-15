/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor25
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x13 x16 x18 : Fin 4) : Fin 8689 × LocalSym :=
  ![![![(0, (0, 0)), (4, (0, 0)), (4, (0, 2)), (4, (0, 3))], ![(4, (6, 0)), (14, (0, 0)), (21, (0, 0)), (21, (0, 1))], ![(4, (6, 2)), (21, (0, 2)), (14, (0, 2)), (21, (0, 4))], ![(4, (6, 3)), (21, (0, 3)), (21, (0, 5)), (14, (0, 3))]], ![![(944, (0, 6)), (497, (10, 6)), (953, (0, 6)), (953, (0, 7))], ![(497, (4, 6)), (145, (4, 6)), (867, (4, 12)), (867, (4, 13))], ![(953, (6, 6)), (867, (10, 12)), (968, (0, 6)), (978, (0, 6))], ![(953, (6, 7)), (867, (10, 13)), (978, (0, 7)), (968, (0, 7))]], ![![(944, (0, 8)), (953, (0, 8)), (497, (10, 8)), (953, (0, 10))], ![(953, (6, 8)), (968, (0, 8)), (867, (10, 14)), (978, (0, 8))], ![(497, (4, 8)), (867, (4, 14)), (145, (4, 8)), (867, (4, 16))], ![(953, (6, 10)), (978, (0, 10)), (867, (10, 16)), (968, (0, 10))]], ![![(944, (0, 9)), (953, (0, 9)), (953, (0, 11)), (497, (10, 9))], ![(953, (6, 9)), (968, (0, 9)), (978, (0, 9)), (867, (10, 15))], ![(953, (6, 11)), (978, (0, 11)), (968, (0, 11)), (867, (10, 17))], ![(497, (4, 9)), (867, (4, 15)), (867, (4, 17)), (145, (4, 9))]]] x13 x16 x18
def table (x13 x16 x18 : Fin 4) : ℤ :=
  ![![![342684662906040, 1693600988588145, 1693600988588145, 1693600988588145], ![1693600988588145, 3044532442067025, 3044532106670145, 3044532106670145], ![1693600988588145, 3044532106670145, 3044532442067025, 3044532106670145], ![1693600988588145, 3044532106670145, 3044532106670145, 3044532442067025]], ![![(-114228225626970), (-594470238080355), (-549565382241330), (-549565382241330)], ![(-594470238080355), (-749342940678150), (-948365394964260), (-948365394964260)], ![(-549565382241330), (-948365394964260), (-1147594754188155), (-1147801330716495)], ![(-549565382241330), (-948365394964260), (-1147801330716495), (-1147594754188155)]], ![![(-114228225626970), (-549565382241330), (-594470238080355), (-549565382241330)], ![(-549565382241330), (-1147594754188155), (-948365394964260), (-1147801330716495)], ![(-594470238080355), (-948365394964260), (-749342940678150), (-948365394964260)], ![(-549565382241330), (-1147801330716495), (-948365394964260), (-1147594754188155)]], ![![(-114228225626970), (-549565382241330), (-549565382241330), (-594470238080355)], ![(-549565382241330), (-1147594754188155), (-1147801330716495), (-948365394964260)], ![(-549565382241330), (-1147801330716495), (-1147594754188155), (-948365394964260)], ![(-594470238080355), (-948365394964260), (-948365394964260), (-749342940678150)]]] x13 x16 x18
private def completedPartial (x13 x16 x18 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (Function.update (prefixPartial 13 4) (13 : Fin 20) (some x13)) (16 : Fin 20) (some x16)) (18 : Fin 20) (some x18))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 13) (e 16) (e 18)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ (compatible_fill _ _ hp 13) 16) 18)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x13 x16 x18 : Fin 4),
    EJMSingletonCacheData.assignment (state x13 x16 x18).1 =
      singletonPartialAct (state x13 x16 x18).2 ((completedPartial x13 x16 x18) ∘ lhsSingleton 9) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x13 x16 x18 : Fin 4),
    (mkSingleton (state x13 x16 x18)).row.lower = table x13 x16 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 16) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 9 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 13) (e 16) (e 18)) ((completedPartial (e 13) (e 16) (e 18)) ∘ lhsSingleton 9)
    (assignment_receipt (e 13) (e 16) (e 18))
  have compatible := compatible_project (completedPartial (e 13) (e 16) (e 18)) e (lhsSingleton 9)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 13) (e 16) (e 18)))
    ((completedPartial (e 13) (e 16) (e 18)) ∘ lhsSingleton 9) (e ∘ lhsSingleton 9) valid compatible
  change (mkSingleton (state (e 13) (e 16) (e 18))).row.lower ≤ singletonBlock F2 9 e at lower
  rw [lower_receipt (e 13) (e 16) (e 18)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor25

/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor29
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (LocalSym)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundTransport (singletonPartialAct)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness (singleton_valid_lower)
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common

private def state (x14 x17 : Fin 4) : Fin 8689 × LocalSym :=
  ![![(0, (0, 0)), (944, (0, 6)), (944, (0, 8)), (944, (0, 9))], ![(4, (0, 0)), (497, (10, 6)), (953, (0, 8)), (953, (0, 9))], ![(4, (0, 2)), (953, (0, 6)), (497, (10, 8)), (953, (0, 11))], ![(4, (0, 3)), (953, (0, 7)), (953, (0, 10)), (497, (10, 9))]] x14 x17
def table (x14 x17 : Fin 4) : ℤ :=
  ![![342684662906040, (-114228225626970), (-114228225626970), (-114228225626970)], ![1693600988588145, (-594470238080355), (-549565382241330), (-549565382241330)], ![1693600988588145, (-549565382241330), (-594470238080355), (-549565382241330)], ![1693600988588145, (-549565382241330), (-549565382241330), (-594470238080355)]] x14 x17
private def completedPartial (x14 x17 : Fin 4) : Partial (Fin 20) (Fin 4) :=
  (Function.update (Function.update (prefixPartial 13 4) (14 : Fin 20) (some x14)) (17 : Fin 20) (some x17))

private theorem completedCompatible (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) :
    Compatible (completedPartial (e 14) (e 17)) e := by
  unfold completedPartial
  exact (compatible_fill _ _ (compatible_fill _ _ hp 14) 17)

set_option trace.profiler true in
private theorem assignment_receipt : ∀ (x14 x17 : Fin 4),
    EJMSingletonCacheData.assignment (state x14 x17).1 =
      singletonPartialAct (state x14 x17).2 ((completedPartial x14 x17) ∘ lhsSingleton 13) := by
  decide +kernel

set_option trace.profiler true in
private theorem lower_receipt : ∀ (x14 x17 : Fin 4),
    (mkSingleton (state x14 x17)).row.lower = table x14 x17 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 17)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  singletonBlock F2 13 e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  have valid := singleton_from_assignment (state (e 14) (e 17)) ((completedPartial (e 14) (e 17)) ∘ lhsSingleton 13)
    (assignment_receipt (e 14) (e 17))
  have compatible := compatible_project (completedPartial (e 14) (e 17)) e (lhsSingleton 13)
    (completedCompatible e hp)
  have lower := singleton_valid_lower (mkSingleton (state (e 14) (e 17)))
    ((completedPartial (e 14) (e 17)) ∘ lhsSingleton 13) (e ∘ lhsSingleton 13) valid compatible
  change (mkSingleton (state (e 14) (e 17))).row.lower ≤ singletonBlock F2 13 e at lower
  rw [lower_receipt (e 14) (e 17)] at lower
  exact lower

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor29

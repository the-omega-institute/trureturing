/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor28

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group02
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x13 x15 x16 : Fin 4) : ℤ :=
  TransientEJMAnchor13674Factor28.table x13 x15 x16

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x13 x15 x16 : Fin 4),
    table x13 x15 x16 = TransientEJMAnchor13674Factor28.table x13 x15 x16 := by
  rfl

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 15) (e 16)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor28.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 13) (e 15) (e 16) ≤ TransientEJMAnchor13674Factor28.score e
  rw [sum_receipt (e 13) (e 15) (e 16)]
  exact TransientEJMAnchor13674Factor28.bound e hp

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group02

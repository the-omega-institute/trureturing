/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group12
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group17

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Merge19
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Common (checked_finite_table_merge_lower)

def table (x14 x17 x19 : Fin 4) : ℤ :=
  ![![![3387201977176290, 3201952567817640, 4811563895949720, 4811563895949720], ![4447710197791770, 4994224027419900, 4069984568526240, 4069984568526240], ![4433961329389410, 5664143365829130, 4560519205495890, 4371767721664980], ![4433961329389410, 5664143365829130, 4371767721664980, 4560519205495890]], ![![1099130750507790, 825744002163990, 1524955876919475, 1524955876919475], ![2025918722594130, 2827924458568755, 1394163817838610, 1394163817838610], ![1352301913080300, 2214517314359805, 900676668159450, 268212811261395], ![1352301913080300, 2214517314359805, 268212811261395, 900676668159450]], ![![1144035606346815, 1188104275839390, 1524955876919475, 1761652128135900], ![1210895730611385, 1083149773944420, 1778978744931570, 896841984793755], ![1352301913080300, 2078740426137375, 1080805398665265, 2560262438858670], ![1729357482266505, 1370885611357080, 1543292457570045, 2579037131683740]], ![![1144035606346815, 1188104275839390, 1761652128135900, 1524955876919475], ![1210895730611385, 1083149773944420, 896841984793755, 1778978744931570], ![1729357482266505, 1370885611357080, 2579037131683740, 1543292457570045], ![1352301913080300, 2078740426137375, 2560262438858670, 1080805398665265]]] x14 x17 x19

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x14 x17 x19 : Fin 4),
    table x14 x17 x19 = TransientEJMAnchor13674Group12.table x14 x17 x19 + TransientEJMAnchor13674Group17.table x17 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 17) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Group12.score e + TransientEJMAnchor13674Group17.score e

theorem sum_at (e : Event (Fin 20) (Fin 4)) :
    lowerAt e = TransientEJMAnchor13674Group12.lowerAt e + TransientEJMAnchor13674Group17.lowerAt e := by
  exact sum_receipt (e 14) (e 17) (e 19)

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  exact checked_finite_table_merge_lower (prefixPartial 13 4)
    TransientEJMAnchor13674Group12.lowerAt TransientEJMAnchor13674Group17.lowerAt lowerAt TransientEJMAnchor13674Group12.score TransientEJMAnchor13674Group17.score
    sum_at TransientEJMAnchor13674Group12.bound TransientEJMAnchor13674Group17.bound e hp

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Merge19

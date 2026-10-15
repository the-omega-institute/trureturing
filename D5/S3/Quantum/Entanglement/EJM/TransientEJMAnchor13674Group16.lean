/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor09
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group16
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x15 x17 x18 : Fin 4) : ℤ :=
  ![![![(-4176225093858090), 7253932577642205, 1955706411325485, 1955706411325485], ![(-160975451465010), 48289541403285, (-2506765329848325), (-2506765329848325)], ![(-154107641352210), (-1543580228093085), (-2723714160425895), (-2790494362408935)], ![(-154107641352210), (-1543580228093085), (-2790494362408935), (-2723714160425895)]], ![![479996460012615, 22341258212971425, 10094080917886875, 10094080917886875], ![5894978857027260, 5508151450830210, 5678503173623280, 5678503173623280], ![7457864270998050, 3050291101685100, 10301132249422560, 5709389725566345], ![7457864270998050, 3050291101685100, 5709389725566345, 10301132249422560]], ![![2298603149871210, 15791930985387375, 21090157151704095, 10900390648298970], ![6778000995053925, 12270664376960535, 6458296252016700, 6952782535026510], ![6771133184941125, 8111384958916785, 13957542915046185, 6817781021503725], ![8022611979957120, 8524426747681845, 6736336527258975, 7305020691574515]], ![![2298603149871210, 15791930985387375, 10900390648298970, 21090157151704095], ![6778000995053925, 12270664376960535, 6952782535026510, 6458296252016700], ![8022611979957120, 8524426747681845, 7305020691574515, 6736336527258975], ![6771133184941125, 8111384958916785, 6817781021503725, 13957542915046185]]] x15 x17 x18

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x15 x17 x18 : Fin 4),
    table x15 x17 x18 = TransientEJMAnchor13674Factor09.table x15 x17 x18 + TransientEJMAnchor13674Factor14.table x15 x17 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 17) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor09.score e + TransientEJMAnchor13674Factor14.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 15) (e 17) (e 18) ≤ TransientEJMAnchor13674Factor09.score e + TransientEJMAnchor13674Factor14.score e
  rw [sum_receipt (e 15) (e 17) (e 18)]
  exact add_le_add (TransientEJMAnchor13674Factor09.bound e hp) (TransientEJMAnchor13674Factor14.bound e hp)

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group16

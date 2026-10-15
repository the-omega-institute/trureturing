/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor08
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor15

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group07
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x13 x18 x19 : Fin 4) : ℤ :=
  ![![![(-4176225093858090), 479996460012615, 2298603149871210, 2298603149871210], ![2331512948555700, 6381230943997455, 4930356796251705, 4930356796251705], ![1914391028795700, 4249509577660620, 5726799339114945, 4733893154637465], ![1914391028795700, 4249509577660620, 4733893154637465, 5726799339114945]], ![![(-160975451465010), 5894978857027260, 6778000995053925, 6778000995053925], ![18654205974875835, 7404179311785165, 6282367857350130, 6282367857350130], ![11674662122794125, 7695445355083395, 9637158777989925, 7873572772406250], ![11674662122794125, 7695445355083395, 7873572772406250, 9637158777989925]], ![![(-154107641352210), 7457864270998050, 6771133184941125, 8022611979957120], ![11218173287716395, 7385200907280105, 7021935006129225, 7550195615206335], ![19435510442447190, 8939941180070355, 8123128188913920, 6824719670232555], ![9600382489135620, 7627057260457635, 7709593799956230, 7921208101232790]], ![![(-154107641352210), 7457864270998050, 8022611979957120, 6771133184941125], ![11218173287716395, 7385200907280105, 7550195615206335, 7021935006129225], ![9600382489135620, 7627057260457635, 7921208101232790, 7709593799956230], ![19435510442447190, 8939941180070355, 6824719670232555, 8123128188913920]]] x13 x18 x19

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x13 x18 x19 : Fin 4),
    table x13 x18 x19 = TransientEJMAnchor13674Factor08.table x13 x18 x19 + TransientEJMAnchor13674Factor15.table x13 x18 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 18) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor08.score e + TransientEJMAnchor13674Factor15.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 13) (e 18) (e 19) ≤ TransientEJMAnchor13674Factor08.score e + TransientEJMAnchor13674Factor15.score e
  rw [sum_receipt (e 13) (e 18) (e 19)]
  exact add_le_add (TransientEJMAnchor13674Factor08.bound e hp) (TransientEJMAnchor13674Factor15.bound e hp)

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group07

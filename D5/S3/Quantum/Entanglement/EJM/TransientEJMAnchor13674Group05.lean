/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor03
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor07

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group05
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x13 x16 x17 : Fin 4) : ℤ :=
  ![![![6037221791824860, (-160975451465010), (-154107641352210), (-154107641352210)], ![7253932577642205, (-1688936323718280), (-4162097569365645), (-4162097569365645)], ![1955706411325485, (-2509008862465560), (-3375814861803930), (-2374007348942775)], ![1955706411325485, (-2509008862465560), (-2374007348942775), (-3375814861803930)]], ![![(-160975451465010), (-3677496117178065), (-982735099405605), (-982735099405605)], ![3518339460106380, (-4310242413186255), (-4252263430605645), (-4252263430605645)], ![1419899854581390, (-2556848049708225), 40309149965175, (-1610608022847915)], ![1419899854581390, (-2556848049708225), (-1610608022847915), 40309149965175]], ![![(-154107641352210), (-982735099405605), (-2121478513320075), 261875885497590], ![3882522007917735, (-4245725140940010), (-2275537326476505), (-3906375259337460)], ![1380532939263660, (-2549511180071310), (-1557217115862135), (-1737521538433590)], ![(-654379779077115), (-2058316027858545), (-2341507111773375), (-1675641526791960)]], ![![(-154107641352210), (-982735099405605), 261875885497590, (-2121478513320075)], ![3882522007917735, (-4245725140940010), (-3906375259337460), (-2275537326476505)], ![(-654379779077115), (-2058316027858545), (-1675641526791960), (-2341507111773375)], ![1380532939263660, (-2549511180071310), (-1737521538433590), (-1557217115862135)]]] x13 x16 x17

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x13 x16 x17 : Fin 4),
    table x13 x16 x17 = TransientEJMAnchor13674Factor03.table x13 x16 x17 + TransientEJMAnchor13674Factor07.table x13 x16 x17 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 13) (e 16) (e 17)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor03.score e + TransientEJMAnchor13674Factor07.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 13) (e 16) (e 17) ≤ TransientEJMAnchor13674Factor03.score e + TransientEJMAnchor13674Factor07.score e
  rw [sum_receipt (e 13) (e 16) (e 17)]
  exact add_le_add (TransientEJMAnchor13674Factor03.bound e hp) (TransientEJMAnchor13674Factor07.bound e hp)

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group05

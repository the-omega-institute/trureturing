/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor17
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor18
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor21
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor23

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group10
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x14 x16 x18 : Fin 4) : ℤ :=
  ![![![913825763091150, 4486332727684080, 4531237583523105, 4531237583523105], ![4486332727684080, 8384254385522925, 8185230925046175, 8185230925046175], ![4531237583523105, 8185230925046175, 7986002572012920, 7985794989293940], ![4531237583523105, 8185230925046175, 7985794989293940, 7986002572012920]], ![![4486332727684080, 4027696569981630, 6336519772869195, 6336519772869195], ![6473628920385900, 7822148485988655, 5464148386364850, 5464148386364850], ![5786263242469710, 7878660680188935, 5461195873655340, 4639980532926375], ![5786263242469710, 7878660680188935, 4639980532926375, 5461195873655340]], ![![4531237583523105, 6336519772869195, 4390056843657030, 6573216024085620], ![5786263242469710, 5641324604161155, 7742883791966505, 6932030160523650], ![5658605928403155, 5848963313457810, 6077373801364320, 4966826553319995], ![6163318811655915, 5915060179235025, 7035028977186210, 7139556337179630]], ![![4531237583523105, 6336519772869195, 6573216024085620, 4390056843657030], ![5786263242469710, 5641324604161155, 6932030160523650, 7742883791966505], ![6163318811655915, 5915060179235025, 7139556337179630, 7035028977186210], ![5658605928403155, 5848963313457810, 4966826553319995, 6077373801364320]]] x14 x16 x18

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x14 x16 x18 : Fin 4),
    table x14 x16 x18 = TransientEJMAnchor13674Factor17.table x14 x16 x18 + TransientEJMAnchor13674Factor18.table x14 x16 x18 + TransientEJMAnchor13674Factor21.table x14 x16 x18 + TransientEJMAnchor13674Factor23.table x14 x16 x18 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 14) (e 16) (e 18)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor17.score e + TransientEJMAnchor13674Factor18.score e + TransientEJMAnchor13674Factor21.score e + TransientEJMAnchor13674Factor23.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 14) (e 16) (e 18) ≤ TransientEJMAnchor13674Factor17.score e + TransientEJMAnchor13674Factor18.score e + TransientEJMAnchor13674Factor21.score e + TransientEJMAnchor13674Factor23.score e
  rw [sum_receipt (e 14) (e 16) (e 18)]
  exact add_le_add (add_le_add (add_le_add (TransientEJMAnchor13674Factor17.bound e hp) (TransientEJMAnchor13674Factor18.bound e hp)) (TransientEJMAnchor13674Factor21.bound e hp)) (TransientEJMAnchor13674Factor23.bound e hp)

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group10

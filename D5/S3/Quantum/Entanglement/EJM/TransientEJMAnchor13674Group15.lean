/- Prepared transient actual-prefix semantic bound; uncompiled.
Original anchor: depth13/code4/index674/fuel8. No raw Accepted or
global coverage is asserted. Every original factor, outcome and
scaled integer is retained; no native fact is a mathematical premise. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor02
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Factor06

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group15
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly (prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJMInflationScore (lhsTriangle lhsSingleton triangleBlock singletonBlock)

def table (x15 x16 x19 : Fin 4) : ℤ :=
  ![![![(-4176225093858090), (-9733450425670335), (-7914843735811740), (-7914843735811740)], ![(-7881933937127250), (-11666132183568135), (-12078211516048860), (-12078211516048860)], ![(-8299055856887250), (-12759058734639945), (-12320563788450645), (-12274675157663100)], ![(-8299055856887250), (-12759058734639945), (-12274675157663100), (-12320563788450645)]], ![![(-9733450425670335), (-13238310543704610), (-8558220813253020), (-8558220813253020)], ![(-6368403480698805), (-10010215857371730), (-8193403778393925), (-8193403778393925)], ![(-9610200750664605), (-12491973450827325), (-9961925456513940), (-11413194093877485)], ![(-9610200750664605), (-12491973450827325), (-11413194093877485), (-9961925456513940)]], ![![(-7914843735811740), (-8558220813253020), (-10376827503111615), (-5428787716904370)], ![(-6075677853065730), (-8817892435518075), (-10430268530968650), (-10440561169459785)], ![(-5658555933305730), (-9749421312377565), (-8163460830635565), (-10244097527845545)], ![(-7015373727802440), (-10767701444716125), (-11252085021692970), (-7114230050612685)]], ![![(-7914843735811740), (-8558220813253020), (-5428787716904370), (-10376827503111615)], ![(-6075677853065730), (-8817892435518075), (-10440561169459785), (-10430268530968650)], ![(-7015373727802440), (-10767701444716125), (-7114230050612685), (-11252085021692970)], ![(-5658555933305730), (-9749421312377565), (-10244097527845545), (-8163460830635565)]]] x15 x16 x19

set_option trace.profiler true in
private theorem sum_receipt : ∀ (x15 x16 x19 : Fin 4),
    table x15 x16 x19 = TransientEJMAnchor13674Factor02.table x15 x16 x19 + TransientEJMAnchor13674Factor06.table x15 x16 x19 := by
  decide +kernel

def lowerAt (e : Event (Fin 20) (Fin 4)) : ℤ :=
  table (e 15) (e 16) (e 19)
def score (e : Event (Fin 20) (Fin 4)) : ℤ :=
  TransientEJMAnchor13674Factor02.score e + TransientEJMAnchor13674Factor06.score e

theorem bound (e : Event (Fin 20) (Fin 4))
    (hp : Compatible (prefixPartial 13 4) e) : lowerAt e ≤ score e := by
  change table (e 15) (e 16) (e 19) ≤ TransientEJMAnchor13674Factor02.score e + TransientEJMAnchor13674Factor06.score e
  rw [sum_receipt (e 15) (e 16) (e 19)]
  exact add_le_add (TransientEJMAnchor13674Factor02.bound e hp) (TransientEJMAnchor13674Factor06.bound e hp)

#print axioms bound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674Group15

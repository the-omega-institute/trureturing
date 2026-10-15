/- Actual original prefix13/code4/index674; source only, uncompiled.
All 32 original factors and all four values are retained.
Boolean receipts are proved by kernel reduction, never native_decide. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket04
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket05
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon

def table (x19 : Fin 4) : ℤ :=
  ![0, (-45112), 3858, 3858] x19

private def inequalityCheck : Bool :=
  all4 (fun x17 => all4 (fun x19 => decide (0 + table x19 ≤ TransientEJMAnchor13674VEGroups.table13 x17 x19 + TransientEJMAnchor13674VEBucket04.table x17 x19)))

set_option trace.profiler true in
private theorem inequalityChecked : inequalityCheck = true := by
  decide +kernel

theorem inequality (x17 x19 : Fin 4) :
    0 + table x19 ≤ TransientEJMAnchor13674VEGroups.table13 x17 x19 + TransientEJMAnchor13674VEBucket04.table x17 x19 := by
  have h0 := inequalityChecked
  unfold inequalityCheck at h0
  have h1 := all4_sound h0 x17
  have h2 := all4_sound h1 x19
  exact of_decide_eq_true h2

def lowerAt (e : Assignment) : ℤ := table (e 19)

theorem inequality_at (e : Assignment) :
    0 + lowerAt e ≤ TransientEJMAnchor13674VEGroups.lowerAt13 e + TransientEJMAnchor13674VEBucket04.lowerAt e := by
  exact inequality (e 17) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket05

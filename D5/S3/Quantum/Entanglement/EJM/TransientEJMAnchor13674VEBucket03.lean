/- Actual original prefix13/code4/index674; source only, uncompiled.
All 32 original factors and all four values are retained.
Boolean receipts are proved by kernel reduction, never native_decide. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket02
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket03
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon

def table (x14 x17 x19 : Fin 4) : ℤ :=
  ![![![0, 97098248, 1242743340, 1242743340], ![(-86377094), (-99251226), 278472958, 278472958], ![(-84413230), (-194840286), (-37133010), 11461314], ![(-84413230), (-194840286), 11461314, (-37133010)]], ![![139835026, 816923027, 2566787533, 2566787533], ![680591150, 915353842, 1581511425, 1581511425], ![589632959, 947247628, 1114941567, 1074000762], ![589632959, 947247628, 1074000762, 1114941567]], ![![(-29496096), 936161991, 2573214048, 2344357188], ![457559929, 668361997, 1921756943, 1568907166], ![520683022, 681687726, 1018271419, 955502994], ![460294564, 573724083, 1323120863, 580646942]], ![![(-29496096), 936161991, 2344357188, 2573214048], ![457559929, 668361997, 1568907166, 1921756943], ![460294564, 573724083, 580646942, 1323120863], ![520683022, 681687726, 955502994, 1018271419]]] x14 x17 x19

private def inequalityCheck : Bool :=
  all4 (fun x14 => all4 (fun x17 => all4 (fun x18 => all4 (fun x19 => decide (0 + table x14 x17 x19 ≤ TransientEJMAnchor13674VEBucket02.table x14 x17 x18 x19)))))

set_option trace.profiler true in
private theorem inequalityChecked : inequalityCheck = true := by
  decide +kernel

theorem inequality (x14 x17 x18 x19 : Fin 4) :
    0 + table x14 x17 x19 ≤ TransientEJMAnchor13674VEBucket02.table x14 x17 x18 x19 := by
  have h0 := inequalityChecked
  unfold inequalityCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x18
  have h4 := all4_sound h3 x19
  exact of_decide_eq_true h4

def lowerAt (e : Assignment) : ℤ := table (e 14) (e 17) (e 19)

theorem inequality_at (e : Assignment) :
    0 + lowerAt e ≤ TransientEJMAnchor13674VEBucket02.lowerAt e := by
  exact inequality (e 14) (e 17) (e 18) (e 19)

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEBucket03

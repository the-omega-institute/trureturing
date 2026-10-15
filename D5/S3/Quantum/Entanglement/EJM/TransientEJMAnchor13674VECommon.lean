/- Actual original prefix13/code4/index674; source only, uncompiled.
All 32 original factors and all four values are retained.
Boolean receipts are proved by kernel reduction, never native_decide. -/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
abbrev Assignment := Fin 20 → Fin 4

def all4 (p : Fin 4 → Bool) : Bool := p 0 && p 1 && p 2 && p 3

theorem all4_sound {p : Fin 4 → Bool} (h : all4 p = true) (a : Fin 4) : p a = true := by
  fin_cases a <;> simp_all [all4, Bool.and_eq_true_iff]

#print axioms all4_sound
end D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon

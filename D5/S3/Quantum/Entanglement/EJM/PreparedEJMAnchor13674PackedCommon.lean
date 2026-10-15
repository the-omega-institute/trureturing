/- Prepared, uncompiled source; no kernel acceptance is asserted.
Actual prefix depth13/code4/index674, first bucket only.
Source cells are scope-sized. Broadcasts are structural proofs.
No native-expanded 16384-by-8 source binding is used. -/
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon
import D5.S0.Certificates.TransientPackedBroadcastFixedPrepared
import D5.S0.Certificates.TransientPackedConsumerHelpersPrepared
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
open EJMPackedBroadcastPrepared

abbrev Assignment := Fin 20 → Fin 4

def unionCode (e : Assignment) : Nat := (((((((0 * 4 + (e 13).val) * 4 + (e 14).val) * 4 + (e 15).val) * 4 + (e 16).val) * 4 + (e 17).val) * 4 + (e 18).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 16384 := by
  have h13 := (e 13).isLt
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

theorem all_le_mem (xs : List Nat) (bound : Nat)
    (h : xs.all (fun x => decide (x ≤ bound)) = true) :
    ∀ x ∈ xs, x ≤ bound := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact of_decide_eq_true h.1
    · exact ih h.2 x hx

theorem getD_le (xs : List Nat) (bound : Nat)
    (h : ∀ x ∈ xs, x ≤ bound) (i : Nat) : xs.getD i 0 ≤ bound := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero => exact h a (by simp)
    | succ i =>
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx)) i

theorem packed_source_lane_le (xs : List Nat) (bound : Nat)
    (hbound : bound < 2 ^ 64)
    (h : xs.all (fun x => decide (x ≤ bound)) = true) (i : Nat) :
    digit (2 ^ 64) i (Nat.ofDigits (2 ^ 64) xs) ≤ bound := by
  have hx := all_le_mem xs bound h
  rw [digit_ofDigits _ (by positivity) xs
    (fun x hmem => (hx x hmem).trans_lt hbound)]
  exact getD_le xs bound hx i

#print axioms packed_source_lane_le
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

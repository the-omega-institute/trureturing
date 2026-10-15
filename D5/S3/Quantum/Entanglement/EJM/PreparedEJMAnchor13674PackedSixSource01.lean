/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource01
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [134120017, 68729371, 68729371, 68729371, 327455100, 0, 6426515, 6426515, 327455100, 6426515, 0, 6426515, 327455100, 6426515, 6426515, 0]

def sourcePacked : Nat := 0x620f930000000000620f93000000001384917c0000000000620f9300000000000000000000000000620f93000000001384917c0000000000620f930000000000620f930000000000000000000000001384917c000000000418ba1b000000000418ba1b000000000418ba1b0000000007fe8251

def sourceCode (e : Assignment) : Nat := ((0 * 4 + (e 14).val) * 4 + (e 17).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 16 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 327455100)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 327455100 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 327455100
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 2) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 327455100
      sourceBoundChecked x hx).trans_lt (by decide : 327455100 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x14 => all4 (fun x17 => decide (((digit (2 ^ 64) ((0 * 4 + x14.val) * 4 + x17.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table01 x14 x17 + 134120017)))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x14 x17 : Fin 4) :
    ((digit (2 ^ 64) ((0 * 4 + x14.val) * 4 + x17.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table01 x14 x17 + 134120017 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  exact of_decide_eq_true h2

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + 134120017 := by
  exact source_binding (e 14) (e 17)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource01

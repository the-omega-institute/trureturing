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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource13
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [13255895, 0, 115178984, 115178984, 89142699, 128249598, 62113780, 62113780, 88158871, 176187027, 97214975, 83708482, 88158871, 176187027, 83708482, 97214975]

def sourcePacked : Nat := 0x5cb61ff0000000004fd4a42000000000a80669300000000054132970000000004fd4a420000000005cb61ff000000000a80669300000000054132970000000003b3c7f40000000003b3c7f40000000007a4eefe00000000055035ab0000000006dd7de80000000006dd7de800000000000000000000000000ca44d7

def sourceCode (e : Assignment) : Nat := ((0 * 4 + (e 17).val) * 4 + (e 19).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 16 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 176187027)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 176187027 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 176187027
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 2) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 176187027
      sourceBoundChecked x hx).trans_lt (by decide : 176187027 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x17 => all4 (fun x19 => decide (((digit (2 ^ 64) ((0 * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table13 x17 x19 + 13255895)))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x17 x19 : Fin 4) :
    ((digit (2 ^ 64) ((0 * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table13 x17 x19 + 13255895 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x17
  have h2 := all4_sound h1 x19
  exact of_decide_eq_true h2

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + 13255895 := by
  exact source_binding (e 17) (e 19)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource13

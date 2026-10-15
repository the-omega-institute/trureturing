/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixTables

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource22
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [7931759500, 7950211207, 9211035283, 9211035283, 7855878564, 7816720685, 8128309051, 8128309051, 7856858600, 7769069054, 7847804278, 7882892109, 7856858600, 7769069054, 7882892109, 7847804278]

def sourcePacked : Nat := 0x1d3c3fd7600000001d5db634d00000001cf1295fe00000001d44e25e800000001d5db634d00000001d3c3fd7600000001cf1295fe00000001d44e25e800000001e47c273b00000001e47c273b00000001d1e9b12d00000001d43f31a40000000225053e930000000225053e9300000001d9de988700000001d8c50b8c

def sourceCode (e : Assignment) : Nat := ((0 * 4 + (e 17).val) * 4 + (e 19).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 16 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 9211035283)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 9211035283 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 9211035283
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 2) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 9211035283
      sourceBoundChecked x hx).trans_lt (by decide : 9211035283 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x17 => all4 (fun x19 => decide (((digit (2 ^ 64) ((0 * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table22 x17 x19 + 7931759500)))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x17 x19 : Fin 4) :
    ((digit (2 ^ 64) ((0 * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table22 x17 x19 + 7931759500 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x17
  have h2 := all4_sound h1 x19
  exact of_decide_eq_true h2

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19) + 7931759500 := by
  exact source_binding (e 17) (e 19)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource22

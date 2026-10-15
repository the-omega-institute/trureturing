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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource06
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [0, 511275878, 517702393, 517702393, 511275878, 1069123165, 1040640115, 1040640115, 517702393, 1040640115, 1012127742, 1012098034, 517702393, 1040640115, 1012098034, 1012127742, 511275878, 445638608, 776063607, 776063607, 795685850, 988677923, 651215020, 651215020, 697314176, 996765611, 650792474, 533265035, 697314176, 996765611, 533265035, 650792474, 517702393, 776063607, 497497448, 809938162, 697314176, 676571423, 977334033, 861289500, 679044623, 706287436, 738976182, 580041287, 751276119, 715746825, 876030076, 890989408, 517702393, 776063607, 809938162, 497497448, 697314176, 676571423, 861289500, 977334033, 751276119, 715746825, 890989408, 876030076, 679044623, 706287436, 580041287, 738976182]

def sourcePacked : Nat := 0x2c0be1b6000000002292ba47000000002a19174c000000002879660f000000003437287c00000000351b6b60000000002aa96e09000000002cc79057000000003a40ef110000000033563c1c000000002853a91f0000000029902b80000000001da73568000000003046acf2000000002e41ca77000000001edb82f900000000351b6b60000000003437287c000000002aa96e09000000002cc79057000000002292ba47000000002c0be1b6000000002a19174c000000002879660f0000000033563c1c000000003a40ef11000000002853a91f0000000029902b80000000003046acf2000000001da73568000000002e41ca77000000001edb82f90000000026ca4e1a000000001fc8fa8b000000003b696fab0000000029902b80000000001fc8fa8b0000000026ca4e1a000000003b696fab0000000029902b800000000026d0c0ac0000000026d0c0ac000000003aee0723000000002f6d33da000000002e41ca77000000002e41ca77000000001a8fe7d0000000001e797366000000003c53d7fe000000003c5363f2000000003e06e873000000001edb82f9000000003c5363f2000000003c53d7fe000000003e06e873000000001edb82f9000000003e06e873000000003e06e873000000003fb9865d000000001e797366000000001edb82f9000000001edb82f9000000001e7973660000000000000000

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 14).val) * 4 + (e 16).val) * 4 + (e 18).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 1069123165)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 1069123165 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 1069123165
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 1069123165
      sourceBoundChecked x hx).trans_lt (by decide : 1069123165 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x14 => all4 (fun x16 => all4 (fun x18 => decide (((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table06 x14 x16 x18 + 0))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x14 x16 x18 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table06 x14 x16 x18 + 0 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table06 (e 14) (e 16) (e 18) + 0 := by
  exact source_binding (e 14) (e 16) (e 18)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource06

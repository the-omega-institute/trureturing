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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource12
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [1296911592, 501594665, 761862802, 761862802, 766572656, 225000785, 166026450, 166026450, 706876656, 68587659, 131342439, 137909746, 706876656, 68587659, 137909746, 131342439, 501594665, 0, 669786514, 669786514, 983180103, 461985648, 721996951, 721996951, 519233423, 106811311, 468896682, 261199775, 519233423, 106811311, 261199775, 468896682, 761862802, 669786514, 409518377, 1117652304, 1025073248, 632623861, 401870216, 400397195, 1084769248, 499309007, 726282207, 428513899, 890589582, 353578831, 284256744, 876441855, 761862802, 669786514, 1117652304, 409518377, 1025073248, 632623861, 400397195, 401870216, 890589582, 353578831, 876441855, 284256744, 1084769248, 499309007, 428513899, 726282207]

def sourcePacked : Nat := 0x2b4a2fdf00000000198a9a6b000000001dc2d9cf0000000040a843e00000000010f169e800000000343d70ff0000000015132f4f000000003515518e0000000017f40d880000000017dd938b0000000025b512f5000000003d196060000000001868c12900000000429e05500000000027ec2192000000002d691a9200000000343d70ff0000000010f169e80000000015132f4f000000003515518e00000000198a9a6b000000002b4a2fdf000000001dc2d9cf0000000040a843e00000000017dd938b0000000017f40d880000000025b512f5000000003d19606000000000429e0550000000001868c1290000000027ec2192000000002d691a92000000001bf2cbaa000000000f91979f00000000065dcfaf000000001ef2df8f000000000f91979f000000001bf2cbaa00000000065dcfaf000000001ef2df8f000000002b08cc97000000002b08cc97000000001b895770000000003a9a23470000000027ec21920000000027ec21920000000000000000000000001de5ba290000000007d4206700000000083855f2000000000416908b000000002a2214f000000000083855f20000000007d42067000000000416908b000000002a2214f00000000009e55cd20000000009e55cd2000000000d693d51000000002db0f870000000002d691a92000000002d691a92000000001de5ba29000000004d4d4ce8

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 15).val) * 4 + (e 16).val) * 4 + (e 19).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 1296911592)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 1296911592 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 1296911592
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 1296911592
      sourceBoundChecked x hx).trans_lt (by decide : 1296911592 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x15 => all4 (fun x16 => all4 (fun x19 => decide (((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x16.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table12 x15 x16 x19 + 1296911592))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x15 x16 x19 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x16.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table12 x15 x16 x19 + 1296911592 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table12 (e 15) (e 16) (e 19) + 1296911592 := by
  exact source_binding (e 15) (e 16) (e 19)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource12

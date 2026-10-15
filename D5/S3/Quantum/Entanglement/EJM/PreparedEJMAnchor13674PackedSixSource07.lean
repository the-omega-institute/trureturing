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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource07
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [213309461, 406644544, 406644544, 406644544, 406644544, 599981792, 599981744, 599981744, 406644544, 599981744, 599981792, 599981744, 406644544, 599981744, 599981744, 599981792, 147918815, 79189444, 85615959, 85615959, 79189444, 57024987, 28542081, 28542081, 85615959, 28542081, 29564, 0, 85615959, 28542081, 0, 29564, 147918815, 85615959, 79189444, 85615959, 85615959, 29564, 28542081, 0, 79189444, 28542081, 57024987, 28542081, 85615959, 0, 28542081, 29564, 147918815, 85615959, 85615959, 79189444, 85615959, 29564, 0, 28542081, 85615959, 0, 29564, 28542081, 79189444, 28542081, 28542081, 57024987]

def sourcePacked : Nat := 0x36621db0000000001b384810000000001b384810000000004b855c40000000001b38481000000000000737c000000000000000000000000051a65570000000001b384810000000000000000000000000000737c00000000051a65570000000004b855c400000000051a655700000000051a65570000000008d10fdf000000000000737c0000000001b38481000000000000000000000000051a65570000000001b3848100000000036621db0000000001b384810000000004b855c400000000000000000000000001b38481000000000000737c00000000051a655700000000051a65570000000004b855c400000000051a65570000000008d10fdf000000000000737c00000000000000000000000001b3848100000000051a65570000000000000000000000000000737c0000000001b3848100000000051a65570000000001b384810000000001b3848100000000036621db0000000004b855c400000000051a655700000000051a65570000000004b855c40000000008d10fdf0000000023c2fee00000000023c2feb00000000023c2feb000000000183ce7400000000023c2feb00000000023c2fee00000000023c2feb000000000183ce7400000000023c2feb00000000023c2feb00000000023c2fee000000000183ce74000000000183ce74000000000183ce74000000000183ce740000000000cb6d815

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 15).val) * 4 + (e 16).val) * 4 + (e 18).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 599981792)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 599981792 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 599981792
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 599981792
      sourceBoundChecked x hx).trans_lt (by decide : 599981792 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x15 => all4 (fun x16 => all4 (fun x18 => decide (((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table07 x15 x16 x18 + 213309461))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x15 x16 x18 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table07 x15 x16 x18 + 213309461 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table07 (e 15) (e 16) (e 18) + 213309461 := by
  exact source_binding (e 15) (e 16) (e 18)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource07

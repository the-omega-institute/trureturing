/- Prepared, uncompiled source; no kernel acceptance is asserted.
Actual prefix depth13/code4/index674, first bucket only.
Source cells are scope-sized. Broadcasts are structural proofs.
No native-expanded 16384-by-8 source binding is used. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VEGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource05
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

def sourceCells : List Nat :=
  [213309461, 406644544, 406644544, 406644544, 406644544, 599981792, 599981744, 599981744, 406644544, 599981744, 599981792, 599981744, 406644544, 599981744, 599981744, 599981792, 147918815, 79189444, 85615959, 85615959, 79189444, 57024987, 28542081, 28542081, 85615959, 28542081, 29564, 0, 85615959, 28542081, 0, 29564, 147918815, 85615959, 79189444, 85615959, 85615959, 29564, 28542081, 0, 79189444, 28542081, 57024987, 28542081, 85615959, 0, 28542081, 29564, 147918815, 85615959, 85615959, 79189444, 85615959, 29564, 0, 28542081, 85615959, 0, 29564, 28542081, 79189444, 28542081, 28542081, 57024987]

def sourcePacked : Nat := 0x36621db0000000001b384810000000001b384810000000004b855c40000000001b38481000000000000737c000000000000000000000000051a65570000000001b384810000000000000000000000000000737c00000000051a65570000000004b855c400000000051a655700000000051a65570000000008d10fdf000000000000737c0000000001b38481000000000000000000000000051a65570000000001b3848100000000036621db0000000001b384810000000004b855c400000000000000000000000001b38481000000000000737c00000000051a655700000000051a65570000000004b855c400000000051a65570000000008d10fdf000000000000737c00000000000000000000000001b3848100000000051a65570000000000000000000000000000737c0000000001b3848100000000051a65570000000001b384810000000001b3848100000000036621db0000000004b855c400000000051a655700000000051a65570000000004b855c40000000008d10fdf0000000023c2fee00000000023c2feb00000000023c2feb000000000183ce7400000000023c2feb00000000023c2fee00000000023c2feb000000000183ce7400000000023c2feb00000000023c2feb00000000023c2fee000000000183ce74000000000183ce74000000000183ce74000000000183ce740000000000cb6d815

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 13).val) * 4 + (e 16).val) * 4 + (e 18).val)

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
  all4 (fun x13 => all4 (fun x16 => all4 (fun x18 => decide (((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table05 x13 x16 x18 + 213309461))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x13 x16 x18 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x16.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table05 x13 x16 x18 + 213309461 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table05 (e 13) (e 16) (e 18) + 213309461 := by
  exact source_binding (e 13) (e 16) (e 18)

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 3) sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 3 0 sourcePacked
    source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) sourcePacked := by
  exact broadcastBits_lane_nat 64 3 0 sourcePacked
    source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 2) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 2 2 stage1
    stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 2 i) stage1 := by
  exact broadcastBits_lane_nat 64 2 2 stage1
    stage1_size i

def stage3 : Nat := broadcastBits (64 * 4 ^ 4) (4 ^ 1) stage2

theorem stage3_size : stage3 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 1 4 stage2
    stage2_size

theorem stage3_lane (i : Nat) :
    digit (2 ^ 64) i stage3 = digit (2 ^ 64) (eraseDigit 4 4 i) stage2 := by
  exact broadcastBits_lane_nat 64 1 4 stage2
    stage2_size i

def stage4 : Nat := broadcastBits (64 * 4 ^ 5) (4 ^ 1) stage3

theorem stage4_size : stage4 < (2 ^ 64) ^ (4 ^ 7) := by
  exact broadcastBits_lt_nat 64 1 5 stage3
    stage3_size

theorem stage4_lane (i : Nat) :
    digit (2 ^ 64) i stage4 = digit (2 ^ 64) (eraseDigit 4 5 i) stage3 := by
  exact broadcastBits_lane_nat 64 1 5 stage3
    stage3_size i

def packed : Nat := stage4

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 2 (eraseDigit 4 4 (eraseDigit 4 5 i))))

theorem packed_size : packed < (2 ^ 64) ^ 16384 := by
  exact stage4_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) sourcePacked := by
  dsimp only [packed, project]
  rw [stage4_lane, stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 599981792 := by
  rw [packed_lane]
  exact source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = sourceCode e := by
  have h13 := (e 13).isLt
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table05 (e 13) (e 16) (e 18) + 213309461 := by
  rw [packed_lane, project_unionCode]
  exact source_binding_at e

#print axioms lane_binding
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource05

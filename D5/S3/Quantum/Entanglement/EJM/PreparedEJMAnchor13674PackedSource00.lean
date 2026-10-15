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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource00
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

def sourceCells : List Nat :=
  [516823704, 189368604, 195795119, 195795119, 503567809, 163499019, 215357859, 215357859, 618746793, 148387066, 148387066, 182261621, 618746793, 148387066, 182261621, 148387066, 592710508, 246118164, 129476937, 129476937, 631817407, 321789540, 72087799, 72087799, 565681589, 182734091, 237806507, 111560358, 565681589, 182734091, 111560358, 237806507, 591726680, 150697974, 150697974, 204659917, 679754836, 186064941, 166633363, 65329406, 600782784, 77007960, 102786909, 317204894, 587276291, 0, 328024465, 182481790, 591726680, 150697974, 204659917, 150697974, 679754836, 186064941, 65329406, 166633363, 587276291, 0, 182481790, 328024465, 600782784, 77007960, 317204894, 102786909]

def sourcePacked : Nat := 0x620675d0000000012e8299e0000000004970c580000000023cf37c000000000138d4191000000000ae0737e000000000000000000000000230120030000000009ee9f930000000003e4d8fe000000000b17202d0000000028843c540000000008fb77f6000000000c32dccd0000000008fb77f60000000023450858000000000ae0737e00000000138d4191000000000000000000000000230120030000000012e8299e000000000620675d0000000004970c580000000023cf37c00000000003e4d8fe0000000009ee9f93000000000b17202d0000000028843c54000000000c32dccd0000000008fb77f60000000008fb77f60000000023450858000000000e2ca3ab0000000006a646a6000000000ae44d0b0000000021b79db50000000006a646a6000000000e2ca3ab000000000ae44d0b0000000021b79db500000000044bf8f700000000044bf8f700000000132e1e640000000025a8c4bf0000000007b7a9490000000007b7a949000000000eab77140000000023540b6c0000000008d834fa000000000add17750000000008d834fa0000000024e153a9000000000add17750000000008d834fa0000000008d834fa0000000024e153a9000000000cd619a3000000000cd619a30000000009becc0b000000001e03d5c1000000000bab98af000000000bab98af000000000b49891c000000001ece1a98

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 13).val) * 4 + (e 15).val) * 4 + (e 16).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 679754836)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 679754836 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 679754836
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 679754836
      sourceBoundChecked x hx).trans_lt (by decide : 679754836 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x13 => all4 (fun x15 => all4 (fun x16 => decide (((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x15.val) * 4 + x16.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table00 x13 x15 x16 + 516823704))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x13 x15 x16 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x15.val) * 4 + x16.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table00 x13 x15 x16 + 516823704 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x15
  have h3 := all4_sound h2 x16
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table00 (e 13) (e 15) (e 16) + 516823704 := by
  exact source_binding (e 13) (e 15) (e 16)

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 3) sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 3 0 sourcePacked
    source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) sourcePacked := by
  exact broadcastBits_lane_nat 64 3 0 sourcePacked
    source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 3) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 3 1 stage1
    stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 1 i) stage1 := by
  exact broadcastBits_lane_nat 64 3 1 stage1
    stage1_size i

def stage3 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 3) stage2

theorem stage3_size : stage3 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 3 2 stage2
    stage2_size

theorem stage3_lane (i : Nat) :
    digit (2 ^ 64) i stage3 = digit (2 ^ 64) (eraseDigit 4 2 i) stage2 := by
  exact broadcastBits_lane_nat 64 3 2 stage2
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

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 1 (eraseDigit 4 2 (eraseDigit 4 5 i))))

theorem packed_size : packed < (2 ^ 64) ^ 16384 := by
  exact stage4_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) sourcePacked := by
  dsimp only [packed, project]
  rw [stage4_lane, stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 679754836 := by
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
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table00 (e 13) (e 15) (e 16) + 516823704 := by
  rw [packed_lane, project_unionCode]
  exact source_binding_at e

#print axioms lane_binding
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource00

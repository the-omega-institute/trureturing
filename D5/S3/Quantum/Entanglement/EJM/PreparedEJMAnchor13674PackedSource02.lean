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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource02
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

def sourceCells : List Nat :=
  [1480867329, 593818327, 594801207, 594801207, 1654995716, 375145685, 21201606, 21201606, 896745204, 257781797, 133729695, 277102408, 896745204, 257781797, 277102408, 133729695, 593818327, 90554874, 476212990, 476212990, 1120379921, 0, 8297606, 8297606, 820063767, 250935338, 622624978, 386355564, 820063767, 250935338, 386355564, 622624978, 594801207, 476212990, 313242828, 654334287, 1172499554, 9233327, 291194850, 57799057, 814429809, 251985347, 393996552, 368192459, 523205244, 322282266, 281753648, 377048357, 594801207, 476212990, 654334287, 313242828, 1172499554, 9233327, 57799057, 291194850, 523205244, 322282266, 377048357, 281753648, 814429809, 251985347, 368192459, 393996552]

def sourcePacked : Nat := 0x177be9080000000015f22bcb000000000f04fdc300000000308b36710000000010cb38300000000016794d25000000001335a31a000000001f2f7a7c00000000115b47e2000000000371f19100000000008ce3af0000000045e2ec620000000012abb4cc000000002700594f000000001c626efe000000002373f2370000000016794d250000000010cb3830000000001335a31a000000001f2f7a7c0000000015f22bcb00000000177be908000000000f04fdc300000000308b3671000000000371f19100000000115b47e200000000008ce3af0000000045e2ec62000000002700594f0000000012abb4cc000000001c626efe000000002373f23700000000251c80d2000000001707516c000000000ef4f82a0000000030e12e17000000001707516c00000000251c80d2000000000ef4f82a0000000030e12e1700000000007e9c8600000000007e9c8600000000000000000000000042c7a411000000001c626efe000000001c626efe000000000565c1fa000000002364f2d70000000007f88d9f0000000010843f48000000000f5d70250000000035733ef40000000010843f480000000007f88d9f000000000f5d70250000000035733ef400000000014382c600000000014382c600000000165c44d50000000062a53b04000000002373f237000000002373f237000000002364f2d70000000058443e01

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 13).val) * 4 + (e 16).val) * 4 + (e 17).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 1654995716)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 1654995716 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 1654995716
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 1654995716
      sourceBoundChecked x hx).trans_lt (by decide : 1654995716 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x13 => all4 (fun x16 => all4 (fun x17 => decide (((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x16.val) * 4 + x17.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table02 x13 x16 x17 + 1480867329))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x13 x16 x17 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x16.val) * 4 + x17.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table02 x13 x16 x17 + 1480867329 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x16
  have h3 := all4_sound h2 x17
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table02 (e 13) (e 16) (e 17) + 1480867329 := by
  exact source_binding (e 13) (e 16) (e 17)

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

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 1 (eraseDigit 4 4 (eraseDigit 4 5 i))))

theorem packed_size : packed < (2 ^ 64) ^ 16384 := by
  exact stage4_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) sourcePacked := by
  dsimp only [packed, project]
  rw [stage4_lane, stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 1654995716 := by
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
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table02 (e 13) (e 16) (e 17) + 1480867329 := by
  rw [packed_lane, project_unionCode]
  exact source_binding_at e

#print axioms lane_binding
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource02

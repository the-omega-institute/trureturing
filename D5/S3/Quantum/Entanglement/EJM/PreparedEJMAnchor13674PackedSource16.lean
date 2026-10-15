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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource16
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

def sourceCells : List Nat :=
  [0, 666370643, 926638780, 926638780, 931348634, 1510920107, 1303279657, 1303279657, 871652634, 1205840866, 1417261761, 1275162953, 871652634, 1205840866, 1275162953, 1417261761, 574638568, 1441330610, 1567703469, 1567703469, 3267355055, 1657318373, 1496771412, 1496771412, 2268484389, 1699002631, 1976889069, 1724495164, 2268484389, 1699002631, 1724495164, 1976889069, 575621448, 1665001444, 1566720589, 1745824766, 2203154431, 1654602297, 1602613849, 1678215355, 3379170688, 1877107447, 1760210046, 1574389567, 1971625866, 1689215335, 1701027472, 1731312448, 575621448, 1665001444, 1745824766, 1566720589, 2203154431, 1654602297, 1678215355, 1602613849, 1971625866, 1689215335, 1731312448, 1701027472, 3379170688, 1877107447, 1574389567, 1760210046]

def sourcePacked : Nat := 0x68eaac7e000000005dd7473f000000006fe262f700000000c96a0d800000000065639e90000000006731bb400000000064af61670000000075849f8a000000005f85f25900000000640788bb00000000629f3a3900000000835177ff000000005d62424d00000000680f2bfe00000000633de7e400000000224f4948000000006731bb400000000065639e900000000064af61670000000075849f8a000000005dd7473f0000000068eaac7e000000006fe262f700000000c96a0d8000000000640788bb000000005f85f25900000000629f3a3900000000835177ff00000000680f2bfe000000005d62424d00000000633de7e400000000224f49480000000075d4eeed0000000066c9b53c000000006544b90700000000873653250000000066c9b53c0000000075d4eeed000000006544b9070000000087365325000000005936eb54000000005936eb540000000062c8abe500000000c2bfe1af000000005d7141ad000000005d7141ad0000000055e8f5b200000000224049e8000000005479b2c1000000004c0171490000000047dfabe20000000033f45d1a000000004c017149000000005479b2c10000000047dfabe20000000033f45d1a000000004dae7829000000004dae7829000000005a0ecfab000000003783409a00000000373b62bc00000000373b62bc0000000027b802530000000000000000

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 13).val) * 4 + (e 18).val) * 4 + (e 19).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 3379170688)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 3379170688 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 3379170688
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 3379170688
      sourceBoundChecked x hx).trans_lt (by decide : 3379170688 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x13 => all4 (fun x18 => all4 (fun x19 => decide (((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x18.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table16 x13 x18 x19 + 0))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x13 x18 x19 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x13.val) * 4 + x18.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table16 x13 x18 x19 + 0 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x13
  have h2 := all4_sound h1 x18
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table16 (e 13) (e 18) (e 19) + 0 := by
  exact source_binding (e 13) (e 18) (e 19)

def stage1 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 1) sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 1 2 sourcePacked
    source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 2 i) sourcePacked := by
  exact broadcastBits_lane_nat 64 1 2 sourcePacked
    source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 3) (4 ^ 1) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 1 3 stage1
    stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 3 i) stage1 := by
  exact broadcastBits_lane_nat 64 1 3 stage1
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

def project (i : Nat) : Nat := (eraseDigit 4 2 (eraseDigit 4 3 (eraseDigit 4 4 (eraseDigit 4 5 i))))

theorem packed_size : packed < (2 ^ 64) ^ 16384 := by
  exact stage4_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) sourcePacked := by
  dsimp only [packed, project]
  rw [stage4_lane, stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 3379170688 := by
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
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table16 (e 13) (e 18) (e 19) + 0 := by
  rw [packed_lane, project_unionCode]
  exact source_binding_at e

#print axioms lane_binding
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource16

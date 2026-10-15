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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource09
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [0, 1635815957, 877565445, 877565445, 574638568, 604587325, 238923119, 238923119, 575621448, 376768423, 207874697, 198317513, 575621448, 376768423, 198317513, 207874697, 666370643, 3795023969, 2042281039, 2042281039, 1441330610, 1385970180, 1410349902, 1410349902, 1665001444, 1034215874, 2071912990, 1414770201, 1665001444, 1034215874, 1414770201, 2071912990, 926638780, 2857723339, 3615973851, 2157675276, 1567703469, 2353780675, 1521949234, 1592717160, 1566720589, 1758529425, 2595196665, 1573396549, 1745824766, 1817641501, 1561740699, 1643127383, 926638780, 2857723339, 2157675276, 3615973851, 1567703469, 2353780675, 1592717160, 1521949234, 1745824766, 1817641501, 1643127383, 1561740699, 1566720589, 1758529425, 1573396549, 2595196665]

def sourcePacked : Nat := 0x9aaf8ef9000000005dc820450000000068d10791000000005d62424d000000005d16459b0000000061f02257000000006c57021d00000000680f2bfe000000005ab71a32000000005eeeef68000000008c4bd7c3000000005d7141ad00000000d78761db00000000809b830c00000000aa5565cb00000000373b62bc0000000061f02257000000005d16459b000000006c57021d00000000680f2bfe000000005dc82045000000009aaf8ef90000000068d10791000000005d62424d000000005eeeef68000000005ab71a32000000008c4bd7c3000000005d7141ad00000000809b830c00000000d78761db00000000aa5565cb00000000373b62bc000000007b7ee21e000000005453ae19000000003da4e1c200000000633de7e4000000005453ae19000000007b7ee21e000000003da4e1c200000000633de7e40000000054103b4e0000000054103b4e00000000529c3a040000000055e8f5b20000000079babc4f0000000079babc4f00000000e23378610000000027b80253000000000c63ea89000000000bd215c900000000167507a700000000224f4948000000000bd215c9000000000c63ea8900000000167507a700000000224f4948000000000e3dad6f000000000e3dad6f000000002409453d00000000224049e800000000344e960500000000344e960500000000618092150000000000000000

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 15).val) * 4 + (e 17).val) * 4 + (e 18).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 3795023969)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 3795023969 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 3795023969
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 3795023969
      sourceBoundChecked x hx).trans_lt (by decide : 3795023969 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x15 => all4 (fun x17 => all4 (fun x18 => decide (((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x17.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table09 x15 x17 x18 + 0))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x15 x17 x18 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x15.val) * 4 + x17.val) * 4 + x18.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table09 x15 x17 x18 + 0 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x15
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x18
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + 0 := by
  exact source_binding (e 15) (e 17) (e 18)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource09

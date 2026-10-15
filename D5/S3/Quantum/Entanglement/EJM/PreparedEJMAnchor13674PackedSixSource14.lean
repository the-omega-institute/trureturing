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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource14
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [516823704, 503567809, 618746793, 618746793, 592710508, 631817407, 565681589, 565681589, 591726680, 679754836, 600782784, 587276291, 591726680, 679754836, 587276291, 600782784, 189368604, 163499019, 148387066, 148387066, 246118164, 321789540, 182734091, 182734091, 150697974, 186064941, 77007960, 0, 150697974, 186064941, 0, 77007960, 195795119, 215357859, 148387066, 182261621, 129476937, 72087799, 237806507, 111560358, 150697974, 166633363, 102786909, 328024465, 204659917, 65329406, 182481790, 317204894, 195795119, 215357859, 182261621, 148387066, 129476937, 72087799, 111560358, 237806507, 204659917, 65329406, 317204894, 182481790, 150697974, 166633363, 328024465, 102786909]

def sourcePacked : Nat := 0x620675d00000000138d41910000000009ee9f930000000008fb77f6000000000ae0737e0000000012e8299e0000000003e4d8fe000000000c32dccd000000000e2ca3ab0000000006a646a600000000044bf8f70000000007b7a9490000000008d834fa000000000add1775000000000cd619a3000000000bab98af0000000012e8299e000000000ae0737e0000000003e4d8fe000000000c32dccd00000000138d4191000000000620675d0000000009ee9f930000000008fb77f60000000006a646a6000000000e2ca3ab00000000044bf8f70000000007b7a949000000000add17750000000008d834fa000000000cd619a3000000000bab98af0000000004970c580000000000000000000000000b17202d0000000008fb77f600000000000000000000000004970c58000000000b17202d0000000008fb77f6000000000ae44d0b000000000ae44d0b00000000132e1e64000000000eab77140000000008d834fa0000000008d834fa0000000009becc0b000000000b49891c0000000023cf37c000000000230120030000000028843c54000000002345085800000000230120030000000023cf37c00000000028843c5400000000234508580000000021b79db50000000021b79db50000000025a8c4bf0000000023540b6c0000000024e153a90000000024e153a9000000001e03d5c1000000001ece1a98

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 14).val) * 4 + (e 17).val) * 4 + (e 19).val)

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
  all4 (fun x14 => all4 (fun x17 => all4 (fun x19 => decide (((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table14 x14 x17 x19 + 516823704))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x14 x17 x19 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table14 x14 x17 x19 + 516823704 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + 516823704 := by
  exact source_binding (e 14) (e 17) (e 19)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource14

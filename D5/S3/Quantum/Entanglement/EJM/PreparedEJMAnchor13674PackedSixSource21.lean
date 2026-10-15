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

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource21
open EJMPackedBroadcastPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (all4 all4_sound Assignment)
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon (all_le_mem packed_source_lane_le)

def sourceCells : List Nat :=
  [7146695762, 7243794010, 8389439102, 8389439102, 7060318668, 7047444536, 7425168720, 7425168720, 7062282532, 6951855476, 7109562752, 7158157076, 7062282532, 6951855476, 7158157076, 7109562752, 7286530788, 7963618789, 9713483295, 9713483295, 7827286912, 8062049604, 8728207187, 8728207187, 7736328721, 8093943390, 8261637329, 8220696524, 7736328721, 8093943390, 8220696524, 8261637329, 7117199666, 8082857753, 9719909810, 9491052950, 7604255691, 7815057759, 9068452705, 8715602928, 7667378784, 7828383488, 8164967181, 8102198756, 7606990326, 7720419845, 8469816625, 7727342704, 7117199666, 8082857753, 9491052950, 9719909810, 7604255691, 7815057759, 8715602928, 9068452705, 7606990326, 7720419845, 7727342704, 8469816625, 7667378784, 7828383488, 8102198756, 8164967181]

def sourcePacked : Nat := 0x1e6ab830d00000001e2edbde400000001d29ba70000000001c902ea6000000001f8d7253100000001cc95e47000000001cc2c420500000001c56975f6000000021c859b6100000002077d8bf000000001d1d0515f00000001c53fbbcb00000002435a0db20000000235b5f99600000001e1c69f1900000001a837d93200000001cc95e47000000001f8d7253100000001cc2c420500000001c56975f600000001e2edbde400000001e6ab830d00000001d29ba70000000001c902ea6000000002077d8bf0000000021c859b6100000001d1d0515f00000001c53fbbcb0000000235b5f99600000002435a0db200000001e1c69f1900000001a837d93200000001ec6e94d100000001e9fddfcc00000001e26fc65e00000001cd1f021100000001e9fddfcc00000001ec6e94d100000001e26fc65e00000001cd1f021100000002083ddf5300000002083ddf5300000001e0891d4400000001d28aeb800000000242f7fe1f0000000242f7fe1f00000001daab2de500000001b24fa2e400000001a7c3518000000001aaa8cf14000000019e5ce57400000001a4f1e12400000001aaa8cf1400000001a7c35180000000019e5ce57400000001a4f1e12400000001ba93155000000001ba93155000000001a40f783800000001a4d3e9cc00000001f40cae7e00000001f40cae7e00000001afc3865a00000001a9f9ec52

def sourceCode (e : Assignment) : Nat := (((0 * 4 + (e 14).val) * 4 + (e 17).val) * 4 + (e 19).val)

set_option trace.profiler true in
theorem source_pack : sourcePacked = pack 64 sourceCells := by
  decide +kernel

theorem source_length : sourceCells.length = 64 := by
  decide +kernel

private theorem sourceBoundChecked :
    sourceCells.all (fun x => decide (x ≤ 9719909810)) = true := by
  decide +kernel

theorem source_lane_le (i : Nat) :
    digit (2 ^ 64) i sourcePacked ≤ 9719909810 := by
  rw [source_pack]
  exact packed_source_lane_le sourceCells 9719909810
    (by decide) sourceBoundChecked i

theorem source_size :
    sourcePacked < (2 ^ 64) ^ (4 ^ 3) := by
  rw [source_pack]
  unfold pack
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2 ^ 64)
    (fun x hx => (all_le_mem sourceCells 9719909810
      sourceBoundChecked x hx).trans_lt (by decide : 9719909810 < 2 ^ 64))
  simpa only [source_length] using h

private def source_bindingCheck : Bool :=
  all4 (fun x14 => all4 (fun x17 => all4 (fun x19 => decide (((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table21 x14 x17 x19 + 7146695762))))

set_option trace.profiler true in
private theorem source_bindingChecked : source_bindingCheck = true := by
  decide +kernel

theorem source_binding (x14 x17 x19 : Fin 4) :
    ((digit (2 ^ 64) (((0 * 4 + x14.val) * 4 + x17.val) * 4 + x19.val) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table21 x14 x17 x19 + 7146695762 := by
  have h0 := source_bindingChecked
  unfold source_bindingCheck at h0
  have h1 := all4_sound h0 x14
  have h2 := all4_sound h1 x17
  have h3 := all4_sound h2 x19
  exact of_decide_eq_true h3

theorem source_binding_at (e : Assignment) :
    ((digit (2 ^ 64) (sourceCode e) sourcePacked : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19) + 7146695762 := by
  exact source_binding (e 14) (e 17) (e 19)

#print axioms source_binding_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource21

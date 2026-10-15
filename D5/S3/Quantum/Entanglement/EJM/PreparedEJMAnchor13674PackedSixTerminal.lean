/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource23

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixTerminal
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def xLane (_ : Fin 4) : Nat := 7966241707
def yLane (i : Fin 4) : Nat := digit (2 ^ 64) i.val PreparedEJMAnchor13674PackedSixSource23.sourcePacked + 21271424

def xPacked : Nat := pack 64 (List.replicate 4 7966241707)
def constantPacked : Nat := pack 64 (List.replicate 4 21271424)
def yPacked : Nat := PreparedEJMAnchor13674PackedSixSource23.sourcePacked + constantPacked
def guardMask : Nat := mask 64 4

theorem x_pack : pack 64 (List.ofFn xLane) = xPacked := by
  rfl

theorem y_pack : pack 64 (List.ofFn yLane) = yPacked := by
  dsimp only [yLane, yPacked]
  rw [pack_ofFn_add]
  rw [pack_ofFn_digit 64 4 PreparedEJMAnchor13674PackedSixSource23.sourcePacked PreparedEJMAnchor13674PackedSixSource23.source_size]
  rfl

theorem x_range (i : Fin 4) : xLane i < 2 ^ (64 - 1) := by
  decide +kernel

theorem y_range (i : Fin 4) : yLane i < 2 ^ (64 - 1) := by
  have h := PreparedEJMAnchor13674PackedSixSource23.source_lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 4) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem lower_at (e : Assignment) :
    (21226312 : ℤ) ≤ 21271424 + PreparedEJMAnchor13674PackedSixTables.table23 (e 19) := by
  have h : (xLane (e 19) : ℤ) ≤ (yLane (e 19) : ℤ) := by
    exact_mod_cast pointwise_nat (e 19)
  have hb := PreparedEJMAnchor13674PackedSixSource23.source_binding_at e
  change ((digit (2 ^ 64) (e 19).val PreparedEJMAnchor13674PackedSixSource23.sourcePacked : Nat) : ℤ) =
    PreparedEJMAnchor13674PackedSixTables.table23 (e 19) + 7945015395 at hb
  dsimp only [xLane, yLane] at h
  push_cast at h
  rw [hb] at h
  linarith only [h]

#print axioms lower_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixTerminal

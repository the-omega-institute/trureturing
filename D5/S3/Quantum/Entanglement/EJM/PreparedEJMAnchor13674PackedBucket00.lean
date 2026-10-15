/- Prepared, uncompiled source; no kernel acceptance is asserted.
Actual prefix depth13/code4/index674, first bucket only.
Source cells are scope-sized. Broadcasts are structural proofs.
No native-expanded 16384-by-8 source binding is used. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource00
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource02
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource04
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource05
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource08
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource11
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource15
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSource16
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedBucket00
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon

def xLane (i : Fin 16384) : Nat := digit (2 ^ 64) i.val PreparedEJMAnchor13674PackedOutput.packed
def yLane (i : Fin 16384) : Nat := digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource00.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource02.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource04.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource05.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource08.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource11.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource15.packed) + digit (2 ^ 64) i.val (PreparedEJMAnchor13674PackedSource16.packed)

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := PreparedEJMAnchor13674PackedOutput.packed
def yPacked : Nat := PreparedEJMAnchor13674PackedSource00.packed + PreparedEJMAnchor13674PackedSource02.packed + PreparedEJMAnchor13674PackedSource04.packed + PreparedEJMAnchor13674PackedSource05.packed + PreparedEJMAnchor13674PackedSource08.packed + PreparedEJMAnchor13674PackedSource11.packed + PreparedEJMAnchor13674PackedSource15.packed + PreparedEJMAnchor13674PackedSource16.packed
def guardMask : Nat := mask 64 16384

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 16384 xPacked PreparedEJMAnchor13674PackedOutput.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource00.packed PreparedEJMAnchor13674PackedSource00.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource02.packed PreparedEJMAnchor13674PackedSource02.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource04.packed PreparedEJMAnchor13674PackedSource04.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource05.packed PreparedEJMAnchor13674PackedSource05.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource08.packed PreparedEJMAnchor13674PackedSource08.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource11.packed PreparedEJMAnchor13674PackedSource11.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource15.packed PreparedEJMAnchor13674PackedSource15.packed_size, pack_ofFn_digit 64 16384 PreparedEJMAnchor13674PackedSource16.packed PreparedEJMAnchor13674PackedSource16.packed_size]

theorem x_range (i : Fin 16384) : xLane i < 2 ^ (64 - 1) := by
  exact (PreparedEJMAnchor13674PackedOutput.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 16384) : yLane i < 2 ^ (64 - 1) := by
  have h0 := PreparedEJMAnchor13674PackedSource00.lane_le i.val
  have h1 := PreparedEJMAnchor13674PackedSource02.lane_le i.val
  have h2 := PreparedEJMAnchor13674PackedSource04.lane_le i.val
  have h3 := PreparedEJMAnchor13674PackedSource05.lane_le i.val
  have h4 := PreparedEJMAnchor13674PackedSource08.lane_le i.val
  have h5 := PreparedEJMAnchor13674PackedSource11.lane_le i.val
  have h6 := PreparedEJMAnchor13674PackedSource15.lane_le i.val
  have h7 := PreparedEJMAnchor13674PackedSource16.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 16384) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 16384 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 16384) = mask 64 16384
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedOutput.outputTable (e 14) (e 15) (e 16) (e 17) (e 18) (e 19) ≤
      TransientEJMAnchor13674VEGroups.table00 (e 13) (e 15) (e 16) + TransientEJMAnchor13674VEGroups.table02 (e 13) (e 16) (e 17) + TransientEJMAnchor13674VEGroups.table04 (e 13) (e 15) (e 18) + TransientEJMAnchor13674VEGroups.table05 (e 13) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table08 (e 13) (e 14) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table11 (e 13) (e 14) (e 16) (e 19) + TransientEJMAnchor13674VEGroups.table15 (e 13) (e 15) (e 17) (e 19) + TransientEJMAnchor13674VEGroups.table16 (e 13) (e 18) (e 19) := by
  let i : Fin 16384 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [PreparedEJMAnchor13674PackedSource00.lane_binding e, PreparedEJMAnchor13674PackedSource02.lane_binding e, PreparedEJMAnchor13674PackedSource04.lane_binding e, PreparedEJMAnchor13674PackedSource05.lane_binding e, PreparedEJMAnchor13674PackedSource08.lane_binding e, PreparedEJMAnchor13674PackedSource11.lane_binding e, PreparedEJMAnchor13674PackedSource15.lane_binding e, PreparedEJMAnchor13674PackedSource16.lane_binding e, PreparedEJMAnchor13674PackedOutput.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedBucket00

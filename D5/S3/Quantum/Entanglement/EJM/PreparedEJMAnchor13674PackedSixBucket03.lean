/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource20
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource21

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket03
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def unionCode (e : Assignment) : Nat := ((((0 * 4 + (e 14).val) * 4 + (e 17).val) * 4 + (e 18).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 256 := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

namespace Input20

def packed : Nat := PreparedEJMAnchor13674PackedSixSource20.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 256 := by
  exact PreparedEJMAnchor13674PackedSixSource20.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource20.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 11511802936 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource20.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource20.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource20.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table20 (e 14) (e 17) (e 18) (e 19) + 7146695762 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource20.source_binding_at e

end Input20

namespace Output

def stage1 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 2) PreparedEJMAnchor13674PackedSixSource21.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 2 1 PreparedEJMAnchor13674PackedSixSource21.sourcePacked PreparedEJMAnchor13674PackedSixSource21.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 1 i) PreparedEJMAnchor13674PackedSixSource21.sourcePacked := by
  exact broadcastBits_lane_nat 64 2 1 PreparedEJMAnchor13674PackedSixSource21.sourcePacked PreparedEJMAnchor13674PackedSixSource21.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 1 i)

theorem packed_size : packed < (2 ^ 64) ^ 256 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource21.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9719909810 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource21.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource21.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource21.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19) + 7146695762 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource21.source_binding_at e

end Output

def xLane (i : Fin 256) : Nat := digit (2 ^ 64) i.val Output.packed
def yLane (i : Fin 256) : Nat := digit (2 ^ 64) i.val Input20.packed

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := Output.packed
def yPacked : Nat := Input20.packed
def guardMask : Nat := mask 64 256

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 256 xPacked Output.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 256 Input20.packed Input20.packed_size]

theorem x_range (i : Fin 256) : xLane i < 2 ^ (64 - 1) := by
  exact (Output.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 256) : yLane i < 2 ^ (64 - 1) := by
  have h0 := Input20.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 256) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 256 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 256) = mask 64 256
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19) ≤ PreparedEJMAnchor13674PackedSixTables.table20 (e 14) (e 17) (e 18) (e 19) := by
  let i : Fin 256 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [Input20.lane_binding e, Output.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket03

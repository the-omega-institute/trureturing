/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource13
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource22
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource23

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket05
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def unionCode (e : Assignment) : Nat := ((0 * 4 + (e 17).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 16 := by
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

namespace Input13

def packed : Nat := PreparedEJMAnchor13674PackedSixSource13.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 16 := by
  exact PreparedEJMAnchor13674PackedSixSource13.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource13.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 176187027 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource13.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource13.sourceCode e := by
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource13.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + 13255895 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource13.source_binding_at e

end Input13

namespace Input22

def packed : Nat := PreparedEJMAnchor13674PackedSixSource22.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 16 := by
  exact PreparedEJMAnchor13674PackedSixSource22.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource22.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9211035283 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource22.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource22.sourceCode e := by
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource22.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19) + 7931759500 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource22.source_binding_at e

end Input22

namespace Output

def stage1 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 0) PreparedEJMAnchor13674PackedSixSource23.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 2) := by
  exact broadcastBits_lt_nat 64 0 1 PreparedEJMAnchor13674PackedSixSource23.sourcePacked PreparedEJMAnchor13674PackedSixSource23.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 1 i) PreparedEJMAnchor13674PackedSixSource23.sourcePacked := by
  exact broadcastBits_lane_nat 64 0 1 PreparedEJMAnchor13674PackedSixSource23.sourcePacked PreparedEJMAnchor13674PackedSixSource23.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 1 i)

theorem packed_size : packed < (2 ^ 64) ^ 16 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource23.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 7945019253 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource23.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource23.sourceCode e := by
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource23.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table23 (e 19) + 7945015395 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource23.source_binding_at e

end Output

def xLane (i : Fin 16) : Nat := digit (2 ^ 64) i.val Output.packed
def yLane (i : Fin 16) : Nat := digit (2 ^ 64) i.val Input13.packed + digit (2 ^ 64) i.val Input22.packed

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := Output.packed
def yPacked : Nat := Input13.packed + Input22.packed
def guardMask : Nat := mask 64 16

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 16 xPacked Output.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 16 Input13.packed Input13.packed_size, pack_ofFn_digit 64 16 Input22.packed Input22.packed_size]

theorem x_range (i : Fin 16) : xLane i < 2 ^ (64 - 1) := by
  exact (Output.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 16) : yLane i < 2 ^ (64 - 1) := by
  have h0 := Input13.lane_le i.val
  have h1 := Input22.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 16) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 16 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 16) = mask 64 16
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedSixTables.table23 (e 19) ≤ TransientEJMAnchor13674VEGroups.table13 (e 17) (e 19) + PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19) := by
  let i : Fin 16 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [Input13.lane_binding e, Input22.lane_binding e, Output.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket05

/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource09
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource17
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource19
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource20

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket02
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def unionCode (e : Assignment) : Nat := (((((0 * 4 + (e 14).val) * 4 + (e 15).val) * 4 + (e 17).val) * 4 + (e 18).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 1024 := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

namespace Input09

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 3) PreparedEJMAnchor13674PackedSixSource09.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource09.sourcePacked PreparedEJMAnchor13674PackedSixSource09.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) PreparedEJMAnchor13674PackedSixSource09.sourcePacked := by
  exact broadcastBits_lane_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource09.sourcePacked PreparedEJMAnchor13674PackedSixSource09.source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 4) (4 ^ 0) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 0 4 stage1 stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 4 i) stage1 := by
  exact broadcastBits_lane_nat 64 0 4 stage1 stage1_size i

def packed : Nat := stage2

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 4 i))

theorem packed_size : packed < (2 ^ 64) ^ 1024 := by
  exact stage2_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource09.sourcePacked := by
  dsimp only [packed, project]
  rw [stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 3795023969 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource09.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource09.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource09.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + 0 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource09.source_binding_at e

end Input09

namespace Input17

def stage1 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 2) PreparedEJMAnchor13674PackedSixSource17.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 2 2 PreparedEJMAnchor13674PackedSixSource17.sourcePacked PreparedEJMAnchor13674PackedSixSource17.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 2 i) PreparedEJMAnchor13674PackedSixSource17.sourcePacked := by
  exact broadcastBits_lane_nat 64 2 2 PreparedEJMAnchor13674PackedSixSource17.sourcePacked PreparedEJMAnchor13674PackedSixSource17.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 2 i)

theorem packed_size : packed < (2 ^ 64) ^ 1024 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource17.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 1296911592 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource17.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource17.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource17.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table17 (e 14) (e 15) (e 18) (e 19) + 1296911592 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource17.source_binding_at e

end Input17

namespace Input19

def packed : Nat := PreparedEJMAnchor13674PackedSixSource19.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 1024 := by
  exact PreparedEJMAnchor13674PackedSixSource19.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource19.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9504383372 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource19.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource19.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource19.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table19 (e 14) (e 15) (e 17) (e 18) (e 19) + 5849784170 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource19.source_binding_at e

end Input19

namespace Output

def stage1 : Nat := broadcastBits (64 * 4 ^ 3) (4 ^ 1) PreparedEJMAnchor13674PackedSixSource20.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 1 3 PreparedEJMAnchor13674PackedSixSource20.sourcePacked PreparedEJMAnchor13674PackedSixSource20.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 3 i) PreparedEJMAnchor13674PackedSixSource20.sourcePacked := by
  exact broadcastBits_lane_nat 64 1 3 PreparedEJMAnchor13674PackedSixSource20.sourcePacked PreparedEJMAnchor13674PackedSixSource20.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 3 i)

theorem packed_size : packed < (2 ^ 64) ^ 1024 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource20.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 11511802936 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource20.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource20.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource20.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table20 (e 14) (e 17) (e 18) (e 19) + 7146695762 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource20.source_binding_at e

end Output

def xLane (i : Fin 1024) : Nat := digit (2 ^ 64) i.val Output.packed
def yLane (i : Fin 1024) : Nat := digit (2 ^ 64) i.val Input09.packed + digit (2 ^ 64) i.val Input17.packed + digit (2 ^ 64) i.val Input19.packed

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := Output.packed
def yPacked : Nat := Input09.packed + Input17.packed + Input19.packed
def guardMask : Nat := mask 64 1024

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 1024 xPacked Output.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 1024 Input09.packed Input09.packed_size, pack_ofFn_digit 64 1024 Input17.packed Input17.packed_size, pack_ofFn_digit 64 1024 Input19.packed Input19.packed_size]

theorem x_range (i : Fin 1024) : xLane i < 2 ^ (64 - 1) := by
  exact (Output.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 1024) : yLane i < 2 ^ (64 - 1) := by
  have h0 := Input09.lane_le i.val
  have h1 := Input17.lane_le i.val
  have h2 := Input19.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 1024) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 1024 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 1024) = mask 64 1024
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedSixTables.table20 (e 14) (e 17) (e 18) (e 19) ≤ TransientEJMAnchor13674VEGroups.table09 (e 15) (e 17) (e 18) + TransientEJMAnchor13674VEGroups.table17 (e 14) (e 15) (e 18) (e 19) + PreparedEJMAnchor13674PackedSixTables.table19 (e 14) (e 15) (e 17) (e 18) (e 19) := by
  let i : Fin 1024 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [Input09.lane_binding e, Input17.lane_binding e, Input19.lane_binding e, Output.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket02

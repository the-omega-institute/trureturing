/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedOutput
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource03
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource06
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource07
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource12
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource19

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket01
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def unionCode (e : Assignment) : Nat := ((((((0 * 4 + (e 14).val) * 4 + (e 15).val) * 4 + (e 16).val) * 4 + (e 17).val) * 4 + (e 18).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 4096 := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

namespace Input03

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 4) PreparedEJMAnchor13674PackedSixSource03.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 4 0 PreparedEJMAnchor13674PackedSixSource03.sourcePacked PreparedEJMAnchor13674PackedSixSource03.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) PreparedEJMAnchor13674PackedSixSource03.sourcePacked := by
  exact broadcastBits_lane_nat 64 4 0 PreparedEJMAnchor13674PackedSixSource03.sourcePacked PreparedEJMAnchor13674PackedSixSource03.source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 4) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 4 1 stage1 stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 1 i) stage1 := by
  exact broadcastBits_lane_nat 64 4 1 stage1 stage1_size i

def packed : Nat := stage2

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 1 i))

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact stage2_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource03.sourcePacked := by
  dsimp only [packed, project]
  rw [stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 3795023969 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource03.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource03.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource03.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table03 (e 14) (e 15) (e 16) (e 17) + 0 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource03.source_binding_at e

end Input03

namespace Input06

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 3) PreparedEJMAnchor13674PackedSixSource06.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource06.sourcePacked PreparedEJMAnchor13674PackedSixSource06.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) PreparedEJMAnchor13674PackedSixSource06.sourcePacked := by
  exact broadcastBits_lane_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource06.sourcePacked PreparedEJMAnchor13674PackedSixSource06.source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 2) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 2 2 stage1 stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 2 i) stage1 := by
  exact broadcastBits_lane_nat 64 2 2 stage1 stage1_size i

def stage3 : Nat := broadcastBits (64 * 4 ^ 4) (4 ^ 1) stage2

theorem stage3_size : stage3 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 1 4 stage2 stage2_size

theorem stage3_lane (i : Nat) :
    digit (2 ^ 64) i stage3 = digit (2 ^ 64) (eraseDigit 4 4 i) stage2 := by
  exact broadcastBits_lane_nat 64 1 4 stage2 stage2_size i

def packed : Nat := stage3

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 2 (eraseDigit 4 4 i)))

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact stage3_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource06.sourcePacked := by
  dsimp only [packed, project]
  rw [stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 1069123165 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource06.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource06.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource06.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table06 (e 14) (e 16) (e 18) + 0 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource06.source_binding_at e

end Input06

namespace Input07

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 3) PreparedEJMAnchor13674PackedSixSource07.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource07.sourcePacked PreparedEJMAnchor13674PackedSixSource07.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) PreparedEJMAnchor13674PackedSixSource07.sourcePacked := by
  exact broadcastBits_lane_nat 64 3 0 PreparedEJMAnchor13674PackedSixSource07.sourcePacked PreparedEJMAnchor13674PackedSixSource07.source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 2) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 2 2 stage1 stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 2 i) stage1 := by
  exact broadcastBits_lane_nat 64 2 2 stage1 stage1_size i

def stage3 : Nat := broadcastBits (64 * 4 ^ 5) (4 ^ 0) stage2

theorem stage3_size : stage3 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 0 5 stage2 stage2_size

theorem stage3_lane (i : Nat) :
    digit (2 ^ 64) i stage3 = digit (2 ^ 64) (eraseDigit 4 5 i) stage2 := by
  exact broadcastBits_lane_nat 64 0 5 stage2 stage2_size i

def packed : Nat := stage3

def project (i : Nat) : Nat := (eraseDigit 4 0 (eraseDigit 4 2 (eraseDigit 4 5 i)))

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact stage3_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource07.sourcePacked := by
  dsimp only [packed, project]
  rw [stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 599981792 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource07.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource07.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource07.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table07 (e 15) (e 16) (e 18) + 213309461 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource07.source_binding_at e

end Input07

namespace Input12

def stage1 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 2) PreparedEJMAnchor13674PackedSixSource12.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 4) := by
  exact broadcastBits_lt_nat 64 2 1 PreparedEJMAnchor13674PackedSixSource12.sourcePacked PreparedEJMAnchor13674PackedSixSource12.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 1 i) PreparedEJMAnchor13674PackedSixSource12.sourcePacked := by
  exact broadcastBits_lane_nat 64 2 1 PreparedEJMAnchor13674PackedSixSource12.sourcePacked PreparedEJMAnchor13674PackedSixSource12.source_size i

def stage2 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 2) stage1

theorem stage2_size : stage2 < (2 ^ 64) ^ (4 ^ 5) := by
  exact broadcastBits_lt_nat 64 2 2 stage1 stage1_size

theorem stage2_lane (i : Nat) :
    digit (2 ^ 64) i stage2 = digit (2 ^ 64) (eraseDigit 4 2 i) stage1 := by
  exact broadcastBits_lane_nat 64 2 2 stage1 stage1_size i

def stage3 : Nat := broadcastBits (64 * 4 ^ 5) (4 ^ 0) stage2

theorem stage3_size : stage3 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 0 5 stage2 stage2_size

theorem stage3_lane (i : Nat) :
    digit (2 ^ 64) i stage3 = digit (2 ^ 64) (eraseDigit 4 5 i) stage2 := by
  exact broadcastBits_lane_nat 64 0 5 stage2 stage2_size i

def packed : Nat := stage3

def project (i : Nat) : Nat := (eraseDigit 4 1 (eraseDigit 4 2 (eraseDigit 4 5 i)))

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact stage3_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource12.sourcePacked := by
  dsimp only [packed, project]
  rw [stage3_lane, stage2_lane, stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 1296911592 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource12.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource12.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource12.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table12 (e 15) (e 16) (e 19) + 1296911592 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource12.source_binding_at e

end Input12

namespace Input18

def packed : Nat := PreparedEJMAnchor13674PackedOutput.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact PreparedEJMAnchor13674PackedOutput.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedOutput.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 7431545553 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedOutput.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedOutput.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedOutput.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedOutput.outputTable (e 14) (e 15) (e 16) (e 17) (e 18) (e 19) + 4339563117 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedOutput.source_binding_at e

end Input18

namespace Output

def stage1 : Nat := broadcastBits (64 * 4 ^ 3) (4 ^ 2) PreparedEJMAnchor13674PackedSixSource19.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 6) := by
  exact broadcastBits_lt_nat 64 2 3 PreparedEJMAnchor13674PackedSixSource19.sourcePacked PreparedEJMAnchor13674PackedSixSource19.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 3 i) PreparedEJMAnchor13674PackedSixSource19.sourcePacked := by
  exact broadcastBits_lane_nat 64 2 3 PreparedEJMAnchor13674PackedSixSource19.sourcePacked PreparedEJMAnchor13674PackedSixSource19.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 3 i)

theorem packed_size : packed < (2 ^ 64) ^ 4096 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource19.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9504383372 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource19.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource19.sourceCode e := by
  have h14 := (e 14).isLt
  have h15 := (e 15).isLt
  have h16 := (e 16).isLt
  have h17 := (e 17).isLt
  have h18 := (e 18).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource19.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table19 (e 14) (e 15) (e 17) (e 18) (e 19) + 5849784170 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource19.source_binding_at e

end Output

def xLane (i : Fin 4096) : Nat := digit (2 ^ 64) i.val Output.packed
def yLane (i : Fin 4096) : Nat := digit (2 ^ 64) i.val Input03.packed + digit (2 ^ 64) i.val Input06.packed + digit (2 ^ 64) i.val Input07.packed + digit (2 ^ 64) i.val Input12.packed + digit (2 ^ 64) i.val Input18.packed

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := Output.packed
def yPacked : Nat := Input03.packed + Input06.packed + Input07.packed + Input12.packed + Input18.packed
def guardMask : Nat := mask 64 4096

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 4096 xPacked Output.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 4096 Input03.packed Input03.packed_size, pack_ofFn_digit 64 4096 Input06.packed Input06.packed_size, pack_ofFn_digit 64 4096 Input07.packed Input07.packed_size, pack_ofFn_digit 64 4096 Input12.packed Input12.packed_size, pack_ofFn_digit 64 4096 Input18.packed Input18.packed_size]

theorem x_range (i : Fin 4096) : xLane i < 2 ^ (64 - 1) := by
  exact (Output.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 4096) : yLane i < 2 ^ (64 - 1) := by
  have h0 := Input03.lane_le i.val
  have h1 := Input06.lane_le i.val
  have h2 := Input07.lane_le i.val
  have h3 := Input12.lane_le i.val
  have h4 := Input18.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 4096) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 4096 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 4096) = mask 64 4096
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedSixTables.table19 (e 14) (e 15) (e 17) (e 18) (e 19) ≤ TransientEJMAnchor13674VEGroups.table03 (e 14) (e 15) (e 16) (e 17) + TransientEJMAnchor13674VEGroups.table06 (e 14) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table07 (e 15) (e 16) (e 18) + TransientEJMAnchor13674VEGroups.table12 (e 15) (e 16) (e 19) + PreparedEJMAnchor13674PackedOutput.outputTable (e 14) (e 15) (e 16) (e 17) (e 18) (e 19) := by
  let i : Fin 4096 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [Input03.lane_binding e, Input06.lane_binding e, Input07.lane_binding e, Input12.lane_binding e, Input18.lane_binding e, Output.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket01

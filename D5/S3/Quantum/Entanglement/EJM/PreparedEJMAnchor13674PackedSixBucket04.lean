/- Prepared, uncompiled; no kernel acceptance is asserted.
Actual depth13/code4/index674 only. Source-sized cell bindings and
structural broadcasts preserve all original 20 coordinates, four
values, Int offsets and scale 6987435. No native source premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedCommon
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource01
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource10
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource14
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource21
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixSource22

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket04
open EJMPackedBroadcastPrepared
open EJMPackedBroadcastFixedPrepared
open PackedConsumerHelpersPrepared
open D5.S0.Certificates.FinitePackedLaneGuard
open D5.S3.Quantum.Entanglement.EJM.TransientEJMAnchor13674VECommon (Assignment)

def unionCode (e : Assignment) : Nat := (((0 * 4 + (e 14).val) * 4 + (e 17).val) * 4 + (e 19).val)

theorem unionCode_lt (e : Assignment) : unionCode e < 64 := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [unionCode]
  omega

namespace Input01

def stage1 : Nat := broadcastBits (64 * 4 ^ 0) (4 ^ 2) PreparedEJMAnchor13674PackedSixSource01.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 3) := by
  exact broadcastBits_lt_nat 64 2 0 PreparedEJMAnchor13674PackedSixSource01.sourcePacked PreparedEJMAnchor13674PackedSixSource01.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 0 i) PreparedEJMAnchor13674PackedSixSource01.sourcePacked := by
  exact broadcastBits_lane_nat 64 2 0 PreparedEJMAnchor13674PackedSixSource01.sourcePacked PreparedEJMAnchor13674PackedSixSource01.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 0 i)

theorem packed_size : packed < (2 ^ 64) ^ 64 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource01.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 327455100 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource01.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource01.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource01.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + 134120017 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource01.source_binding_at e

end Input01

namespace Input10

def stage1 : Nat := broadcastBits (64 * 4 ^ 1) (4 ^ 1) PreparedEJMAnchor13674PackedSixSource10.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 3) := by
  exact broadcastBits_lt_nat 64 1 1 PreparedEJMAnchor13674PackedSixSource10.sourcePacked PreparedEJMAnchor13674PackedSixSource10.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 1 i) PreparedEJMAnchor13674PackedSixSource10.sourcePacked := by
  exact broadcastBits_lane_nat 64 1 1 PreparedEJMAnchor13674PackedSixSource10.sourcePacked PreparedEJMAnchor13674PackedSixSource10.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 1 i)

theorem packed_size : packed < (2 ^ 64) ^ 64 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource10.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 327455100 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource10.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource10.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource10.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + 134120017 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource10.source_binding_at e

end Input10

namespace Input14

def packed : Nat := PreparedEJMAnchor13674PackedSixSource14.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 64 := by
  exact PreparedEJMAnchor13674PackedSixSource14.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource14.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 679754836 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource14.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource14.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource14.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + 516823704 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource14.source_binding_at e

end Input14

namespace Input21

def packed : Nat := PreparedEJMAnchor13674PackedSixSource21.sourcePacked

def project (i : Nat) : Nat := i

theorem packed_size : packed < (2 ^ 64) ^ 64 := by
  exact PreparedEJMAnchor13674PackedSixSource21.source_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource21.sourcePacked := by
  dsimp only [packed, project]
  rfl

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9719909810 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource21.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource21.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource21.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19) + 7146695762 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource21.source_binding_at e

end Input21

namespace Output

def stage1 : Nat := broadcastBits (64 * 4 ^ 2) (4 ^ 0) PreparedEJMAnchor13674PackedSixSource22.sourcePacked

theorem stage1_size : stage1 < (2 ^ 64) ^ (4 ^ 3) := by
  exact broadcastBits_lt_nat 64 0 2 PreparedEJMAnchor13674PackedSixSource22.sourcePacked PreparedEJMAnchor13674PackedSixSource22.source_size

theorem stage1_lane (i : Nat) :
    digit (2 ^ 64) i stage1 = digit (2 ^ 64) (eraseDigit 4 2 i) PreparedEJMAnchor13674PackedSixSource22.sourcePacked := by
  exact broadcastBits_lane_nat 64 0 2 PreparedEJMAnchor13674PackedSixSource22.sourcePacked PreparedEJMAnchor13674PackedSixSource22.source_size i

def packed : Nat := stage1

def project (i : Nat) : Nat := (eraseDigit 4 2 i)

theorem packed_size : packed < (2 ^ 64) ^ 64 := by
  exact stage1_size

theorem packed_lane (i : Nat) :
    digit (2 ^ 64) i packed = digit (2 ^ 64) (project i) PreparedEJMAnchor13674PackedSixSource22.sourcePacked := by
  dsimp only [packed, project]
  rw [stage1_lane]

theorem lane_le (i : Nat) :
    digit (2 ^ 64) i packed ≤ 9211035283 := by
  rw [packed_lane]
  exact PreparedEJMAnchor13674PackedSixSource22.source_lane_le (project i)

theorem project_unionCode (e : Assignment) :
    project (unionCode e) = PreparedEJMAnchor13674PackedSixSource22.sourceCode e := by
  have h14 := (e 14).isLt
  have h17 := (e 17).isLt
  have h19 := (e 19).isLt
  dsimp [project, eraseDigit, unionCode, PreparedEJMAnchor13674PackedSixSource22.sourceCode]
  omega

theorem lane_binding (e : Assignment) :
    ((digit (2 ^ 64) (unionCode e) packed : Nat) : ℤ) = PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19) + 7931759500 := by
  rw [packed_lane, project_unionCode]
  exact PreparedEJMAnchor13674PackedSixSource22.source_binding_at e

end Output

def xLane (i : Fin 64) : Nat := digit (2 ^ 64) i.val Output.packed
def yLane (i : Fin 64) : Nat := digit (2 ^ 64) i.val Input01.packed + digit (2 ^ 64) i.val Input10.packed + digit (2 ^ 64) i.val Input14.packed + digit (2 ^ 64) i.val Input21.packed

def xCells : List Nat := List.ofFn xLane
def yCells : List Nat := List.ofFn yLane

def xPacked : Nat := Output.packed
def yPacked : Nat := Input01.packed + Input10.packed + Input14.packed + Input21.packed
def guardMask : Nat := mask 64 64

theorem x_pack : pack 64 xCells = xPacked := by
  exact pack_ofFn_digit 64 64 xPacked Output.packed_size

theorem y_pack : pack 64 yCells = yPacked := by
  dsimp only [yCells, yLane, yPacked]
  simp only [pack_ofFn_add]
  rw [pack_ofFn_digit 64 64 Input01.packed Input01.packed_size, pack_ofFn_digit 64 64 Input10.packed Input10.packed_size, pack_ofFn_digit 64 64 Input14.packed Input14.packed_size, pack_ofFn_digit 64 64 Input21.packed Input21.packed_size]

theorem x_range (i : Fin 64) : xLane i < 2 ^ (64 - 1) := by
  exact (Output.lane_le i.val).trans_lt (by decide)

theorem y_range (i : Fin 64) : yLane i < 2 ^ (64 - 1) := by
  have h0 := Input01.lane_le i.val
  have h1 := Input10.lane_le i.val
  have h2 := Input14.lane_le i.val
  have h3 := Input21.lane_le i.val
  dsimp only [yLane]
  omega

set_option trace.profiler true in
theorem packed_guard_checked :
    ((guardMask + yPacked - xPacked) &&& guardMask) = guardMask := by
  decide +kernel

theorem pointwise_nat (i : Fin 64) : xLane i ≤ yLane i := by
  apply guard_ofFn_le 64 (by decide) xLane yLane x_range y_range
  change ((mask 64 64 + pack 64 yCells - pack 64 xCells) &&&
    mask 64 64) = mask 64 64
  rw [x_pack, y_pack]
  exact packed_guard_checked

theorem inequality_at (e : Assignment) :
    PreparedEJMAnchor13674PackedSixTables.table22 (e 17) (e 19) ≤ TransientEJMAnchor13674VEGroups.table01 (e 14) (e 17) + TransientEJMAnchor13674VEGroups.table10 (e 14) (e 19) + TransientEJMAnchor13674VEGroups.table14 (e 14) (e 17) (e 19) + PreparedEJMAnchor13674PackedSixTables.table21 (e 14) (e 17) (e 19) := by
  let i : Fin 64 := ⟨unionCode e, unionCode_lt e⟩
  have h : (xLane i : ℤ) ≤ (yLane i : ℤ) := by
    exact_mod_cast pointwise_nat i
  dsimp only [xLane, yLane, i] at h
  push_cast at h
  rw [Input01.lane_binding e, Input10.lane_binding e, Input14.lane_binding e, Input21.lane_binding e, Output.lane_binding e] at h
  linarith only [h]

#print axioms inequality_at
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMAnchor13674PackedSixBucket04

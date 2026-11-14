/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/HeawoodInterfaces.beta_graph; instance=D5/S3/Combinatorics/Graph/StarForming/HeawoodPorts.facts
   digest: Actual broken-Heawood dissociation cap and saturated selected ports. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
import D5.S3.Combinatorics.Graph.StarForming.CubicDense

/-! The written saturated-port lemma in CUBIC_STAR_FORMING_GAPS at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The sparse fourteen-vertex table is unchanged. A bounded
kernel certificate discharges only this local block lemma. No enumeration
of the number of blocks or interface graphs occurs. -/
namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts
open StarFormingDissociationRefutation Cubic

def graph : SimpleGraph (Fin 14) where
  Adj := BrokenAdj
  symm := ⟨fun a b h => (broken_simple.2 a b).mp h⟩
  loopless := ⟨broken_simple.1⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (b ∈ brokenNeighbors a))

private def count (mask : ℕ) (v : Fin 14) : ℕ :=
  ((brokenNeighbors v).filter (fun w => mask.testBit w.val)).length

private def dissociationBool (mask : ℕ) : Bool :=
  (List.finRange 14).all fun v => !mask.testBit v.val || decide (count mask v ≤ 1)

private def factsBool (mask : ℕ) : Bool :=
  decide (selectedCard mask ≤ 8 ∧ (selectedCard mask = 8 →
    mask.testBit 0 = true ∧ mask.testBit 8 = true ∧ count mask 0 = 1 ∧ count mask 8 = 1))

private def capChunk (chunk : ℕ) : Bool :=
  (List.finRange 256).all fun off =>
    !dissociationBool (256*chunk+off.val) || factsBool (256*chunk+off.val)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_0 : capChunk 0 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_1 : capChunk 1 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_2 : capChunk 2 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_3 : capChunk 3 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_4 : capChunk 4 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_5 : capChunk 5 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_6 : capChunk 6 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_7 : capChunk 7 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_8 : capChunk 8 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_9 : capChunk 9 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_10 : capChunk 10 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_11 : capChunk 11 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_12 : capChunk 12 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_13 : capChunk 13 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_14 : capChunk 14 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_15 : capChunk 15 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_16 : capChunk 16 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_17 : capChunk 17 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_18 : capChunk 18 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_19 : capChunk 19 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_20 : capChunk 20 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_21 : capChunk 21 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_22 : capChunk 22 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_23 : capChunk 23 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_24 : capChunk 24 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_25 : capChunk 25 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_26 : capChunk 26 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_27 : capChunk 27 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_28 : capChunk 28 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_29 : capChunk 29 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_30 : capChunk 30 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_31 : capChunk 31 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_32 : capChunk 32 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_33 : capChunk 33 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_34 : capChunk 34 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_35 : capChunk 35 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_36 : capChunk 36 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_37 : capChunk 37 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_38 : capChunk 38 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_39 : capChunk 39 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_40 : capChunk 40 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_41 : capChunk 41 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_42 : capChunk 42 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_43 : capChunk 43 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_44 : capChunk 44 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_45 : capChunk 45 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_46 : capChunk 46 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_47 : capChunk 47 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_48 : capChunk 48 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_49 : capChunk 49 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_50 : capChunk 50 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_51 : capChunk 51 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_52 : capChunk 52 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_53 : capChunk 53 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_54 : capChunk 54 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_55 : capChunk 55 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_56 : capChunk 56 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_57 : capChunk 57 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_58 : capChunk 58 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_59 : capChunk 59 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_60 : capChunk 60 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_61 : capChunk 61 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_62 : capChunk 62 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Sparse bounded reduction of one 256-mask portion of this fixed block.
private theorem chunk_63 : capChunk 63 = true := by
  unfold capChunk dissociationBool factsBool count selectedCard chosen brokenNeighbors fanoNeighbors
  decide +kernel

private theorem all_chunks : ∀ c : Fin 64, capChunk c.val = true
  | ⟨0,_⟩ => chunk_0
  | ⟨1,_⟩ => chunk_1
  | ⟨2,_⟩ => chunk_2
  | ⟨3,_⟩ => chunk_3
  | ⟨4,_⟩ => chunk_4
  | ⟨5,_⟩ => chunk_5
  | ⟨6,_⟩ => chunk_6
  | ⟨7,_⟩ => chunk_7
  | ⟨8,_⟩ => chunk_8
  | ⟨9,_⟩ => chunk_9
  | ⟨10,_⟩ => chunk_10
  | ⟨11,_⟩ => chunk_11
  | ⟨12,_⟩ => chunk_12
  | ⟨13,_⟩ => chunk_13
  | ⟨14,_⟩ => chunk_14
  | ⟨15,_⟩ => chunk_15
  | ⟨16,_⟩ => chunk_16
  | ⟨17,_⟩ => chunk_17
  | ⟨18,_⟩ => chunk_18
  | ⟨19,_⟩ => chunk_19
  | ⟨20,_⟩ => chunk_20
  | ⟨21,_⟩ => chunk_21
  | ⟨22,_⟩ => chunk_22
  | ⟨23,_⟩ => chunk_23
  | ⟨24,_⟩ => chunk_24
  | ⟨25,_⟩ => chunk_25
  | ⟨26,_⟩ => chunk_26
  | ⟨27,_⟩ => chunk_27
  | ⟨28,_⟩ => chunk_28
  | ⟨29,_⟩ => chunk_29
  | ⟨30,_⟩ => chunk_30
  | ⟨31,_⟩ => chunk_31
  | ⟨32,_⟩ => chunk_32
  | ⟨33,_⟩ => chunk_33
  | ⟨34,_⟩ => chunk_34
  | ⟨35,_⟩ => chunk_35
  | ⟨36,_⟩ => chunk_36
  | ⟨37,_⟩ => chunk_37
  | ⟨38,_⟩ => chunk_38
  | ⟨39,_⟩ => chunk_39
  | ⟨40,_⟩ => chunk_40
  | ⟨41,_⟩ => chunk_41
  | ⟨42,_⟩ => chunk_42
  | ⟨43,_⟩ => chunk_43
  | ⟨44,_⟩ => chunk_44
  | ⟨45,_⟩ => chunk_45
  | ⟨46,_⟩ => chunk_46
  | ⟨47,_⟩ => chunk_47
  | ⟨48,_⟩ => chunk_48
  | ⟨49,_⟩ => chunk_49
  | ⟨50,_⟩ => chunk_50
  | ⟨51,_⟩ => chunk_51
  | ⟨52,_⟩ => chunk_52
  | ⟨53,_⟩ => chunk_53
  | ⟨54,_⟩ => chunk_54
  | ⟨55,_⟩ => chunk_55
  | ⟨56,_⟩ => chunk_56
  | ⟨57,_⟩ => chunk_57
  | ⟨58,_⟩ => chunk_58
  | ⟨59,_⟩ => chunk_59
  | ⟨60,_⟩ => chunk_60
  | ⟨61,_⟩ => chunk_61
  | ⟨62,_⟩ => chunk_62
  | ⟨63,_⟩ => chunk_63
  | ⟨n+64,h⟩ => by omega

private theorem count_bridge (mask : Fin 16384) (v : Fin 14) :
    count mask.val v = ((HeawoodParameters.maskSet mask).filter (graph.Adj v)).card := by
  have hn : (brokenNeighbors v).Nodup := by
    unfold brokenNeighbors
    split
    · decide +kernel
    · split
      · decide +kernel
      · exact (fano_simple_cubic.2.2 v).2
  rw [count,← List.toFinset_card_of_nodup (hn.filter _)]
  congr 1
  ext w
  simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,
    HeawoodParameters.maskSet,Finset.mem_univ,true_and]
  change (w ∈ brokenNeighbors v ∧ mask.val.testBit w.val = true) ↔
    (mask.val.testBit w.val = true ∧ w ∈ brokenNeighbors v)
  exact and_comm

/-- Every actual dissociation eight-set selects and saturates both ports. -/
theorem facts (D : Finset (Fin 14)) (hD : IsKIndependent graph 2 D) :
    D.card ≤ 8 ∧ (D.card = 8 → 0 ∈ D ∧ 8 ∈ D ∧
      DegreeCapacity.selectedDegree graph D 0 = 1 ∧
      DegreeCapacity.selectedDegree graph D 8 = 1) := by
  obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask D
  have he : HeawoodParameters.maskSet mask = D := by
    ext v
    simp [HeawoodParameters.maskSet,hm]
  have hb : dissociationBool mask.val = true := by
    apply List.all_eq_true.mpr
    intro v hv
    change (!mask.val.testBit v.val || decide (count mask.val v ≤ 1)) = true
    cases hh : mask.val.testBit v.val
    · simp
    · simp only [Bool.not_true,Bool.false_or,decide_eq_true_eq]
      rw [count_bridge,he]
      have hi := hD v ((hm v).mp hh)
      omega
  have hc := List.all_eq_true.mp (all_chunks ⟨mask.val/256,by omega⟩)
    ⟨mask.val%256,by omega⟩ (List.mem_finRange _)
  have hi : 256*(mask.val/256)+mask.val%256 = mask.val := by omega
  change (!dissociationBool (256*(mask.val/256)+mask.val%256) ||
    factsBool (256*(mask.val/256)+mask.val%256)) = true at hc
  rw [hi,hb] at hc
  have hf : selectedCard mask.val ≤ 8 ∧ (selectedCard mask.val = 8 →
    mask.val.testBit 0 = true ∧ mask.val.testBit 8 = true ∧
      count mask.val 0 = 1 ∧ count mask.val 8 = 1) := by
    simp only [Bool.not_true,Bool.false_or] at hc
    exact of_decide_eq_true hc
  have hs : selectedCard mask.val = D.card := by
    rw [selectedCard,FiniteMasks.list_count]
    congr 1
  rw [hs] at hf
  refine ⟨hf.1,?_⟩
  intro h8
  obtain ⟨h0,h8,hc0,hc8⟩ := hf.2 h8
  refine ⟨(hm 0).mp h0,(hm 8).mp h8,?_,?_⟩
  · simpa only [count_bridge,he,DegreeCapacity.selectedDegree] using hc0
  · simpa only [count_bridge,he,DegreeCapacity.selectedDegree] using hc8

/-- The original attaining selections either saturate both ports or omit both. -/
def eightSet : Finset (Fin 14) := {0,1,2,3,7,8,12,13}
def sevenSet : Finset (Fin 14) := {1,2,4,5,7,10,13}

theorem selections : IsKIndependent graph 2 eightSet ∧ eightSet.card = 8 ∧
    IsKIndependent graph 2 sevenSet ∧ sevenSet.card = 7 ∧
    0 ∉ sevenSet ∧ 8 ∉ sevenSet := by
  unfold IsKIndependent graph eightSet sevenSet BrokenAdj brokenNeighbors fanoNeighbors
  decide +kernel

end D5.S3.Combinatorics.Graph.StarForming.HeawoodPorts

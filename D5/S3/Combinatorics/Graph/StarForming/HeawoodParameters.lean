/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodParameters
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim; result=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result; claim=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim
   digest: The original Heawood graph has beta two seven and upper two-star formation eight. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicCertificate
import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity

/-! The original cyclic labels, incidence rows and selected eight-set are reused
from the supplier. The finite mask cap is only for this fourteen-vertex graph;
it is not a finite substitute for any unbounded composition or cover theorem. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters
open StarFormingDissociationRefutation Cubic

def graph : SimpleGraph (Fin 14) where
  Adj := FanoAdj
  symm := ⟨fun a b h => (fano_simple_cubic.2.1 a b).mp h⟩
  loopless := ⟨fano_simple_cubic.1⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (b ∈ fanoNeighbors a))

def selectedSet : Finset (Fin 14) := Finset.univ.filter fanoSelected

def maskSet (mask : Fin 16384) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => mask.val.testBit v.val = true)

def maskDissociates (mask : Fin 16384) : Prop :=
  ∀ v : Fin 14, mask.val.testBit v.val = true →
    ((fanoNeighbors v).filter (fun w => mask.val.testBit w.val)).length ≤ 1

/-- The supplier's sparse neighbor lists count actual canonical selected degrees. -/
theorem mask_dissociation_iff (mask : Fin 16384) :
    maskDissociates mask ↔ IsKIndependent graph 2 (maskSet mask) := by
  have hc (v : Fin 14) :
      ((fanoNeighbors v).filter (fun w => mask.val.testBit w.val)).length =
        ((maskSet mask).filter (graph.Adj v)).card := by
    rw [← List.toFinset_card_of_nodup ((fano_simple_cubic.2.2 v).2.filter _)]
    congr 1
    ext w
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_filter,maskSet,
      Finset.mem_univ,true_and]
    change (w ∈ fanoNeighbors v ∧ mask.val.testBit w.val = true) ↔
      (mask.val.testBit w.val = true ∧ w ∈ fanoNeighbors v)
    exact and_comm
  constructor
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc] at hh
    omega
  · intro h v hv
    have hh := h v (by simpa [maskSet] using hv)
    rw [hc]
    omega

private def dissociationBool (mask : ℕ) : Bool :=
  (List.finRange 14).all fun v => !mask.testBit v.val ||
    decide (((fanoNeighbors v).filter (fun w => mask.testBit w.val)).length ≤ 1)

private def capChunk (chunk : ℕ) : Bool :=
  (List.finRange 256).all fun offset =>
    let mask := 256 * chunk + offset.val
    decide (((List.finRange 14).filter (fun v => mask.testBit v.val)).length ≤ 7) ||
      !dissociationBool mask

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_0 : capChunk 0 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_1 : capChunk 1 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_2 : capChunk 2 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_3 : capChunk 3 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_4 : capChunk 4 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_5 : capChunk 5 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_6 : capChunk 6 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_7 : capChunk 7 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_8 : capChunk 8 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_9 : capChunk 9 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_10 : capChunk 10 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_11 : capChunk 11 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_12 : capChunk 12 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_13 : capChunk 13 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_14 : capChunk 14 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_15 : capChunk 15 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_16 : capChunk 16 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_17 : capChunk 17 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_18 : capChunk 18 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_19 : capChunk 19 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_20 : capChunk 20 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_21 : capChunk 21 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_22 : capChunk 22 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_23 : capChunk 23 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_24 : capChunk 24 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_25 : capChunk 25 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_26 : capChunk 26 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_27 : capChunk 27 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_28 : capChunk 28 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_29 : capChunk 29 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_30 : capChunk 30 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_31 : capChunk 31 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_32 : capChunk 32 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_33 : capChunk 33 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_34 : capChunk 34 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_35 : capChunk 35 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_36 : capChunk 36 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_37 : capChunk 37 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_38 : capChunk 38 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_39 : capChunk 39 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_40 : capChunk 40 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_41 : capChunk 41 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_42 : capChunk 42 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_43 : capChunk 43 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_44 : capChunk 44 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_45 : capChunk 45 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_46 : capChunk 46 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_47 : capChunk 47 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_48 : capChunk 48 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_49 : capChunk 49 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_50 : capChunk 50 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_51 : capChunk 51 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_52 : capChunk 52 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_53 : capChunk 53 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_54 : capChunk 54 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_55 : capChunk 55 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_56 : capChunk 56 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_57 : capChunk 57 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_58 : capChunk 58 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_59 : capChunk 59 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_60 : capChunk 60 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_61 : capChunk 61 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_62 : capChunk 62 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Each bounded chunk limits kernel reduction and its temporary memory.
private theorem cap_chunk_63 : capChunk 63 = true := by
  unfold capChunk dissociationBool fanoNeighbors
  decide +kernel

private theorem all_cap_chunks : ∀ chunk : Fin 64, capChunk chunk.val = true
  | ⟨0, _⟩ => cap_chunk_0
  | ⟨1, _⟩ => cap_chunk_1
  | ⟨2, _⟩ => cap_chunk_2
  | ⟨3, _⟩ => cap_chunk_3
  | ⟨4, _⟩ => cap_chunk_4
  | ⟨5, _⟩ => cap_chunk_5
  | ⟨6, _⟩ => cap_chunk_6
  | ⟨7, _⟩ => cap_chunk_7
  | ⟨8, _⟩ => cap_chunk_8
  | ⟨9, _⟩ => cap_chunk_9
  | ⟨10, _⟩ => cap_chunk_10
  | ⟨11, _⟩ => cap_chunk_11
  | ⟨12, _⟩ => cap_chunk_12
  | ⟨13, _⟩ => cap_chunk_13
  | ⟨14, _⟩ => cap_chunk_14
  | ⟨15, _⟩ => cap_chunk_15
  | ⟨16, _⟩ => cap_chunk_16
  | ⟨17, _⟩ => cap_chunk_17
  | ⟨18, _⟩ => cap_chunk_18
  | ⟨19, _⟩ => cap_chunk_19
  | ⟨20, _⟩ => cap_chunk_20
  | ⟨21, _⟩ => cap_chunk_21
  | ⟨22, _⟩ => cap_chunk_22
  | ⟨23, _⟩ => cap_chunk_23
  | ⟨24, _⟩ => cap_chunk_24
  | ⟨25, _⟩ => cap_chunk_25
  | ⟨26, _⟩ => cap_chunk_26
  | ⟨27, _⟩ => cap_chunk_27
  | ⟨28, _⟩ => cap_chunk_28
  | ⟨29, _⟩ => cap_chunk_29
  | ⟨30, _⟩ => cap_chunk_30
  | ⟨31, _⟩ => cap_chunk_31
  | ⟨32, _⟩ => cap_chunk_32
  | ⟨33, _⟩ => cap_chunk_33
  | ⟨34, _⟩ => cap_chunk_34
  | ⟨35, _⟩ => cap_chunk_35
  | ⟨36, _⟩ => cap_chunk_36
  | ⟨37, _⟩ => cap_chunk_37
  | ⟨38, _⟩ => cap_chunk_38
  | ⟨39, _⟩ => cap_chunk_39
  | ⟨40, _⟩ => cap_chunk_40
  | ⟨41, _⟩ => cap_chunk_41
  | ⟨42, _⟩ => cap_chunk_42
  | ⟨43, _⟩ => cap_chunk_43
  | ⟨44, _⟩ => cap_chunk_44
  | ⟨45, _⟩ => cap_chunk_45
  | ⟨46, _⟩ => cap_chunk_46
  | ⟨47, _⟩ => cap_chunk_47
  | ⟨48, _⟩ => cap_chunk_48
  | ⟨49, _⟩ => cap_chunk_49
  | ⟨50, _⟩ => cap_chunk_50
  | ⟨51, _⟩ => cap_chunk_51
  | ⟨52, _⟩ => cap_chunk_52
  | ⟨53, _⟩ => cap_chunk_53
  | ⟨54, _⟩ => cap_chunk_54
  | ⟨55, _⟩ => cap_chunk_55
  | ⟨56, _⟩ => cap_chunk_56
  | ⟨57, _⟩ => cap_chunk_57
  | ⟨58, _⟩ => cap_chunk_58
  | ⟨59, _⟩ => cap_chunk_59
  | ⟨60, _⟩ => cap_chunk_60
  | ⟨61, _⟩ => cap_chunk_61
  | ⟨62, _⟩ => cap_chunk_62
  | ⟨63, _⟩ => cap_chunk_63
  | ⟨remaining + 64, hbound⟩ => by omega

/-- Exact finite cap for every subset of this fixed Fano incidence graph. -/
theorem mask_cap (mask : Fin 16384) (h : maskDissociates mask) :
    ((List.finRange 14).filter (fun v => mask.val.testBit v.val)).length ≤ 7 := by
  have hbool : dissociationBool mask.val = true := by
    apply List.all_eq_true.mpr
    intro v hv
    change (!mask.val.testBit v.val || decide (_ ≤ 1)) = true
    cases hb : mask.val.testBit v.val with
    | false => simp
    | true =>
      simp only [Bool.not_true,Bool.false_or,decide_eq_true_eq]
      exact h v hb
  have hchunk := all_cap_chunks ⟨mask.val / 256, by omega⟩
  have hcheck := List.all_eq_true.mp hchunk ⟨mask.val % 256, by omega⟩
    (List.mem_finRange _)
  have hindex : 256 * (mask.val / 256) + mask.val % 256 = mask.val := by omega
  change (decide (((List.finRange 14).filter
    (fun v => (256 * (mask.val / 256) + mask.val % 256).testBit v.val)).length ≤ 7) ||
      !dissociationBool (256 * (mask.val / 256) + mask.val % 256)) = true at hcheck
  rw [hindex,hbool] at hcheck
  simpa using hcheck

/-- Both the upper bound and an actual bipartition side are checked. -/
theorem beta_graph : beta graph 2 = 7 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro S hS
    obtain ⟨mask,hm⟩ := FiniteMasks.selection_mask S
    have he : maskSet mask = S := by ext v; simp [maskSet,hm]
    have hi : maskDissociates mask := (mask_dissociation_iff mask).mpr
      (he.symm ▸ (Finset.mem_filter.mp hS).2)
    have hc := mask_cap mask hi
    rw [FiniteMasks.list_count] at hc
    change (maskSet mask).card ≤ 7 at hc
    simpa only [he] using hc
  · let S : Finset (Fin 14) := {0,1,2,3,4,5,6}
    have hi : IsKIndependent graph 2 S := by
      change IsKIndependent graph 2 {0,1,2,3,4,5,6}
      unfold IsKIndependent graph FanoAdj fanoNeighbors
      decide +kernel
    have hc : S.card = 7 := by decide +kernel
    rw [← hc]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)

/-- Degree capacity supplies the all-minimal-selection upper bound. -/
theorem sf_graph : SF graph 2 = 8 := by
  classical
  have hd : ∀ v : Fin 14, DegreeCapacity.degree graph v = 3 := by
    unfold DegreeCapacity.degree graph FanoAdj fanoNeighbors
    decide +kernel
  have hu := DegreeCapacity.sf_regular_bound graph 3 (by omega) hd
  have hm : IsMinimalStarForming graph 2 selectedSet := by
    apply (regular_minimal_iff graph selectedSet).mp
    simpa [graph,selectedSet] using fano_minimal
  have hc : selectedSet.card = 8 := by
    have hh := fano_selected_card
    rw [FiniteMasks.list_count] at hh
    simpa [selectedSet] using hh
  have hl : selectedSet.card ≤ SF graph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hm⟩)
  rw [hc] at hl
  norm_num at hu
  omega

/-- The graph is bipartite and every vertex has degree three. -/
theorem graph_class : graph.Colorable 2 ∧
    ∀ v, (Finset.univ.filter (graph.Adj v)).card = 3 := by
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 7 then (0 : Fin 2) else 1) ?_⟩
    change ∀ a b : Fin 14, FanoAdj a b →
      (if a.val < 7 then (0 : Fin 2) else 1) ≠ (if b.val < 7 then 0 else 1)
    unfold FanoAdj fanoNeighbors
    decide +kernel
  · unfold graph FanoAdj fanoNeighbors
    decide +kernel

/-- The original universal cubic bipartite identification is false. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.Colorable 2 → (∀ v, (Finset.univ.filter (G.Adj v)).card = 3) → beta G 2 = SF G 2

theorem result : ¬ claim := by
  intro h
  have hh := h 14 graph graph_class.1 graph_class.2
  rw [beta_graph,sf_graph] at hh
  omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodParameters

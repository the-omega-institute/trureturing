/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicDense
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicDense
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/CubicExact.ambient_heawood_cap; instance=D5/S3/Combinatorics/Graph/StarForming/CubicDense.all_dense_chunks
   digest: Exact finite local certificates and ambient graph deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicCertificate

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicDense.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The local certificate domains and original embedding hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Cubic

open Regular

open Subcubic

def brokenNeighbors (vertex : Fin 14) : List (Fin 14) :=
  if vertex = 0 then [7,10] else if vertex = 8 then [1,5] else fanoNeighbors vertex

def BrokenAdj (first second : Fin 14) : Prop := second ∈ brokenNeighbors first

theorem broken_simple :
    (∀ vertex : Fin 14, ¬ BrokenAdj vertex vertex) ∧
    (∀ first second : Fin 14, BrokenAdj first second ↔ BrokenAdj second first) := by
  unfold BrokenAdj brokenNeighbors fanoNeighbors
  decide +kernel

def chosen (mask : Nat) (vertex : Fin 14) : Bool := mask.testBit vertex.val

def kept (mask : Nat) (deleted vertex : Fin 14) : Bool :=
  chosen mask vertex && decide (vertex ≠ deleted)

def selectedCard (mask : Nat) : Nat :=
  ((List.finRange 14).filter (chosen mask)).length

def starBool (selection : Fin 14 → Bool) (outside : Fin 14) : Bool :=
  ((brokenNeighbors outside).any fun first => selection first &&
    (brokenNeighbors outside).any fun second => selection second && decide (first ≠ second)) ||
  ((brokenNeighbors outside).any fun center => selection center &&
    (brokenNeighbors center).any selection)

theorem starBool_correct (selection : Fin 14 → Bool) (outside : Fin 14) :
    starBool selection outside = true ↔
    TwoAt BrokenAdj (fun vertex => selection vertex = true) outside := by
  simp only [starBool, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨first, hfirst, hf, second, hsecond, hs, hne⟩ |
      ⟨center, hcenter, hc, leaf, hleaf, hl⟩)
    · exact Or.inl ⟨first, second, hf, hs, hne, hfirst, hsecond⟩
    · exact Or.inr ⟨center, leaf, hc, hl, hcenter, hleaf⟩
  · rintro (⟨first, second, hf, hs, hne, hfirst, hsecond⟩ |
      ⟨center, leaf, hc, hl, hcenter, hleaf⟩)
    · exact Or.inl ⟨first, hfirst, hf, second, hsecond, hs, hne⟩
    · exact Or.inr ⟨center, hcenter, hc, leaf, hleaf, hl⟩

def safeBool (mask : Nat) (deleted : Fin 14) : Bool :=
  chosen mask deleted && decide (deleted ≠ 0 ∧ deleted ≠ 8) &&
  starBool (kept mask deleted) deleted &&
  (brokenNeighbors deleted).all (fun center => !chosen mask center ||
    (brokenNeighbors center).any (kept mask deleted)) &&
  (brokenNeighbors deleted).all (fun outside => chosen mask outside ||
    starBool (kept mask deleted) outside)

def Safe (mask : Nat) (deleted : Fin 14) : Prop :=
  chosen mask deleted = true ∧ (deleted ≠ 0 ∧ deleted ≠ 8) ∧
  TwoAt BrokenAdj (fun vertex => chosen mask vertex = true ∧ vertex ≠ deleted) deleted ∧
  (∀ center, chosen mask center = true → BrokenAdj deleted center →
    ∃ leaf, (chosen mask leaf = true ∧ leaf ≠ deleted) ∧ BrokenAdj center leaf) ∧
  (∀ outside, chosen mask outside ≠ true → BrokenAdj deleted outside →
    TwoAt BrokenAdj (fun vertex => chosen mask vertex = true ∧ vertex ≠ deleted) outside)

theorem safeBool_correct (mask : Nat) (deleted : Fin 14)
    (hsafe : safeBool mask deleted = true) : Safe mask deleted := by
  simp only [safeBool, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  obtain ⟨⟨⟨⟨hselected, hnonport⟩, hnew⟩, hreplace⟩, houtside⟩ := hsafe
  have hkept : (fun vertex => kept mask deleted vertex = true) =
      (fun vertex => chosen mask vertex = true ∧ vertex ≠ deleted) := by
    funext vertex
    simp only [kept, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hselected, hnonport, ?_, ?_, ?_⟩
  · simpa only [hkept] using (starBool_correct _ _).mp hnew
  · intro center hc hedge
    have hchoice : (brokenNeighbors center).any (kept mask deleted) = true := by
      simpa [hc] using List.all_eq_true.mp hreplace center hedge
    obtain ⟨leaf, hleaf, hl⟩ := List.any_eq_true.mp hchoice
    exact ⟨leaf, by simpa only [kept, Bool.and_eq_true, decide_eq_true_eq] using hl, hleaf⟩
  · intro outside hout hedge
    have hchoice := List.all_eq_true.mp houtside outside hedge
    have hcases : chosen mask outside = true ∨ starBool (kept mask deleted) outside = true := by
      simpa only [Bool.or_eq_true] using hchoice
    rcases hcases with hselected | hstar
    · exact False.elim (hout hselected)
    · simpa only [hkept] using (starBool_correct _ _).mp hstar

def denseChunk (chunk : Nat) : Bool :=
  (List.finRange 256).all fun offset =>
    let mask := 256 * chunk + offset.val
    decide (selectedCard mask < 9) || (List.finRange 14).any (safeBool mask)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_0 : denseChunk 0 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_1 : denseChunk 1 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_2 : denseChunk 2 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_3 : denseChunk 3 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_4 : denseChunk 4 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_5 : denseChunk 5 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_6 : denseChunk 6 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_7 : denseChunk 7 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_8 : denseChunk 8 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_9 : denseChunk 9 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_10 : denseChunk 10 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_11 : denseChunk 11 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_12 : denseChunk 12 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_13 : denseChunk 13 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_14 : denseChunk 14 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_15 : denseChunk 15 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_16 : denseChunk 16 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_17 : denseChunk 17 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_18 : denseChunk 18 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_19 : denseChunk 19 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_20 : denseChunk 20 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_21 : denseChunk 21 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_22 : denseChunk 22 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_23 : denseChunk 23 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_24 : denseChunk 24 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_25 : denseChunk 25 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_26 : denseChunk 26 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_27 : denseChunk 27 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_28 : denseChunk 28 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_29 : denseChunk 29 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_30 : denseChunk 30 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_31 : denseChunk 31 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_32 : denseChunk 32 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_33 : denseChunk 33 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_34 : denseChunk 34 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_35 : denseChunk 35 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_36 : denseChunk 36 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_37 : denseChunk 37 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_38 : denseChunk 38 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_39 : denseChunk 39 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_40 : denseChunk 40 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_41 : denseChunk 41 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_42 : denseChunk 42 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_43 : denseChunk 43 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_44 : denseChunk 44 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_45 : denseChunk 45 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_46 : denseChunk 46 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_47 : denseChunk 47 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_48 : denseChunk 48 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_49 : denseChunk 49 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_50 : denseChunk 50 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_51 : denseChunk 51 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_52 : denseChunk 52 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_53 : denseChunk 53 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_54 : denseChunk 54 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_55 : denseChunk 55 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_56 : denseChunk 56 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_57 : denseChunk 57 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_58 : denseChunk 58 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_59 : denseChunk 59 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_60 : denseChunk 60 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_61 : denseChunk 61 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_62 : denseChunk 62 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
theorem dense_chunk_63 : denseChunk 63 = true := by
  unfold denseChunk selectedCard safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

theorem all_dense_chunks : ∀ chunk : Fin 64, denseChunk chunk.val = true
  | ⟨0, _⟩ => dense_chunk_0
  | ⟨1, _⟩ => dense_chunk_1
  | ⟨2, _⟩ => dense_chunk_2
  | ⟨3, _⟩ => dense_chunk_3
  | ⟨4, _⟩ => dense_chunk_4
  | ⟨5, _⟩ => dense_chunk_5
  | ⟨6, _⟩ => dense_chunk_6
  | ⟨7, _⟩ => dense_chunk_7
  | ⟨8, _⟩ => dense_chunk_8
  | ⟨9, _⟩ => dense_chunk_9
  | ⟨10, _⟩ => dense_chunk_10
  | ⟨11, _⟩ => dense_chunk_11
  | ⟨12, _⟩ => dense_chunk_12
  | ⟨13, _⟩ => dense_chunk_13
  | ⟨14, _⟩ => dense_chunk_14
  | ⟨15, _⟩ => dense_chunk_15
  | ⟨16, _⟩ => dense_chunk_16
  | ⟨17, _⟩ => dense_chunk_17
  | ⟨18, _⟩ => dense_chunk_18
  | ⟨19, _⟩ => dense_chunk_19
  | ⟨20, _⟩ => dense_chunk_20
  | ⟨21, _⟩ => dense_chunk_21
  | ⟨22, _⟩ => dense_chunk_22
  | ⟨23, _⟩ => dense_chunk_23
  | ⟨24, _⟩ => dense_chunk_24
  | ⟨25, _⟩ => dense_chunk_25
  | ⟨26, _⟩ => dense_chunk_26
  | ⟨27, _⟩ => dense_chunk_27
  | ⟨28, _⟩ => dense_chunk_28
  | ⟨29, _⟩ => dense_chunk_29
  | ⟨30, _⟩ => dense_chunk_30
  | ⟨31, _⟩ => dense_chunk_31
  | ⟨32, _⟩ => dense_chunk_32
  | ⟨33, _⟩ => dense_chunk_33
  | ⟨34, _⟩ => dense_chunk_34
  | ⟨35, _⟩ => dense_chunk_35
  | ⟨36, _⟩ => dense_chunk_36
  | ⟨37, _⟩ => dense_chunk_37
  | ⟨38, _⟩ => dense_chunk_38
  | ⟨39, _⟩ => dense_chunk_39
  | ⟨40, _⟩ => dense_chunk_40
  | ⟨41, _⟩ => dense_chunk_41
  | ⟨42, _⟩ => dense_chunk_42
  | ⟨43, _⟩ => dense_chunk_43
  | ⟨44, _⟩ => dense_chunk_44
  | ⟨45, _⟩ => dense_chunk_45
  | ⟨46, _⟩ => dense_chunk_46
  | ⟨47, _⟩ => dense_chunk_47
  | ⟨48, _⟩ => dense_chunk_48
  | ⟨49, _⟩ => dense_chunk_49
  | ⟨50, _⟩ => dense_chunk_50
  | ⟨51, _⟩ => dense_chunk_51
  | ⟨52, _⟩ => dense_chunk_52
  | ⟨53, _⟩ => dense_chunk_53
  | ⟨54, _⟩ => dense_chunk_54
  | ⟨55, _⟩ => dense_chunk_55
  | ⟨56, _⟩ => dense_chunk_56
  | ⟨57, _⟩ => dense_chunk_57
  | ⟨58, _⟩ => dense_chunk_58
  | ⟨59, _⟩ => dense_chunk_59
  | ⟨60, _⟩ => dense_chunk_60
  | ⟨61, _⟩ => dense_chunk_61
  | ⟨62, _⟩ => dense_chunk_62
  | ⟨63, _⟩ => dense_chunk_63
  | ⟨remaining + 64, hbound⟩ => by omega

theorem dense_certificate (mask : Fin 16384) (hcard : 9 ≤ selectedCard mask.val) :
    ∃ deleted, Safe mask.val deleted := by
  have hchunk := all_dense_chunks ⟨mask.val / 256, by omega⟩
  have hcheck := List.all_eq_true.mp hchunk ⟨mask.val % 256, by omega⟩
    (List.mem_finRange _)
  have hindex : 256 * (mask.val / 256) + mask.val % 256 = mask.val := by omega
  change (decide (selectedCard (256 * (mask.val / 256) + mask.val % 256) < 9) ||
    (List.finRange 14).any (safeBool (256 * (mask.val / 256) + mask.val % 256))) = true at hcheck
  rw [hindex] at hcheck
  have hcases : decide (selectedCard mask.val < 9) = true ∨
      (List.finRange 14).any (safeBool mask.val) = true := by
    simpa only [Bool.or_eq_true] using hcheck
  rcases hcases with hsmall | hexists
  · have hlt := of_decide_eq_true hsmall
    omega
  · obtain ⟨deleted, _, hsafe⟩ := List.any_eq_true.mp hexists
    exact ⟨deleted, safeBool_correct _ _ hsafe⟩

end D5.S3.Combinatorics.Graph.StarForming.Cubic

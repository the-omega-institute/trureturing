/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodBareCap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodBareCap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual arbitrary-ambient one- and two-bare-port Heawood loss. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicExact
import D5.S3.Combinatorics.Graph.StarForming.FiniteMasks
import D5.S3.Combinatorics.Graph.StarForming.FiniteCover

/-! BARE_HEAWOOD_PORT_COMPENSATION and HEAWOOD_BLOCK_COMPENSATION at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
The local certificate ranges over every selection of the fixed fourteen-point
block. Its conclusion is transported to arbitrary ambient graphs by the
unchanged exact nonport-neighborhood supported-deletion argument. -/

namespace D5.S3.Combinatorics.Graph.StarForming.Cubic
open Regular Subcubic

def bareBool (mask : ℕ) (port : Fin 14) : Bool :=
  !chosen mask port && (brokenNeighbors port).all (fun v => !chosen mask v)

def bareCount (mask : ℕ) : ℕ :=
  (if bareBool mask 0 then 1 else 0)+(if bareBool mask 8 then 1 else 0)

private def smallBareChunk (chunk : ℕ) : Bool :=
  (List.finRange 256).all fun offset =>
    let mask := 256*chunk+offset.val
    decide (8<selectedCard mask ∨ selectedCard mask+bareCount mask≤8) ||
      (List.finRange 14).any (safeBool mask)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_0 : smallBareChunk 0=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_1 : smallBareChunk 1=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_2 : smallBareChunk 2=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_3 : smallBareChunk 3=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_4 : smallBareChunk 4=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_5 : smallBareChunk 5=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_6 : smallBareChunk 6=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_7 : smallBareChunk 7=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_8 : smallBareChunk 8=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_9 : smallBareChunk 9=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_10 : smallBareChunk 10=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_11 : smallBareChunk 11=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_12 : smallBareChunk 12=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_13 : smallBareChunk 13=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_14 : smallBareChunk 14=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_15 : smallBareChunk 15=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_16 : smallBareChunk 16=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_17 : smallBareChunk 17=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_18 : smallBareChunk 18=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_19 : smallBareChunk 19=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_20 : smallBareChunk 20=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_21 : smallBareChunk 21=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_22 : smallBareChunk 22=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_23 : smallBareChunk 23=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_24 : smallBareChunk 24=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_25 : smallBareChunk 25=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_26 : smallBareChunk 26=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_27 : smallBareChunk 27=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_28 : smallBareChunk 28=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_29 : smallBareChunk 29=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_30 : smallBareChunk 30=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_31 : smallBareChunk 31=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_32 : smallBareChunk 32=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_33 : smallBareChunk 33=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_34 : smallBareChunk 34=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_35 : smallBareChunk 35=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_36 : smallBareChunk 36=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_37 : smallBareChunk 37=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_38 : smallBareChunk 38=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_39 : smallBareChunk 39=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_40 : smallBareChunk 40=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_41 : smallBareChunk 41=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_42 : smallBareChunk 42=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_43 : smallBareChunk 43=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_44 : smallBareChunk 44=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_45 : smallBareChunk 45=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_46 : smallBareChunk 46=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_47 : smallBareChunk 47=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_48 : smallBareChunk 48=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_49 : smallBareChunk 49=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_50 : smallBareChunk 50=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_51 : smallBareChunk 51=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_52 : smallBareChunk 52=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_53 : smallBareChunk 53=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_54 : smallBareChunk 54=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_55 : smallBareChunk 55=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_56 : smallBareChunk 56=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_57 : smallBareChunk 57=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_58 : smallBareChunk 58=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_59 : smallBareChunk 59=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_60 : smallBareChunk 60=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_61 : smallBareChunk 61=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_62 : smallBareChunk 62=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
private theorem small_bare_chunk_63 : smallBareChunk 63=true := by
  unfold smallBareChunk selectedCard bareCount bareBool safeBool starBool kept chosen brokenNeighbors fanoNeighbors
  decide +kernel

private theorem all_small_bare_chunks : ∀ c : Fin 64, smallBareChunk c.val=true := by
  intro c
  fin_cases c
  · exact small_bare_chunk_0
  · exact small_bare_chunk_1
  · exact small_bare_chunk_2
  · exact small_bare_chunk_3
  · exact small_bare_chunk_4
  · exact small_bare_chunk_5
  · exact small_bare_chunk_6
  · exact small_bare_chunk_7
  · exact small_bare_chunk_8
  · exact small_bare_chunk_9
  · exact small_bare_chunk_10
  · exact small_bare_chunk_11
  · exact small_bare_chunk_12
  · exact small_bare_chunk_13
  · exact small_bare_chunk_14
  · exact small_bare_chunk_15
  · exact small_bare_chunk_16
  · exact small_bare_chunk_17
  · exact small_bare_chunk_18
  · exact small_bare_chunk_19
  · exact small_bare_chunk_20
  · exact small_bare_chunk_21
  · exact small_bare_chunk_22
  · exact small_bare_chunk_23
  · exact small_bare_chunk_24
  · exact small_bare_chunk_25
  · exact small_bare_chunk_26
  · exact small_bare_chunk_27
  · exact small_bare_chunk_28
  · exact small_bare_chunk_29
  · exact small_bare_chunk_30
  · exact small_bare_chunk_31
  · exact small_bare_chunk_32
  · exact small_bare_chunk_33
  · exact small_bare_chunk_34
  · exact small_bare_chunk_35
  · exact small_bare_chunk_36
  · exact small_bare_chunk_37
  · exact small_bare_chunk_38
  · exact small_bare_chunk_39
  · exact small_bare_chunk_40
  · exact small_bare_chunk_41
  · exact small_bare_chunk_42
  · exact small_bare_chunk_43
  · exact small_bare_chunk_44
  · exact small_bare_chunk_45
  · exact small_bare_chunk_46
  · exact small_bare_chunk_47
  · exact small_bare_chunk_48
  · exact small_bare_chunk_49
  · exact small_bare_chunk_50
  · exact small_bare_chunk_51
  · exact small_bare_chunk_52
  · exact small_bare_chunk_53
  · exact small_bare_chunk_54
  · exact small_bare_chunk_55
  · exact small_bare_chunk_56
  · exact small_bare_chunk_57
  · exact small_bare_chunk_58
  · exact small_bare_chunk_59
  · exact small_bare_chunk_60
  · exact small_bare_chunk_61
  · exact small_bare_chunk_62
  · exact small_bare_chunk_63

private theorem bare_certificate (mask : Fin 16384)
    (hlarge : 8<selectedCard mask.val+bareCount mask.val) :
    ∃ deleted, Safe mask.val deleted := by
  by_cases hd : 9≤selectedCard mask.val
  · exact dense_certificate mask hd
  have hc := all_small_bare_chunks (⟨mask.val/256,by omega⟩ : Fin 64)
  have ht := List.all_eq_true.mp hc (⟨mask.val%256,by omega⟩ : Fin 256) (List.mem_finRange _)
  have hm : 256*(mask.val/256)+mask.val%256=mask.val := by omega
  change (decide (8<selectedCard (256*(mask.val/256)+mask.val%256) ∨
    selectedCard (256*(mask.val/256)+mask.val%256)+bareCount (256*(mask.val/256)+mask.val%256)≤8) ||
    (List.finRange 14).any (safeBool (256*(mask.val/256)+mask.val%256)))=true at ht
  rw [hm] at ht
  have hs : (List.finRange 14).any (safeBool mask.val)=true := by
    simpa [show ¬(8<selectedCard mask.val ∨ selectedCard mask.val+bareCount mask.val≤8) by omega] using ht
  obtain ⟨deleted,_,hdel⟩ := List.any_eq_true.mp hs
  exact ⟨deleted,safeBool_correct _ _ hdel⟩

/-- Every minimal selection in any allowed ambient graph loses at least
one block vertex per bare port, including two simultaneous bare ports.
The restriction need not form the block. -/
theorem ambient_bare_cap {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (embedding : Fin 14 → Vertex) (mask : Fin 16384)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hinjective : ∀ first second, embedding first = embedding second → first = second)
    (hsound : ∀ first second, BrokenAdj first second → adjacency (embedding first) (embedding second))
    (hselection : ∀ vertex, selection (embedding vertex) ↔ chosen mask.val vertex = true)
    (hnonport : ∀ vertex, vertex ≠ 0 → vertex ≠ 8 → ∀ outside,
      adjacency (embedding vertex) outside → ∃ other, outside = embedding other ∧ BrokenAdj vertex other)
    (hminimal : Minimal adjacency selection) : selectedCard mask.val+bareCount mask.val ≤ 8 := by
  classical
  by_contra hbad
  obtain ⟨deleted,hselected,hports,hnew,hreplace,hadjacent⟩ := bare_certificate mask (by omega)
  have hglobal : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ embedding deleted) := by
    apply supported_deletion adjacency selection (embedding deleted) hminimal.1
    · exact lift_broken_star adjacency selection embedding mask hinjective hsound hselection
        deleted deleted hnew
    · intro outside houtside hedge
      obtain ⟨localOutside, rfl, hlocal⟩ :=
        hnonport deleted hports.1 hports.2 outside (hsymmetric _ _ hedge)
      apply lift_broken_star adjacency selection embedding mask hinjective hsound hselection
        deleted localOutside
      exact hadjacent localOutside (fun hchosen => houtside ((hselection _).mpr hchosen)) hlocal
    · intro center hc hedge
      obtain ⟨localCenter, rfl, hlocal⟩ :=
        hnonport deleted hports.1 hports.2 center (hsymmetric _ _ hedge)
      obtain ⟨leaf, hl, hleaf⟩ := hreplace localCenter ((hselection _).mp hc) hlocal
      exact ⟨embedding leaf, ⟨(hselection _).mpr hl.1,
        fun hequal => hl.2 (hinjective _ _ hequal)⟩, hsound _ _ hleaf⟩
  exact hminimal.2 _ (fun _ hvertex => hvertex.1)
    ⟨embedding deleted, (hselection _).mpr hselected, fun hvertex => hvertex.2 rfl⟩ hglobal

noncomputable def barePorts (C : Finset (Fin 14)) : Finset (Fin 14) := by
  classical
  exact ({0,8} : Finset (Fin 14)).filter (fun p => p ∉ C ∧ ∀ w, BrokenAdj p w → w ∉ C)

private theorem bareBool_correct (mask : ℕ) (p : Fin 14) :
    bareBool mask p=true ↔ chosen mask p≠true ∧
      ∀ w, BrokenAdj p w → chosen mask w≠true := by
  simp [bareBool,BrokenAdj]

/-- The Boolean local tally is the actual number of bare boundary ports
of the represented selection, with the two ports counted once each. -/
theorem bareCount_eq (C : Finset (Fin 14)) (mask : Fin 16384)
    (hmask : ∀ v, chosen mask.val v=true ↔ v ∈ C) :
    bareCount mask.val=(barePorts C).card := by
  classical
  have hb (p : Fin 14) : bareBool mask.val p=true ↔
      p ∉ C ∧ ∀ w, BrokenAdj p w → w ∉ C := by
    constructor
    · intro h
      obtain ⟨hp,hn⟩ := (bareBool_correct mask.val p).mp h
      exact ⟨fun hc => hp ((hmask p).mpr hc),
        fun w ha hw => hn w ha ((hmask w).mpr hw)⟩
    · rintro ⟨hp,hn⟩
      exact (bareBool_correct mask.val p).mpr
        ⟨fun hc => hp ((hmask p).mp hc),
          fun w ha hw => hn w ha ((hmask w).mp hw)⟩
  unfold barePorts
  rw [Finset.card_filter]
  simp only [Finset.sum_insert (by decide : (0 : Fin 14) ∉ ({8} : Finset (Fin 14))),
    Finset.sum_singleton,← hb]
  rfl

/-- Canonical finite sets in an arbitrary actual ambient graph satisfy the
full bare-port loss bound. No internal formation premise is imposed. -/
theorem ambient_graph_bare_cap {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (embedding : Fin 14 → V) (hinjective : Function.Injective embedding)
    (hsound : ∀ a b, BrokenAdj a b → G.Adj (embedding a) (embedding b))
    (hnonport : ∀ v, v≠0 → v≠8 → ∀ x, G.Adj (embedding v) x →
      ∃ w, x=embedding w ∧ BrokenAdj v w)
    (hminimal : StarFormingDissociationRefutation.IsMinimalStarForming G 2 S) :
    let C := Finset.univ.filter (fun v => embedding v ∈ S)
    C.card+(barePorts C).card≤8 := by
  classical
  let C := Finset.univ.filter (fun v => embedding v ∈ S)
  obtain ⟨mask,hmask⟩ := FiniteMasks.selection_mask C
  have hm : ∀ v, chosen mask.val v=true ↔ v ∈ C := hmask
  have hc : selectedCard mask.val=C.card := by
    rw [selectedCard,FiniteMasks.list_count]
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hm]
  have hs : ∀ v, embedding v ∈ S ↔ chosen mask.val v=true := by
    intro v
    rw [hm]
    simp [C]
  have h := ambient_bare_cap G.Adj (· ∈ S) embedding mask
    (fun _ _ ha => G.adj_symm ha) (fun _ _ h => hinjective h) hsound hs hnonport
    ((regular_minimal_iff G S).mpr hminimal)
  rw [hc,bareCount_eq C mask hm] at h
  exact h

end D5.S3.Combinatorics.Graph.StarForming.Cubic

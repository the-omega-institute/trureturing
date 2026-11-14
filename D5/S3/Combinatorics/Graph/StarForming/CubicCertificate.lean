/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicCertificate
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim; result=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.result; claim=D5/S3/Combinatorics/Graph/StarForming/HeawoodParameters.claim
   digest: Exact finite local certificates and ambient graph deletion proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.SubcubicCertificate

/-!
Proof bodies received from the-omega-institute/subquorum-colorings,
revision 48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicCertificate.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
The local certificate domains and original embedding hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Cubic

open Regular

set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 128

open Subcubic

theorem forms_rewiring {Vertex : Type}
    (original modified : Vertex → Vertex → Prop)
    (selection smaller : Vertex → Prop)
    (hsubset : ∀ vertex, smaller vertex → selection vertex)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second))
    (hforms : Forms original smaller) : Forms modified smaller := by
  intro outside houtside
  rcases hforms outside houtside with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨first, second, hf, hs, hne,
      (hagreement outside first (Or.inr (hsubset _ hf))).mp ha,
      (hagreement outside second (Or.inr (hsubset _ hs))).mp hb⟩
  · exact Or.inr ⟨center, leaf, hc, hl,
      (hagreement outside center (Or.inr (hsubset _ hc))).mp ha,
      (hagreement center leaf (Or.inl (hsubset _ hc))).mp hb⟩

theorem minimal_rewiring_forward {Vertex : Type}
    (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second))
    (hminimal : Minimal original selection) : Minimal modified selection := by
  refine ⟨forms_rewiring original modified selection selection (fun _ hvertex => hvertex)
    hagreement hminimal.1, ?_⟩
  intro smaller hsubset hexists hforms
  apply hminimal.2 smaller hsubset hexists
  exact forms_rewiring modified original selection smaller hsubset
    (fun first second hselected => (hagreement first second hselected).symm) hforms

theorem minimal_rewiring {Vertex : Type}
    (original modified : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hagreement : ∀ first second, selection first ∨ selection second →
      (original first second ↔ modified first second)) :
    Minimal original selection ↔ Minimal modified selection := by
  constructor
  · exact minimal_rewiring_forward original modified selection hagreement
  · exact minimal_rewiring_forward modified original selection
      (fun first second hselected => (hagreement first second hselected).symm)

def fanoNeighbors (vertex : Fin 14) : List (Fin 14) :=
  match vertex.val with
  | 0 => [7,8,10]
  | 1 => [8,9,11]
  | 2 => [9,10,12]
  | 3 => [10,11,13]
  | 4 => [7,11,12]
  | 5 => [8,12,13]
  | 6 => [7,9,13]
  | 7 => [0,4,6]
  | 8 => [0,1,5]
  | 9 => [1,2,6]
  | 10 => [0,2,3]
  | 11 => [1,3,4]
  | 12 => [2,4,5]
  | _ => [3,5,6]

def FanoAdj (first second : Fin 14) : Prop := second ∈ fanoNeighbors first

def fanoSelected (vertex : Fin 14) : Prop :=
  vertex ∈ ([1,2,3,5,7,9,10,11] : List (Fin 14))

instance (vertex : Fin 14) : Decidable (fanoSelected vertex) :=
  inferInstanceAs (Decidable (vertex ∈ ([1,2,3,5,7,9,10,11] : List (Fin 14))))

def fanoFailure (vertex : Fin 14) : Fin 14 :=
  match vertex.val with
  | 1 => 8
  | 2 => 12
  | 3 => 13
  | 9 => 6
  | 10 => 0
  | 11 => 4
  | _ => vertex

theorem fano_simple_cubic :
    (∀ vertex : Fin 14, ¬ FanoAdj vertex vertex) ∧
    (∀ first second : Fin 14, FanoAdj first second ↔ FanoAdj second first) ∧
    (∀ vertex : Fin 14, (fanoNeighbors vertex).length = 3 ∧ (fanoNeighbors vertex).Nodup) := by
  unfold FanoAdj fanoNeighbors
  decide +kernel

theorem fano_forms : Forms FanoAdj fanoSelected := by
  unfold Forms TwoAt FanoAdj fanoSelected fanoNeighbors
  decide +kernel

theorem fano_deletion_failures : ∀ deleted : Fin 14, fanoSelected deleted →
    ¬ (fanoSelected (fanoFailure deleted) ∧ fanoFailure deleted ≠ deleted) ∧
    ¬ TwoAt FanoAdj (fun vertex => fanoSelected vertex ∧ vertex ≠ deleted) (fanoFailure deleted) := by
  unfold TwoAt FanoAdj fanoSelected fanoFailure fanoNeighbors
  decide +kernel

theorem fano_minimal : Minimal FanoAdj fanoSelected := by
  apply minimal_of_deletion_failures FanoAdj fanoSelected fano_forms
  intro deleted hselected
  exact ⟨fanoFailure deleted, fano_deletion_failures deleted hselected⟩

theorem fano_selected_card :
    ((List.finRange 14).filter (fun vertex => decide (fanoSelected vertex))).length = 8 := by
  decide +kernel


end D5.S3.Combinatorics.Graph.StarForming.Cubic

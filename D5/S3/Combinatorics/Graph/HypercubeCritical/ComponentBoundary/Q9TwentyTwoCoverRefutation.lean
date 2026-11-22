/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwentyTwoCoverRefutation.claim
   digest: Pair coverage and five-set coverage alone do not force a singleton five-set at twenty-two triples on nine points. -/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwentyTwoCoverRefutation

open Finset

/-- The proposed extension of the singleton-mask bound using full pair coverage. -/
def claim : Prop :=
  ∀ F : Finset (Finset (Fin 9)), F.card = 22 →
    F ⊆ (univ : Finset (Fin 9)).powersetCard 3 →
    (∀ P ∈ (univ : Finset (Fin 9)).powersetCard 2, 1 ≤ (F.filter (P ⊆ ·)).card) →
    (∀ U ∈ (univ : Finset (Fin 9)).powersetCard 5, 1 ≤ (F.filter (· ⊆ U)).card) →
    ∃ U ∈ (univ : Finset (Fin 9)).powersetCard 5, (F.filter (· ⊆ U)).card = 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- An explicit 22-triple family covers every pair and doubles every five-set. -/
theorem result : ¬ claim := by
  let F : Finset (Finset (Fin 9)) :=
    {{0, 1, 6}, {0, 2, 3}, {0, 2, 5}, {0, 3, 4}, {0, 3, 5}, {0, 3, 7},
     {0, 4, 7}, {0, 6, 8}, {1, 2, 7}, {1, 2, 8}, {1, 3, 6}, {1, 4, 5},
     {1, 4, 8}, {1, 5, 8}, {1, 7, 8}, {2, 3, 5}, {2, 4, 6}, {2, 7, 8},
     {3, 4, 7}, {3, 6, 8}, {4, 5, 8}, {5, 6, 7}}
  have hcard : F.card = 22 := by decide
  have htriples : F ⊆ (univ : Finset (Fin 9)).powersetCard 3 := by decide
  have hpairs : ∀ P ∈ (univ : Finset (Fin 9)).powersetCard 2,
      1 ≤ (F.filter (P ⊆ ·)).card := by decide
  have hdouble : ∀ U ∈ (univ : Finset (Fin 9)).powersetCard 5,
      2 ≤ (F.filter (· ⊆ U)).card := by decide
  intro h
  obtain ⟨U, hU, hone⟩ :=
    h F hcard htriples hpairs (fun U hU => le_trans (by decide) (hdouble U hU))
  exact (by decide : ¬ 2 ≤ 1) (hone ▸ hdouble U hU)

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwentyTwoCoverRefutation

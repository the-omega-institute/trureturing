/- GID: D5/S3/Combinatorics/Graph/Queries/CompleteNeighborhoodHistory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/CompleteNeighborhoodHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete adaptive neighborhood transcripts by edge extension and queried degree saturation. -/

import D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! The complete unordered neighborhood at a queried vertex is determined by
edge inclusion and an upper bound on the candidate degree. Replaying the same
answers takes the same branches of the deterministic adaptive protocol. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

variable {V : Type*}

abbrev History (V : Type*) := List (Σ _ : V, Set V)

/-- Return the complete unordered neighborhood of the queried label. -/
def readNeighbors (v : V) (G : SimpleGraph V) : Set V := G.neighborSet v

/-- The undirected graph formed by the edges actually returned in the transcript. -/
def revealedEdges (history : History V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y => ∃ entry ∈ history, x = entry.1 ∧ y ∈ entry.2

private theorem recordedNeighbors (H : SimpleGraph V)
    (p : PassiveProtocol V (fun _ => Set V))
    (entry : Σ _ : V, Set V) (he : entry ∈ runPassiveProtocol readNeighbors p H) :
    entry.2 = H.neighborSet entry.1 := by
  induction p with
  | stop => simp [runPassiveProtocol] at he
  | query v next ih =>
      rw [runPassiveProtocol, List.mem_cons] at he
      rcases he with rfl | ht
      · rfl
      · exact ih _ ht

private theorem extends_of_run (H : SimpleGraph V) (p : PassiveProtocol V (fun _ => Set V)) :
    revealedEdges (runPassiveProtocol readNeighbors p H) ≤ H := by
  intro x y hedge
  rw [revealedEdges, SimpleGraph.fromRel_adj] at hedge
  rcases hedge.2 with ⟨entry, he, rfl, hy⟩ | ⟨entry, he, rfl, hx⟩
  · rwa [recordedNeighbors H p entry he] at hy
  · rw [recordedNeighbors H p entry he] at hx
    exact H.adj_symm hx

private theorem revealedEdges_mono {a b : History V} (hsub : ∀ x ∈ a, x ∈ b) :
    revealedEdges a ≤ revealedEdges b := by
  intro x y hxy
  rw [revealedEdges, SimpleGraph.fromRel_adj] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  rcases hxy.2 with ⟨entry, he, hx, hy⟩ | ⟨entry, he, hy, hx⟩
  · exact Or.inl ⟨entry, hsub _ he, hx, hy⟩
  · exact Or.inr ⟨entry, hsub _ he, hy, hx⟩

/-- A transcript is replayed exactly when its edges are present and the queried degrees are saturated. -/
theorem history_eq_iff_extension [Finite V] (G H : SimpleGraph V)
    (p : PassiveProtocol V (fun _ => Set V)) :
    runPassiveProtocol readNeighbors p G = runPassiveProtocol readNeighbors p H ↔
      revealedEdges (runPassiveProtocol readNeighbors p H) ≤ G ∧
      ∀ entry ∈ runPassiveProtocol readNeighbors p H,
        (G.neighborSet entry.1).ncard ≤ entry.2.ncard := by
  constructor
  · intro heq
    rw [← heq]
    exact ⟨extends_of_run G p, fun entry he => le_of_eq
      (congrArg Set.ncard (recordedNeighbors G p entry he).symm)⟩
  · rintro ⟨hext, hdegree⟩
    induction p with
    | stop => rfl
    | query v next ih =>
        let entry : Σ _ : V, Set V := ⟨v, H.neighborSet v⟩
        have hentry : entry ∈ runPassiveProtocol readNeighbors (.query v next) H := by
          rw [runPassiveProtocol]
          exact List.mem_cons_self
        have hn : H.neighborSet v ⊆ G.neighborSet v := by
          intro w hw
          apply hext
          rw [revealedEdges, SimpleGraph.fromRel_adj]
          exact ⟨H.ne_of_adj hw, Or.inl ⟨entry, hentry, rfl, hw⟩⟩
        have hreply : H.neighborSet v = G.neighborSet v :=
          Set.eq_of_subset_of_ncard_le hn (hdegree entry hentry)
        have htail (a : Σ _ : V, Set V)
            (ha : a ∈ runPassiveProtocol readNeighbors (next (H.neighborSet v)) H) :
            a ∈ runPassiveProtocol readNeighbors (.query v next) H := by
          rw [runPassiveProtocol, List.mem_cons]
          exact Or.inr ha
        simp only [runPassiveProtocol, readNeighbors, ← hreply]
        rw [ih _ (le_trans (revealedEdges_mono htail) hext)
          (fun a ha => hdegree a (htail a ha))]

end D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory

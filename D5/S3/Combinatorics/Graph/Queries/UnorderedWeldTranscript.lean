/- GID: D5/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/UnorderedWeldTranscript
   mirror-E: none(waiver:symbolic-conditioning-law)
   anchors: []
   utility: none
   digest: Complete neighborhood queries on a fixed graph with an alternating cycle added expose a conditional cycle law. -/

import D5.S3.Combinatorics.Graph.LinearForests.AlternatingUndirectedCompletionLaw
import D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory

/-! A transcript from a fixed graph with a random alternating weld exposes a prescribed subgraph of the weld. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.Combinatorics.Graph.LinearForests
open D5.S3.Combinatorics.Graph.Queries.CompleteNeighborhoodHistory
open AlternatingUndirectedCompletionLaw CompatibleCycleInventory
open scoped ENNReal

namespace D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript

variable {V L : Type*}

private theorem replay_iff_weld_extension [Finite V] (p : PassiveProtocol V (fun _ => Set V)) (fixed ref G : SimpleGraph V)
    (hdisjoint : Disjoint fixed ref)
    (hsize : ∀ x, (G.neighborSet x).ncard ≤ (ref.neighborSet x).ncard) :
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref)
    runPassiveProtocol readNeighbors p (fixed ⊔ G) = T ↔ revealedEdges T \ fixed ≤ G := by
  intro T
  have hRef := (history_eq_iff_extension (fixed ⊔ ref) (fixed ⊔ ref) p).mp rfl
  have hDeg (x : V) :
      ((fixed ⊔ G).neighborSet x).ncard ≤ ((fixed ⊔ ref).neighborSet x).ncard := by
    have hSep := SimpleGraph.disjoint_neighborSet.mpr hdisjoint x
    change (fixed.neighborSet x ∪ G.neighborSet x).ncard ≤
      (fixed.neighborSet x ∪ ref.neighborSet x).ncard
    rw [Set.ncard_union_eq hSep]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (hsize x) _)
  change runPassiveProtocol readNeighbors p (fixed ⊔ G) =
    runPassiveProtocol readNeighbors p (fixed ⊔ ref) ↔ _
  rw [history_eq_iff_extension]
  constructor
  · rintro ⟨hle, _⟩ x y h
    exact (hle h.1).resolve_left h.2
  · intro h
    refine ⟨?_, fun e he => (hDeg e.1).trans (hRef.2 e he)⟩
    intro x y he
    by_cases hf : fixed.Adj x y
    · exact Or.inl hf
    · exact Or.inr (h ⟨he, hf⟩)

private theorem mapped_degree_le (e : L ↪ V) (G H : SimpleGraph L)
    (h : ∀ x, (G.neighborSet x).ncard ≤ (H.neighborSet x).ncard)
    (v : V) : ((G.map e).neighborSet v).ncard ≤ ((H.map e).neighborSet v).ncard := by
  by_cases hv : v ∈ Set.range e
  · obtain ⟨l, rfl⟩ := hv
    simpa only [SimpleGraph.neighborSet_map, Set.ncard_image_of_injective _ e.injective] using h l
  · suffices he : (G.map e).neighborSet v = ∅ by simp [he]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨a, b, _, ha, _⟩ := (SimpleGraph.map_adj e G v y).mp hy
    exact hv ⟨a, ha⟩

private theorem mapped_extension (e : L ↪ V) (F : SimpleGraph V) (ref G : SimpleGraph L)
    (hle : F ≤ ref.map e) : F ≤ G.map e ↔ F.comap e ≤ G := by
  constructor
  · intro h x y hxy
    exact SimpleGraph.map_adj_apply.mp (h hxy)
  · intro h x y hxy
    obtain ⟨a, b, _, rfl, rfl⟩ := (SimpleGraph.map_adj e ref x y).mp (hle hxy)
    exact SimpleGraph.map_adj_apply.mpr (h hxy)

/-- An unordered transcript of the welded graph conditions the cycle on its revealed edges. -/
theorem weld_transcript_law [Finite V] [Fintype L] (e : L ↪ V) (k : L → Bool) (n : ℕ) (hn : 2 ≤ n)
    (hr : Nat.card (Side k false) = n) (hb : Nat.card (Side k true) = n)
    (p : PassiveProtocol V (fun _ => Set V)) (fixed : SimpleGraph V) (ref : AlternatingCompletedGraph k ⊥)
    (hdisjoint : Disjoint fixed (ref.1.1.map e))
    (μ : PMF (AlternatingCompletedGraph k ⊥))
    (hμ : ∀ C, μ C = ((n.factorial * (n - 1).factorial / 2 : ℕ) : ℝ≥0∞)⁻¹) :
    let T := runPassiveProtocol readNeighbors p (fixed ⊔ ref.1.1.map e)
    let F := (revealedEdges T \ fixed).comap e
    let event : Set (AlternatingCompletedGraph k ⊥) :=
      {C | runPassiveProtocol readNeighbors p (fixed ⊔ C.1.1.map e) = T}
    event = {C | F ≤ C.1.1} ∧
    μ.toOuterMeasure event =
      (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞) /
        (n.factorial * (n - 1).factorial / 2 : ℕ) ∧
    ∀ hEvent : ∃ C ∈ event, C ∈ μ.support,
      ∃ ν : PMF (AlternatingCompletedGraph k F),
        (∀ C, ν C = (Nat.card (AlternatingCompletedGraph k F) : ℝ≥0∞)⁻¹) ∧
        μ.filter event hEvent = ν.map (forgetPrescribedEdges k) := by
  classical
  intro T F event
  have href : revealedEdges T \ fixed ≤ ref.1.1.map e :=
    (replay_iff_weld_extension p fixed (ref.1.1.map e) (ref.1.1.map e) hdisjoint
      (fun _ => le_rfl)).mp rfl
  have evt : event = {C : AlternatingCompletedGraph k ⊥ | F ≤ C.1.1} := by
    ext C
    have degrees := mapped_degree_le e C.1.1 ref.1.1
      (fun x => ((C.1.2.2.1 x).trans (ref.1.2.2.1 x).symm).le)
    exact (replay_iff_weld_extension p fixed _ _ hdisjoint degrees).trans
      (mapped_extension e _ _ _ href)
  obtain ⟨_, μ', hμ', hm, _, hp⟩ := alternating_undirected_completion_law k F n hn hr hb
  have heq : μ = μ' := PMF.ext (fun C => (hμ C).trans (hμ' C).symm)
  subst μ'
  refine ⟨evt, ?_⟩
  change μ.toOuterMeasure event = _ ∧ ∀ hEvent : ∃ C ∈ event, C ∈ μ.support, _
  rw [evt]
  exact ⟨hm, hp⟩

end D5.S3.Combinatorics.Graph.Queries.UnorderedWeldTranscript

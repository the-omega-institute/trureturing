/- GID: D5/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/KnownNameExplorationSize
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: A known-name exploration has a degree-based bound on names seen. -/

import D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
import D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory

/-! The number of names seen during a complete-neighborhood exploration from a single root. -/

open D5.S3.Combinatorics.Graph.Queries.KnownNameSimulation
open D5.S3.Combinatorics.Graph.Queries.NamedNeighborhoodHistory
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize

variable {V N : Type*}

private theorem extend_card (G : SimpleGraph V) (f : V ↪ N) (root v : V)
    (known : Set N) (cap : ℕ)
    (hRoot : (G.neighborSet root).ncard ≤ cap)
    (hDegree : ∀ x, (G.neighborSet x).ncard ≤ cap + 1)
    (hIncident : ∀ x, x ≠ root → f x ∈ known →
      ∃ y ∈ G.neighborSet x, f y ∈ known)
    (hv : f v ∈ known) :
    (known ∪ f '' G.neighborSet v).ncard ≤ known.ncard + cap := by
  classical
  by_cases hr : v = root
  · rw [hr]
    exact (Set.ncard_union_le _ _).trans
      (Nat.add_le_add_left (by rwa [Set.ncard_image_of_injective _ f.injective]) _)
  · obtain ⟨y, hy, hNamed⟩ := hIncident v hr hv
    let D := G.neighborSet v \ {y}
    have hUnion : known ∪ f '' G.neighborSet v = known ∪ f '' D := by
      ext n
      constructor
      · rintro (hn | ⟨x, hx, rfl⟩)
        · exact Or.inl hn
        · by_cases hxy : x = y
          · exact Or.inl (hxy ▸ hNamed)
          · exact Or.inr ⟨x, ⟨hx, hxy⟩, rfl⟩
      · rintro (hn | ⟨x, hx, rfl⟩)
        · exact Or.inl hn
        · exact Or.inr ⟨x, hx.1, rfl⟩
    have hD : D.ncard ≤ cap := by
      calc
        D.ncard = (G.neighborSet v).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hy
        _ ≤ cap := by
          have hBound := hDegree v
          omega
    rw [hUnion]
    exact (Set.ncard_union_le _ _).trans
      (Nat.add_le_add_left (by rwa [Set.ncard_image_of_injective _ f.injective]) _)

private theorem all_known_card [Finite N] (G : SimpleGraph V) (f : V ↪ N) (root : V) (cap : ℕ)
    (hRoot : (G.neighborSet root).ncard ≤ cap)
    (hDegree : ∀ x, (G.neighborSet x).ncard ≤ cap + 1)
    (p : Protocol N) (known : Set N) (hRange : known ⊆ Set.range f)
    (hIncident : ∀ x, x ≠ root → f x ∈ known →
      ∃ y ∈ G.neighborSet x, f y ∈ known) :
    let record := simulate (fun n => nameReply G n f) p known
    (record.foldl (fun seen entry => namesAfter seen entry.1 entry.2) known).ncard ≤
      known.ncard + cap * (sentNames known record).length := by
  classical
  induction p generalizing known with
  | stop => simp [simulate, sentNames]
  | query name next ih =>
    by_cases hName : name ∈ known
    · obtain ⟨v, rfl⟩ := hRange hName
      let neighbors := f '' G.neighborSet v
      let enlarged := known ∪ neighbors
      have hNext : namesAfter known (f v) (some neighbors) = enlarged :=
        Set.insert_eq_of_mem (Or.inl hName)
      have hNextRange : enlarged ⊆ Set.range f := by
        rintro n (hn | ⟨x, _, rfl⟩)
        · exact hRange hn
        · exact ⟨x, rfl⟩
      have hNextIncident (x : V) (hx : x ≠ root) (hSeen : f x ∈ enlarged) :
          ∃ y ∈ G.neighborSet x, f y ∈ enlarged := by
        rcases hSeen with hn | ⟨y, hy, he⟩
        · obtain ⟨z, hz, hKnown⟩ := hIncident x hx hn
          exact ⟨z, hz, Or.inl hKnown⟩
        · obtain rfl : y = x := f.injective he
          exact ⟨v, SimpleGraph.Adj.symm hy, Or.inl hName⟩
      have hRest := ih (some neighbors) enlarged hNextRange hNextIncident
      have hSize := extend_card G f root v known cap hRoot hDegree hIncident hName
      change enlarged.ncard ≤ known.ncard + cap at hSize
      simp only [simulate, ite_eq_left hName, answer_at_name, List.foldl_cons, sentNames,
        List.length_cons, show f '' G.neighborSet v = neighbors from rfl, hNext, Nat.mul_succ]
      exact hRest.trans (by omega)
    · simpa only [simulate, ite_eq_right hName, List.foldl_cons, namesAfter, sentNames]
        using ih none known hRange hIncident

/-- A known-name exploration starting at one root discovers at most `cap` new names
per actual oracle call when the root degree is at most `cap` and every other degree
is at most `cap + 1`. -/
theorem known_names_card_bound [Finite N] (G : SimpleGraph V) (f : V ↪ N) (root : V) (cap : ℕ)
    (hRoot : (G.neighborSet root).ncard ≤ cap)
    (hDegree : ∀ x, (G.neighborSet x).ncard ≤ cap + 1)
    (p : Protocol N) :
    let record := simulate (fun n => nameReply G n f) p {f root}
    let finalNames := record.foldl (fun seen entry => namesAfter seen entry.1 entry.2) {f root}
    let seenCount := finalNames.ncard
    seenCount ≤ 1 + cap * (sentNames {f root} record).length := by
  classical
  simpa only [Set.ncard_singleton] using
    all_known_card G f root cap hRoot hDegree p {f root}
      (Set.singleton_subset_iff.mpr ⟨root, rfl⟩)
      (fun v hNe hMem => (hNe (f.injective (Set.mem_singleton_iff.mp hMem))).elim)

end D5.S3.Combinatorics.Graph.Queries.KnownNameExplorationSize

/- GID: D5/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualJointEndpointPairs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual three-path replacement removes precisely the disjoint old distinguished endpoint pair and inserts the three new endpoint pairs. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

noncomputable def endpointPairs (pieces : List (Piece G)) : Finset (Sym2 V) := by
  classical
  exact (pieces.map fun p => s(p.start, p.finish)).toFinset

private theorem actual_distinguished_pair_absent_from_rest {ℓ z : V}
    (d : G.Walk ℓ z) (rest : List (Piece G))
    (hn : (d.support ++ rest.flatMap fun p => p.walk.support).Nodup) :
    s(ℓ, z) ∉ endpointPairs rest := by
  classical
  have hd := (List.nodup_append'.mp hn).2.2
  intro he
  obtain ⟨p, hp, he⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  have hℓ : ℓ ∈ p.walk.support := by
    rcases Sym2.eq_iff.mp he with ⟨hs, _⟩ | ⟨_, hf⟩
    · exact hs ▸ p.walk.start_mem_support
    · exact hf ▸ p.walk.end_mem_support
  exact List.disjoint_left.mp hd d.start_mem_support
    (List.mem_flatMap.mpr ⟨p, hp, hℓ⟩)

/-- Actual new walks update the complete old endpoint-pair set by deleting
the distinguished actual path and adding their three actual endpoint pairs.
No target pairing relation is supplied. -/
theorem actual_three_path_endpoint_update {ℓ z ℓ₀ r₀ ℓ₁ r₁ : V}
    (d : G.Walk ℓ z) (rest : List (Piece G))
    (hn : (d.support ++ rest.flatMap fun p => p.walk.support).Nodup)
    (new₀ : G.Walk z ℓ₀) (new₁ : G.Walk r₀ ℓ₁) (new₂ : G.Walk r₁ ℓ) :
    endpointPairs ([⟨z, ℓ₀, new₀⟩, ⟨r₀, ℓ₁, new₁⟩, ⟨r₁, ℓ, new₂⟩] ++ rest) =
      (endpointPairs (⟨ℓ, z, d⟩ :: rest)).erase s(ℓ, z) ∪
        {s(z, ℓ₀), s(r₀, ℓ₁), s(r₁, ℓ)} := by
  classical
  have hnot := actual_distinguished_pair_absent_from_rest d rest hn
  have herase : (endpointPairs (⟨ℓ, z, d⟩ :: rest)).erase s(ℓ, z) =
      endpointPairs rest := by
    simp only [endpointPairs, List.map_cons, List.toFinset_cons]
    change (insert s(ℓ, z) (endpointPairs rest)).erase s(ℓ, z) = endpointPairs rest
    exact Finset.erase_insert hnot
  rw [herase]
  ext e
  simp only [endpointPairs, List.map_append, List.map_cons, List.map_nil,
    List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    or_false]
  tauto

#print axioms actual_three_path_endpoint_update

end D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs

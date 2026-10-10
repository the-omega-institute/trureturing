/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverageBoundNonstem
   mirror-E: none(waiver:finite-counting)
   anchors: []
   utility: none
   digest: Self-critical dominating vertices admit neighbour-replacement injections. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.DominatingSetAverage
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Critical vertices without a private neighbour outside the set. -/
noncomputable def selfCritical (S : Finset V) : Finset V :=
  criticalVertices G S \ externallyCritical G S

/-- A deletion can fail away from the deleted vertex only at a private neighbour. -/
theorem private_of_not_dominated_erase (S : Finset V) (v u : V)
    (hd : G.IsDominating (S : Set V)) (hv : v ∈ S) (huv : u ≠ v)
    (hn : ¬ (u ∈ S.erase v ∨ ∃ w ∈ S.erase v, G.Adj u w)) :
    u ∈ privateNeighbors G S ∧ G.Adj v u := by
  classical
  have hus : u ∉ S := by
    intro hu
    exact hn (Or.inl (mem_erase.mpr ⟨huv, hu⟩))
  obtain ⟨w, hw, huw⟩ := (hd u).resolve_left hus
  have hwv : w = v := by
    by_contra hne
    exact hn (Or.inr ⟨w, mem_erase.mpr ⟨hne, hw⟩, huw⟩)
  subst w
  have heq : S.filter (G.Adj u) = {v} := by
    ext w
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hw, huw⟩
      by_contra hne
      exact hn (Or.inr ⟨w, mem_erase.mpr ⟨hne, hw⟩, huw⟩)
    · rintro rfl
      exact ⟨hv, huw⟩
  refine ⟨mem_filter.mpr ⟨mem_univ u, hus, ?_⟩, G.adj_symm huw⟩
  simp [heq]

/-- Deleting a self-critical vertex leaves every other vertex dominated. -/
theorem selfCritical_erase_dominates_other (S : Finset V) (v : V)
    (hd : G.IsDominating (S : Set V)) (hv : v ∈ selfCritical G S) :
    ∀ u, u ≠ v → u ∈ S.erase v ∨ ∃ w ∈ S.erase v, G.Adj u w := by
  classical
  have hvS := (mem_filter.mp (mem_sdiff.mp hv).1).1
  intro u huv
  by_contra hn
  have hp := private_of_not_dominated_erase G S v u hd hvS huv hn
  exact (mem_sdiff.mp hv).2 (mem_filter.mpr
    ⟨(mem_sdiff.mp hv).1, u, hp.1, hp.2⟩)

/-- A self-critical vertex has no selected neighbour. -/
theorem selfCritical_no_selected_neighbor (S : Finset V) (v : V)
    (hd : G.IsDominating (S : Set V)) (hv : v ∈ selfCritical G S) :
    ∀ w ∈ S, ¬ G.Adj v w := by
  classical
  intro w hw hAdj
  have hne : w ≠ v := fun he => G.ne_of_adj hAdj he.symm
  have hd' : G.IsDominating (S.erase v : Set V) := by
    intro u
    by_cases huv : u = v
    · subst u
      exact Or.inr ⟨w, mem_erase.mpr ⟨hne, hw⟩, hAdj⟩
    · exact selfCritical_erase_dominates_other G S v hd hv u huv
  exact (mem_filter.mp (mem_sdiff.mp hv).1).2 hd'

/-- Replacing a self-critical vertex by any nonempty collection of its neighbours preserves domination. -/
theorem selfCritical_neighbor_replacement (S T : Finset V) (v : V)
    (hd : G.IsDominating (S : Set V)) (hv : v ∈ selfCritical G S)
    (hT : T.Nonempty) (hAdj : ∀ w ∈ T, G.Adj v w) :
    G.IsDominating ((S.erase v ∪ T : Finset V) : Set V) := by
  classical
  intro u
  by_cases huv : u = v
  · subst u
    obtain ⟨w, hw⟩ := hT
    exact Or.inr ⟨w, mem_union_right _ hw, hAdj w hw⟩
  · rcases selfCritical_erase_dominates_other G S v hd hv u huv with hu | ⟨w, hw, huw⟩
    · exact Or.inl (mem_union_left _ hu)
    · exact Or.inr ⟨w, mem_union_left _ hw, huw⟩

/-- For a fixed vertex, deletion followed by a fixed nonempty neighbour insertion is injective. -/
theorem selfCritical_neighbor_replacement_injective (T : Finset V) (v : V)
    (hAdj : ∀ w ∈ T, G.Adj v w)
    (S₁ S₂ : Finset V)
    (hd₁ : G.IsDominating (S₁ : Set V)) (hd₂ : G.IsDominating (S₂ : Set V))
    (hv₁ : v ∈ selfCritical G S₁) (hv₂ : v ∈ selfCritical G S₂)
    (heq : S₁.erase v ∪ T = S₂.erase v ∪ T) : S₁ = S₂ := by
  classical
  have hvS₁ := (mem_filter.mp (mem_sdiff.mp hv₁).1).1
  have hvS₂ := (mem_filter.mp (mem_sdiff.mp hv₂).1).1
  have hdT₁ : Disjoint S₁ T := by
    apply disjoint_left.mpr
    intro w hw₁ hwT
    exact selfCritical_no_selected_neighbor G S₁ v hd₁ hv₁ w hw₁ (hAdj w hwT)
  have hdT₂ : Disjoint S₂ T := by
    apply disjoint_left.mpr
    intro w hw₂ hwT
    exact selfCritical_no_selected_neighbor G S₂ v hd₂ hv₂ w hw₂ (hAdj w hwT)
  have herase : S₁.erase v = S₂.erase v := by
    ext w
    have hmem := congrArg (fun A : Finset V => w ∈ A) heq
    have h₁ : w ∈ S₁.erase v → w ∉ T := by
      intro hw hT
      exact disjoint_left.mp hdT₁ (mem_of_mem_erase hw) hT
    have h₂ : w ∈ S₂.erase v → w ∉ T := by
      intro hw hT
      exact disjoint_left.mp hdT₂ (mem_of_mem_erase hw) hT
    simp only [mem_union] at hmem
    constructor
    · intro hw
      have := hmem.mp (Or.inl hw)
      exact this.resolve_right (h₁ hw)
    · intro hw
      have := hmem.mpr (Or.inl hw)
      exact this.resolve_right (h₂ hw)
  calc
    S₁ = insert v (S₁.erase v) := (insert_erase hvS₁).symm
    _ = insert v (S₂.erase v) := by rw [herase]
    _ = S₂ := insert_erase hvS₂

/-- The dominating sets in which a fixed vertex is self-critical. -/
noncomputable def selfCriticalSets (v : V) : Finset (Finset V) :=
  (domSets G).filter fun S => v ∈ selfCritical G S

/-- The dominating sets omitting a vertex and selecting at least two of its neighbours. -/
noncomputable def multiNeighborSets (v : V) : Finset (Finset V) :=
  (domSets G).filter fun S => v ∉ S ∧ 2 ≤ (S.filter (G.Adj v)).card

/-- Insert the entire open neighbourhood after deleting a self-critical vertex. -/
noncomputable def neighborReplacement (v : V) (S : Finset V) : Finset V := by
  classical
  exact S.erase v ∪ G.neighborFinset v

theorem neighborReplacement_mem (v : V) (hvdeg : 2 ≤ G.degree v)
    (S : Finset V) (hS : S ∈ selfCriticalSets G v) :
    neighborReplacement G v S ∈ multiNeighborSets G v := by
  classical
  have hd := mem_domSets.mp (mem_filter.mp hS).1
  have hv := (mem_filter.mp hS).2
  have hne : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    omega
  refine mem_filter.mpr ⟨mem_domSets.mpr
    (selfCritical_neighbor_replacement G S (G.neighborFinset v) v hd hv hne
      (by simpa only [SimpleGraph.mem_neighborFinset] using fun w => fun h => h)), ?_⟩
  constructor
  · simp [neighborReplacement]
  · have hsub : G.neighborFinset v ⊆ (neighborReplacement G v S).filter (G.Adj v) := by
      intro w hw
      exact mem_filter.mpr ⟨mem_union_right _ hw, (G.mem_neighborFinset v w).mp hw⟩
    exact hvdeg.trans (by simpa using Finset.card_le_card hsub)

theorem selfCriticalSets_card_le_multiNeighborSets (v : V) (hvdeg : 2 ≤ G.degree v) :
    (selfCriticalSets G v).card ≤ (multiNeighborSets G v).card := by
  classical
  apply Finset.card_le_card_of_injOn (neighborReplacement G v)
  · intro S hS
    exact neighborReplacement_mem G v hvdeg S hS
  · intro S₁ hS₁ S₂ hS₂ heq
    exact selfCritical_neighbor_replacement_injective G (G.neighborFinset v) v
      (by simpa only [SimpleGraph.mem_neighborFinset] using fun w => fun h => h)
      S₁ S₂ (mem_domSets.mp (mem_filter.mp hS₁).1)
      (mem_domSets.mp (mem_filter.mp hS₂).1)
      (mem_filter.mp hS₁).2 (mem_filter.mp hS₂).2 heq

/-- Neighbours together with vertices outside their closed neighbourhoods dominate the graph. -/
noncomputable def neighborWitness (v : V) : Finset V := by
  classical
  exact G.neighborFinset v ∪ univ.filter fun x =>
    x ≠ v ∧ ∀ u ∈ G.neighborFinset v, ¬ G.Adj x u

theorem neighborWitness_mem (v : V) (hvdeg : 2 ≤ G.degree v) :
    neighborWitness G v ∈ multiNeighborSets G v := by
  classical
  have hne : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    omega
  have hd : G.IsDominating (neighborWitness G v : Set V) := by
    intro x
    by_cases hx : x ∈ neighborWitness G v
    · exact Or.inl hx
    by_cases hxv : x = v
    · subst x
      obtain ⟨u, hu⟩ := hne
      exact Or.inr ⟨u, mem_union_left _ hu, (G.mem_neighborFinset v u).mp hu⟩
    · have hh : ¬ (∀ u ∈ G.neighborFinset v, ¬G.Adj x u) := by
        intro h
        exact hx (mem_union_right _ (mem_filter.mpr ⟨mem_univ x, hxv, h⟩))
      push Not at hh
      obtain ⟨u, hu, hxu⟩ := hh
      exact Or.inr ⟨u, mem_union_left _ hu, hxu⟩
  refine mem_filter.mpr ⟨mem_domSets.mpr hd, ?_⟩
  constructor
  · simp [neighborWitness]
  · have hsub : G.neighborFinset v ⊆ (neighborWitness G v).filter (G.Adj v) := by
      intro w hw
      exact mem_filter.mpr ⟨mem_union_left _ hw, (G.mem_neighborFinset v w).mp hw⟩
    exact hvdeg.trans (by simpa using Finset.card_le_card hsub)

theorem neighborWitness_not_image (v : V) (hvdeg : 2 ≤ G.degree v)
    (S : Finset V) (hS : S ∈ selfCriticalSets G v) :
    neighborReplacement G v S ≠ neighborWitness G v := by
  classical
  intro heq
  have hd := mem_domSets.mp (mem_filter.mp hS).1
  have hv := (mem_filter.mp hS).2
  have hne : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨u, hu⟩ := hne
  have huv : u ≠ v := (G.ne_of_adj ((G.mem_neighborFinset v u).mp hu)).symm
  have hout (w : V) (hw : w ∈ S.erase v) :
      w ≠ v ∧ ∀ t ∈ G.neighborFinset v, ¬G.Adj w t := by
    have hQ : w ∈ neighborWitness G v := by
      rw [← heq]
      exact mem_union_left _ hw
    have hn : w ∉ G.neighborFinset v := by
      intro hn
      exact selfCritical_no_selected_neighbor G S v hd hv w (mem_of_mem_erase hw)
        ((G.mem_neighborFinset v w).mp hn)
    exact (mem_filter.mp ((mem_union.mp hQ).resolve_left hn)).2
  rcases selfCritical_erase_dominates_other G S v hd hv u huv with hus | ⟨w, hw, huw⟩
  · exact selfCritical_no_selected_neighbor G S v hd hv u (mem_of_mem_erase hus)
      ((G.mem_neighborFinset v u).mp hu)
  · exact (hout w hw).2 u hu (G.adj_symm huw)

/-- Beaton–Cameron's strict self-critical bound at every vertex of degree at least two. -/
theorem selfCriticalSets_card_lt_multiNeighborSets (v : V) (hvdeg : 2 ≤ G.degree v) :
    (selfCriticalSets G v).card < (multiNeighborSets G v).card := by
  classical
  have hi : Set.InjOn (neighborReplacement G v) (selfCriticalSets G v : Set (Finset V)) := by
    intro S₁ hS₁ S₂ hS₂ heq
    exact selfCritical_neighbor_replacement_injective G (G.neighborFinset v) v
      (by simpa only [SimpleGraph.mem_neighborFinset] using fun w => fun h => h)
      S₁ S₂ (mem_domSets.mp (mem_filter.mp hS₁).1)
      (mem_domSets.mp (mem_filter.mp hS₂).1)
      (mem_filter.mp hS₁).2 (mem_filter.mp hS₂).2 heq
  have hsub : (selfCriticalSets G v).image (neighborReplacement G v) ⊆ multiNeighborSets G v := by
    intro S hS
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hS
    exact neighborReplacement_mem G v hvdeg T hT
  have hn : neighborWitness G v ∉ (selfCriticalSets G v).image (neighborReplacement G v) := by
    intro h
    obtain ⟨S, hS, heq⟩ := mem_image.mp h
    exact neighborWitness_not_image G v hvdeg S hS heq
  have hlt : (selfCriticalSets G v).image (neighborReplacement G v) ⊂ multiNeighborSets G v :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro he
      exact hn (he.symm ▸ neighborWitness_mem G v hvdeg)⟩
  rw [← card_image_of_injOn hi]
  exact card_lt_card hlt

end D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem

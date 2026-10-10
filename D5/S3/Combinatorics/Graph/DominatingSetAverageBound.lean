/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverageBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverageBound
   mirror-E: none(waiver:finite-domination-bound)
   anchors: []
   utility: none
   digest: The average cardinality of an isolate-free graph's dominating sets is at most two thirds of its order. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem
import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundStem

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverageBound

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.DominatingSetAverage
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundStem

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Blocks meeting the complement of a given set. -/
noncomputable def activeBlocks (S : Finset V) : Finset (Finset V) :=
  (stemBlocks G).filter fun b => ¬ b ⊆ S

/-- Vertices in active leaf-stem blocks. -/
noncomputable def removed (S : Finset V) : Finset V :=
  (activeBlocks G S).biUnion id

/-- The vertices outside all active blocks. -/
noncomputable def residual (S : Finset V) : Finset V := univ \ removed G S

/-- Vertices in no leaf-stem block. -/
noncomputable def core : Finset V := univ \ (stemBlocks G).biUnion id

/-- An outside private neighbour of a residual selected vertex is itself residual. -/
theorem privateNeighbor_residual (S : Finset V) (v u : V)
    (hd : G.IsDominating (S : Set V)) (hvS : v ∈ S)
    (hvR : v ∈ residual G S) (hu : u ∈ privateNeighbors G S) (hvu : G.Adj v u) :
    u ∈ residual G S := by
  classical
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro huD
  obtain ⟨b, hb, hub⟩ := mem_biUnion.mp huD
  obtain ⟨s, hLs, hsb⟩ := (mem_stemBlocks G).mp (mem_filter.mp hb).1
  subst b
  have huS := (mem_filter.mp hu).2.1
  have huone := (mem_filter.mp hu).2.2
  have hvs : v ∈ (S.filter (G.Adj u)) := mem_filter.mpr ⟨hvS, G.adj_symm hvu⟩
  have hcard : (S.filter (G.Adj u)).card ≤ 1 := Nat.le_of_eq huone
  have hvremoved : v ∈ removed G S := by
    by_cases hus : u = s
    · subst u
      obtain ⟨x, hxL⟩ := hLs
      have hxS := leafNeighbors_subset_of_stem_notMem G hd huS hxL
      have hxs : x ∈ S.filter (G.Adj s) :=
        mem_filter.mpr ⟨hxS, (mem_leafNeighbors.mp hxL).1⟩
      have hveq : v = x := Finset.card_le_one.mp hcard v hvs x hxs
      apply mem_biUnion.mpr
      exact ⟨stemBlock G s, hb, hveq.symm ▸ mem_insert_of_mem hxL⟩
    · have huL : u ∈ leafNeighbors G s := (mem_insert.mp hub).resolve_left hus
      have hveq : v = s := leaf_neighbor_only G huL (G.adj_symm hvu)
      apply mem_biUnion.mpr
      exact ⟨stemBlock G s, hb, hveq.symm ▸ mem_insert_self _ _⟩
  exact (mem_sdiff.mp hvR).2 hvremoved

/-- The private-neighbour injection remains valid after deleting complete stem blocks. -/
theorem externallyCritical_residual_card_le (S : Finset V)
    (hd : G.IsDominating (S : Set V)) :
    (externallyCritical G S ∩ residual G S).card ≤
      (privateNeighbors G S ∩ residual G S).card := by
  classical
  by_cases hR : residual G S = univ
  · simpa only [hR, inter_univ] using externallyCritical_card_le G S
  have hex (v : V) (hv : v ∈ externallyCritical G S ∩ residual G S) :
      ∃ u ∈ privateNeighbors G S ∩ residual G S, G.Adj v u := by
    obtain ⟨u, hu, hvu⟩ := (mem_filter.mp (mem_inter.mp hv).1).2
    have hvS := (mem_filter.mp (mem_filter.mp (mem_inter.mp hv).1).1).1
    exact ⟨u, mem_inter.mpr ⟨hu,
      privateNeighbor_residual G S v u hd hvS (mem_inter.mp hv).2 hu hvu⟩, hvu⟩
  let f (v : V) := if hv : v ∈ externallyCritical G S ∩ residual G S then
    (hex v hv).choose else v
  apply Finset.card_le_card_of_injOn f
  · intro v hv
    change f v ∈ privateNeighbors G S ∩ residual G S
    dsimp only [f]
    split_ifs with h
    · exact (hex v h).choose_spec.1
    · exact (h hv).elim
  · intro v hv w hw heq
    have hfv : f v = (hex v hv).choose := by
      dsimp only [f]; split_ifs with h
      · rfl
      · exact (h hv).elim
    have hfw : f w = (hex w hw).choose := by
      dsimp only [f]; split_ifs with h
      · rfl
      · exact (h hw).elim
    have huv := (hex v hv).choose_spec.2
    have huw := (hex w hw).choose_spec.2
    have huone := (mem_filter.mp (mem_inter.mp (hex v hv).choose_spec.1).1).2.2
    have hvs := (mem_filter.mp (mem_filter.mp (mem_inter.mp hv).1).1).1
    have hws := (mem_filter.mp (mem_filter.mp (mem_inter.mp hw).1).1).1
    have hone : (S.filter (G.Adj (f v))).card ≤ 1 := by rw [hfv]; omega
    apply (Finset.card_le_one.mp hone) v (mem_filter.mpr ⟨hvs, by rw [hfv]; exact G.adj_symm huv⟩)
      w (mem_filter.mpr ⟨hws, ?_⟩)
    rw [heq, hfw]
    exact G.adj_symm huw

theorem core_subset_residual (S : Finset V) : core G ⊆ residual G S := by
  classical
  intro v hv
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro h
  obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp h
  exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨b, (mem_filter.mp hb).1, hvb⟩)

/-- A self-critical residual vertex belongs to no stem block, active or inactive. -/
theorem selfCritical_residual_mem_core (S : Finset V) (v : V)
    (hd : G.IsDominating (S : Set V))
    (hv : v ∈ selfCritical G S ∩ residual G S) : v ∈ core G := by
  classical
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro h
  obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp h
  have hfull : b ⊆ S := by
    by_contra hn
    exact (mem_sdiff.mp (mem_inter.mp hv).2).2
      (mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hb, hn⟩, hvb⟩)
  obtain ⟨s, hs, hsb⟩ := (mem_stemBlocks G).mp hb
  subst b
  rcases mem_insert.mp hvb with hvs | hvL
  · subst v
    obtain ⟨x, hx⟩ := hs
    exact selfCritical_no_selected_neighbor G S s hd (mem_inter.mp hv).1 x
      (hfull (mem_insert_of_mem hx)) (mem_leafNeighbors.mp hx).1
  · exact selfCritical_no_selected_neighbor G S v hd (mem_inter.mp hv).1 s
      (hfull (mem_insert_self _ _)) (G.adj_symm (mem_leafNeighbors.mp hvL).1)

theorem selfCritical_inter_residual (S : Finset V)
    (hd : G.IsDominating (S : Set V)) :
    selfCritical G S ∩ residual G S = selfCritical G S ∩ core G := by
  ext v
  constructor
  · intro hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1, selfCritical_residual_mem_core G S v hd hv⟩
  · intro hv
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1, core_subset_residual G S (mem_inter.mp hv).2⟩

/-- With no isolated vertices, every vertex outside the stem blocks has degree at least two. -/
theorem core_degree_ge_two (hpos : ∀ x, 0 < G.degree x) (v : V) (hv : v ∈ core G) :
    2 ≤ G.degree v := by
  classical
  have hn : ¬G.degree v = 1 := by
    intro hd
    exact (mem_sdiff.mp hv).2 (vertex_mem_stemBlocks_of_leaf G hd)
  have hp := hpos v
  omega

/-- Summing set intersections counts the same incidences vertex by vertex. -/
theorem sum_inter_card (F : Finset (Finset V)) (C : Finset V)
    (a : Finset V → Finset V) :
    (∑ S ∈ F, (a S ∩ C).card) =
      ∑ v ∈ C, (F.filter fun S => v ∈ a S).card := by
  classical
  have hcard (S : Finset V) : (a S ∩ C).card = ∑ v ∈ C, if v ∈ a S then 1 else 0 := by
    rw [← sum_filter, ← card_eq_sum_ones]
    congr 1
    ext v
    simp [and_comm]
  simp_rw [hcard]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter, ← card_eq_sum_ones]

/-- The self-critical residual incidence count is bounded by the multi-neighbour core count. -/
theorem selfCritical_core_total_le (hpos : ∀ x, 0 < G.degree x) :
    (∑ S ∈ domSets G, (selfCritical G S ∩ core G).card) ≤
      ∑ v ∈ core G, (multiNeighborSets G v).card := by
  rw [sum_inter_card]
  apply sum_le_sum
  intro v hv
  exact selfCriticalSets_card_le_multiNeighborSets G v (core_degree_ge_two G hpos v hv)

/-- Omitted vertices with at least two selected neighbours. -/
noncomputable def multiNeighbors (S : Finset V) : Finset V :=
  univ.filter fun v => v ∉ S ∧ 2 ≤ (S.filter (G.Adj v)).card

theorem multiNeighbors_core_total :
    (∑ S ∈ domSets G, (multiNeighbors G S ∩ core G).card) =
      ∑ v ∈ core G, (multiNeighborSets G v).card := by
  rw [sum_inter_card]
  apply sum_congr rfl
  intro v _
  congr 1
  ext S
  simp [multiNeighbors, multiNeighborSets]

theorem residual_critical_partition (S : Finset V) :
    (criticalVertices G S ∩ residual G S).card =
      (externallyCritical G S ∩ residual G S).card +
      (selfCritical G S ∩ residual G S).card := by
  classical
  have hsub : externallyCritical G S ∩ residual G S ⊆ criticalVertices G S ∩ residual G S := by
    intro v hv
    exact mem_inter.mpr ⟨(mem_filter.mp (mem_inter.mp hv).1).1, (mem_inter.mp hv).2⟩
  have heq : (criticalVertices G S ∩ residual G S) \ (externallyCritical G S ∩ residual G S) =
      selfCritical G S ∩ residual G S := by
    ext v
    simp only [selfCritical, mem_sdiff, mem_inter]
    tauto
  have hc := card_sdiff_add_card_eq_card hsub
  rw [heq] at hc
  omega

theorem residual_omitted_partition_le (S : Finset V) :
    (privateNeighbors G S ∩ residual G S).card +
      (multiNeighbors G S ∩ core G).card ≤ (residual G S \ S).card := by
  classical
  have hdis : Disjoint (privateNeighbors G S ∩ residual G S) (multiNeighbors G S ∩ core G) := by
    apply disjoint_left.mpr
    intro v hv₁ hv₂
    have hc₁ := (mem_filter.mp (mem_inter.mp hv₁).1).2.2
    have hc₂ := (mem_filter.mp (mem_inter.mp hv₂).1).2.2
    omega
  rw [← card_union_of_disjoint hdis]
  apply card_le_card
  intro v hv
  rcases mem_union.mp hv with h₁ | h₂
  · exact mem_sdiff.mpr ⟨(mem_inter.mp h₁).2,
      (mem_filter.mp (mem_inter.mp h₁).1).2.1⟩
  · exact mem_sdiff.mpr ⟨core_subset_residual G S (mem_inter.mp h₂).2,
      (mem_filter.mp (mem_inter.mp h₂).1).2.1⟩

theorem residual_total_le (hpos : ∀ x, 0 < G.degree x) :
    (∑ S ∈ domSets G, (criticalVertices G S ∩ residual G S).card) ≤
      ∑ S ∈ domSets G, (residual G S \ S).card := by
  classical
  have hext :
      (∑ S ∈ domSets G, (externallyCritical G S ∩ residual G S).card) ≤
        ∑ S ∈ domSets G, (privateNeighbors G S ∩ residual G S).card := by
    apply sum_le_sum
    intro S hS
    exact externallyCritical_residual_card_le G S (mem_domSets.mp hS)
  have hself :
      (∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card) ≤
        ∑ S ∈ domSets G, (multiNeighbors G S ∩ core G).card := by
    have he : (∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card) =
        ∑ S ∈ domSets G, (selfCritical G S ∩ core G).card := by
      apply sum_congr rfl
      intro S hS
      rw [selfCritical_inter_residual G S (mem_domSets.mp hS)]
    rw [he, multiNeighbors_core_total]
    exact selfCritical_core_total_le G hpos
  calc
    _ = (∑ S ∈ domSets G, (externallyCritical G S ∩ residual G S).card) +
        ∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card := by
      simp_rw [residual_critical_partition]; rw [sum_add_distrib]
    _ ≤ (∑ S ∈ domSets G, (privateNeighbors G S ∩ residual G S).card) +
        ∑ S ∈ domSets G, (multiNeighbors G S ∩ core G).card := Nat.add_le_add hext hself
    _ ≤ _ := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun S _ => residual_omitted_partition_le G S

/-- Cardinalities split over active blocks and the residual vertices. -/
theorem active_residual_count (S A : Finset V) :
    A.card = (∑ b ∈ activeBlocks G S, (A ∩ b).card) + (A ∩ residual G S).card := by
  classical
  have hdis : (activeBlocks G S : Set (Finset V)).PairwiseDisjoint (fun b => A ∩ b) := by
    intro b hb c hc hne
    have hd := stemBlocks_pairwiseDisjoint G (mem_filter.mp hb).1 (mem_filter.mp hc).1 hne
    exact hd.mono inter_subset_right inter_subset_right
  have heq : (activeBlocks G S).biUnion (fun b => A ∩ b) = A ∩ removed G S := by
    ext v
    simp only [mem_biUnion, mem_inter, removed]
    constructor
    · rintro ⟨b, hb, hvA, hvb⟩
      exact ⟨hvA, b, hb, hvb⟩
    · rintro ⟨hvA, b, hb, hvb⟩
      exact ⟨b, hb, hvA, hvb⟩
  have hcard := card_biUnion hdis
  rw [heq] at hcard
  have hres : A ∩ residual G S = A \ removed G S := by
    ext v
    simp [residual]
  rw [← hcard, hres]
  exact (card_inter_add_card_sdiff A (removed G S)).symm

theorem active_block_total_le :
    (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (criticalVertices G S ∩ b).card) ≤
      ∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (b \ S).card := by
  classical
  simp only [activeBlocks, sum_filter]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_le_sum
  intro b hb
  obtain ⟨s, hs, hsb⟩ := (mem_stemBlocks G).mp hb
  subst b
  simpa only [activeStemFamily, sum_filter] using activeStemFamily_bound G s hs

/-- The total critical incidence count does not exceed the total omitted incidence count. -/
theorem critical_total_le_omitted_total (hpos : ∀ x, 0 < G.degree x) :
    (∑ S ∈ domSets G, (criticalVertices G S).card) ≤
      ∑ S ∈ domSets G, (univ \ S).card := by
  classical
  have hc : (∑ S ∈ domSets G, (criticalVertices G S).card) =
      (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (criticalVertices G S ∩ b).card) +
      ∑ S ∈ domSets G, (criticalVertices G S ∩ residual G S).card := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun S _ => active_residual_count G S (criticalVertices G S)
  have ho : (∑ S ∈ domSets G, (univ \ S).card) =
      (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (b \ S).card) +
      ∑ S ∈ domSets G, (residual G S \ S).card := by
    have hpoint (S : Finset V) : (univ \ S).card =
        (∑ b ∈ activeBlocks G S, (b \ S).card) + (residual G S \ S).card := by
      have h := active_residual_count G S (univ \ S)
      have hset (b : Finset V) : (univ \ S) ∩ b = b \ S := by ext v; simp [and_comm]
      have hr : (univ \ S) ∩ residual G S = residual G S \ S := by ext v; simp [and_comm]
      simpa only [hset, hr] using h
    simp_rw [hpoint]; rw [sum_add_distrib]
  rw [hc, ho]
  exact Nat.add_le_add (active_block_total_le G) (residual_total_le G hpos)

/-- Beaton–Cameron's global inequality, including the empty graph. -/
theorem avd_le_two_thirds (hpos : ∀ x, 0 < G.degree x) :
    avd G ≤ (2 * Fintype.card V : ℚ) / 3 := by
  classical
  have hc := critical_total_identity G
  have hle := critical_total_le_omitted_total G hpos
  have ho : (∑ S ∈ domSets G, (univ \ S).card) +
      (∑ S ∈ domSets G, S.card) = Fintype.card V * (domSets G).card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _S ∈ domSets G, Fintype.card V := by
        apply sum_congr rfl
        intro S _
        simpa using card_sdiff_add_card_eq_card (subset_univ S)
      _ = _ := by simp [Nat.mul_comm]
  have hn : 3 * (∑ S ∈ domSets G, S.card) ≤ 2 * (Fintype.card V * (domSets G).card) := by
    omega
  have hq : 3 * (∑ S ∈ domSets G, (S.card : ℚ)) ≤
      2 * ((Fintype.card V : ℚ) * (domSets G).card) := by
    exact_mod_cast hn
  have hp : (0 : ℚ) < (domSets G).card := by exact_mod_cast domSets_card_pos G
  rw [avd, familyAverage, div_le_iff₀ hp]
  linarith

end D5.S3.Combinatorics.Graph.DominatingSetAverageBound

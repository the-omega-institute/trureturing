/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverageBoundEquality
   mirror-E: none(waiver:finite-domination-equality)
   anchors: []
   utility: none
   digest: Equality in the two-thirds dominating-set average bound characterizes star-like graphs. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBound

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverageBoundEquality

open Finset
open scoped Classical
open D5.S3.Combinatorics.Graph.DominatingSetAverage
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundCounting
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundNonstem
open D5.S3.Combinatorics.Graph.DominatingSetAverageBoundStem
open D5.S3.Combinatorics.Graph.DominatingSetAverageBound

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- A vertex outside all stem blocks makes the residual inequality strict. -/
theorem residual_total_lt_of_core_nonempty (hpos : ∀ x, 0 < G.degree x)
    (hcore : (core G).Nonempty) :
    (∑ S ∈ domSets G, (criticalVertices G S ∩ residual G S).card) <
      ∑ S ∈ domSets G, (residual G S \ S).card := by
  classical
  have hext :
      (∑ S ∈ domSets G, (externallyCritical G S ∩ residual G S).card) ≤
        ∑ S ∈ domSets G, (privateNeighbors G S ∩ residual G S).card := by
    apply sum_le_sum
    intro S hS
    exact externallyCritical_residual_card_le G S (mem_domSets.mp hS)
  have hself :
      (∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card) <
        ∑ S ∈ domSets G, (multiNeighbors G S ∩ core G).card := by
    have he : (∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card) =
        ∑ S ∈ domSets G, (selfCritical G S ∩ core G).card := by
      apply sum_congr rfl
      intro S hS
      rw [selfCritical_inter_residual G S (mem_domSets.mp hS)]
    rw [he, multiNeighbors_core_total, sum_inter_card]
    apply sum_lt_sum
    · intro v hv
      exact selfCriticalSets_card_le_multiNeighborSets G v (core_degree_ge_two G hpos v hv)
    · obtain ⟨v, hv⟩ := hcore
      exact ⟨v, hv, selfCriticalSets_card_lt_multiNeighborSets G v
        (core_degree_ge_two G hpos v hv)⟩
  calc
    _ = (∑ S ∈ domSets G, (externallyCritical G S ∩ residual G S).card) +
        ∑ S ∈ domSets G, (selfCritical G S ∩ residual G S).card := by
      simp_rw [residual_critical_partition]; rw [sum_add_distrib]
    _ < (∑ S ∈ domSets G, (privateNeighbors G S ∩ residual G S).card) +
        ∑ S ∈ domSets G, (multiNeighbors G S ∩ core G).card := Nat.add_lt_add_of_le_of_lt hext hself
    _ ≤ _ := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun S _ => residual_omitted_partition_le G S

/-- A stem with at least three leaves makes the active-block inequality strict. -/
theorem active_block_total_lt_of_large_stem (s : V) (hs : 3 ≤ leafCount G s) :
    (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (criticalVertices G S ∩ b).card) <
      ∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (b \ S).card := by
  classical
  simp only [activeBlocks, sum_filter]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_lt_sum
  · intro b hb
    obtain ⟨t, ht, htb⟩ := (mem_stemBlocks G).mp hb
    subst b
    simpa only [activeStemFamily, sum_filter] using activeStemFamily_bound G t ht
  · have hne : (leafNeighbors G s).Nonempty := by
      rw [← card_pos]
      change 0 < leafCount G s
      omega
    refine ⟨stemBlock G s, (mem_stemBlocks G).mpr ⟨s, hne, rfl⟩, ?_⟩
    simpa only [activeStemFamily, sum_filter] using activeStemFamily_strict G s hs

/-- Equality of averages is equality of the critical and omitted incidence counts. -/
theorem critical_total_eq_of_avd_eq
    (he : avd G = (2 * Fintype.card V : ℚ) / 3) :
    (∑ S ∈ domSets G, (criticalVertices G S).card) =
      ∑ S ∈ domSets G, (univ \ S).card := by
  classical
  have hc := critical_total_identity G
  have ho : (∑ S ∈ domSets G, (univ \ S).card) +
      (∑ S ∈ domSets G, S.card) = Fintype.card V * (domSets G).card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _S ∈ domSets G, Fintype.card V := by
        apply sum_congr rfl
        intro S _
        simpa using card_sdiff_add_card_eq_card (subset_univ S)
      _ = _ := by simp [Nat.mul_comm]
  have hp : (0 : ℚ) < (domSets G).card := by exact_mod_cast domSets_card_pos G
  have hq : 3 * (∑ S ∈ domSets G, (S.card : ℚ)) =
      2 * ((Fintype.card V : ℚ) * (domSets G).card) := by
    rw [avd, familyAverage, div_eq_iff (ne_of_gt hp)] at he
    linarith
  have hn : 3 * (∑ S ∈ domSets G, S.card) =
      2 * (Fintype.card V * (domSets G).card) := by exact_mod_cast hq
  omega

/-- Decomposition of the incidence difference into active and residual contributions. -/
theorem totals_decomposition :
    (∑ S ∈ domSets G, (criticalVertices G S).card) =
      (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (criticalVertices G S ∩ b).card) +
      ∑ S ∈ domSets G, (criticalVertices G S ∩ residual G S).card ∧
    (∑ S ∈ domSets G, (univ \ S).card) =
      (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (b \ S).card) +
      ∑ S ∈ domSets G, (residual G S \ S).card := by
  constructor
  · rw [← sum_add_distrib]
    exact sum_congr rfl fun S _ => active_residual_count G S (criticalVertices G S)
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    have h := active_residual_count G S (univ \ S)
    have hset (b : Finset V) : (univ \ S) ∩ b = b \ S := by ext v; simp [and_comm]
    have hr : (univ \ S) ∩ residual G S = residual G S \ S := by ext v; simp [and_comm]
    simpa only [hset, hr] using h

/-- Every equality graph is star-like. -/
theorem starLike_of_avd_eq_two_thirds (hpos : ∀ x, 0 < G.degree x)
    (he : avd G = (2 * Fintype.card V : ℚ) / 3) : StarLike G := by
  classical
  have htot := critical_total_eq_of_avd_eq G he
  have hdec := totals_decomposition G
  have hcore : core G = ∅ := by
    by_contra hn
    have hlt := residual_total_lt_of_core_nonempty G hpos (nonempty_iff_ne_empty.mpr hn)
    have hweak := active_block_total_le G
    omega
  have hsmall (s : V) : leafCount G s ≤ 2 := by
    by_contra hn
    have hs : 3 ≤ leafCount G s := by omega
    have hlt := active_block_total_lt_of_large_stem G s hs
    have hweak := residual_total_le G hpos
    omega
  intro v
  have hvU : v ∈ (stemBlocks G).biUnion id := by
    by_contra hn
    have hvcore : v ∈ core G := mem_sdiff.mpr ⟨mem_univ _, hn⟩
    rw [hcore] at hvcore
    exact Finset.notMem_empty _ hvcore
  obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hvU
  obtain ⟨s, hs, hsb⟩ := (mem_stemBlocks G).mp hb
  subst b
  rcases mem_insert.mp hvb with hvs | hvL
  · subst v
    have hp : 0 < leafCount G s := card_pos.mpr hs
    have hl := hsmall s
    exact Or.inr (by omega)
  · exact Or.inl (mem_leafNeighbors.mp hvL).2

/-- In a star-like graph every residual vertex of a selected set is selected. -/
theorem residual_subset_of_starLike (S : Finset V) (hstar : StarLike G) :
    residual G S ⊆ S := by
  classical
  intro v hv
  have hvall : v ∈ (stemBlocks G).biUnion id := by
    rcases hstar v with hl | hk
    · exact vertex_mem_stemBlocks_of_leaf G hl
    · have hp : (leafNeighbors G v).Nonempty := by
        rw [← card_pos]
        change 0 < leafCount G v
        omega
      exact vertex_mem_stemBlocks_of_stem G hp
  obtain ⟨b, hb, hvb⟩ := mem_biUnion.mp hvall
  have hfull : b ⊆ S := by
    by_contra hn
    exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨b, mem_filter.mpr ⟨hb, hn⟩, hvb⟩)
  exact hfull hvb

theorem active_block_total_eq_of_starLike (hstar : StarLike G) :
    (∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (criticalVertices G S ∩ b).card) =
      ∑ S ∈ domSets G, ∑ b ∈ activeBlocks G S, (b \ S).card := by
  classical
  simp only [activeBlocks, sum_filter]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  obtain ⟨s, hs, hsb⟩ := (mem_stemBlocks G).mp hb
  subst b
  have hk : leafCount G s = 1 ∨ leafCount G s = 2 := by
    rcases hstar s with hl | hk
    · have hle := leafCount_le_one_of_leaf G hl
      have hp : 0 < leafCount G s := card_pos.mpr hs
      exact Or.inl (by omega)
    · exact hk
  simpa only [activeStemFamily, sum_filter] using activeStemFamily_eq_of_starLike G s hstar hk

theorem critical_total_eq_of_starLike (hpos : ∀ x, 0 < G.degree x) (hstar : StarLike G) :
    (∑ S ∈ domSets G, (criticalVertices G S).card) =
      ∑ S ∈ domSets G, (univ \ S).card := by
  classical
  have ho : (∑ S ∈ domSets G, (residual G S \ S).card) = 0 := by
    apply sum_eq_zero
    intro S _
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (residual_subset_of_starLike G S hstar), card_empty]
  have hc : (∑ S ∈ domSets G, (criticalVertices G S ∩ residual G S).card) = 0 := by
    have h := residual_total_le G hpos
    rw [ho] at h
    omega
  have hactive := active_block_total_eq_of_starLike G hstar
  have hdec := totals_decomposition G
  omega

/-- Every star-like isolate-free graph attains the two-thirds bound. -/
theorem avd_eq_two_thirds_of_starLike (hpos : ∀ x, 0 < G.degree x) (hstar : StarLike G) :
    avd G = (2 * Fintype.card V : ℚ) / 3 := by
  classical
  have hc := critical_total_identity G
  have he := critical_total_eq_of_starLike G hpos hstar
  have ho : (∑ S ∈ domSets G, (univ \ S).card) +
      (∑ S ∈ domSets G, S.card) = Fintype.card V * (domSets G).card := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ _S ∈ domSets G, Fintype.card V := by
        apply sum_congr rfl
        intro S _
        simpa using card_sdiff_add_card_eq_card (subset_univ S)
      _ = _ := by simp [Nat.mul_comm]
  have hn : 3 * (∑ S ∈ domSets G, S.card) =
      2 * (Fintype.card V * (domSets G).card) := by omega
  have hq : 3 * (∑ S ∈ domSets G, (S.card : ℚ)) =
      2 * ((Fintype.card V : ℚ) * (domSets G).card) := by exact_mod_cast hn
  have hp : (0 : ℚ) < (domSets G).card := by exact_mod_cast domSets_card_pos G
  rw [avd, familyAverage, div_eq_iff (ne_of_gt hp)]
  linarith

/-- The equality characterization in Beaton–Cameron's Theorem 2.9. -/
theorem avd_eq_two_thirds_iff_starLike (hpos : ∀ x, 0 < G.degree x) :
    avd G = (2 * Fintype.card V : ℚ) / 3 ↔ StarLike G :=
  ⟨starLike_of_avd_eq_two_thirds G hpos, avd_eq_two_thirds_of_starLike G hpos⟩

end D5.S3.Combinatorics.Graph.DominatingSetAverageBoundEquality

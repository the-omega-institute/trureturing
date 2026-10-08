/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRank
   mirror-E: none(waiver:phylogenetic-density-limit)
   anchors: []
   utility: none
   digest: The maximal phylogenetic density of connected graphs tends to one. -/

import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankTiling
import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankCover
import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankUpper
import D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankRandom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRank

open SimpleGraph PhylogeneticRankDefs

/-- Conjecture 7.1: maximal phylogenetic density tends to one. -/
theorem result : PhylogeneticRankDefs.claim := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨t, ht⟩ := exists_nat_gt (max 16 (24 / ε))
  have ht16 : 16 ≤ t := by exact_mod_cast (le_max_left _ _).trans ht.le
  have ht0 : 0 < t := by omega
  have hteps : (24 : ℝ) < ε * t := by
    have := (le_max_right (16 : ℝ) (24 / ε)).trans_lt ht
    exact (div_lt_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  have hpow : (0 : ℝ) < (t : ℝ) ^ 8 := by positivity
  have hA : (12 : ℝ) * (t : ℝ) ^ 8 < (ε / 2) * (t : ℝ) ^ 9 := by
    have h := mul_lt_mul_of_pos_right hteps hpow
    rw [show (t : ℝ) ^ 9 = (t : ℝ) * (t : ℝ) ^ 8 by ring]
    nlinarith
  obtain ⟨H, htri, hfour, hα⟩ := PhylogeneticRankRandom.exists_good_block t ht16
  obtain ⟨N, hN⟩ := exists_nat_gt (max (3 * (t : ℝ) ^ 9) (2 * (t : ℝ) ^ 9 / ε))
  refine ⟨N, ?_⟩
  intro n hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnblock : 3 * t ^ 9 ≤ n := by
    have h := (le_max_left _ _).trans (hN.le.trans hnR)
    exact_mod_cast h
  have hn2 : 2 ≤ n := by have := pow_pos ht0 9; nlinarith
  have hnpos : (0 : ℝ) < n := by positivity
  have hsmall : (t : ℝ) ^ 9 < ε / 2 * n := by
    have h := (le_max_right _ _).trans_lt (hN.trans_le hnR)
    have := (div_lt_iff₀ hε).mp h
    nlinarith
  obtain ⟨K, hKtri, hKfour, hKconn, hKdiam, hKα⟩ :=
    tile_graph (pow_pos ht0 9) H htri hfour n hnblock
  have hαsmall : (K.indepNum : ℝ) < ε * n := by
    have hcast : (K.indepNum : ℝ) ≤
        (n / t ^ 9 : ℕ) * (12 * (t : ℝ) ^ 8) + (t : ℝ) ^ 9 := by
      exact_mod_cast hKα.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hα) _)
    have hquot : ((n / t ^ 9 : ℕ) : ℝ) * (t : ℝ) ^ 9 ≤ n := by
      exact_mod_cast Nat.div_mul_le_self n (t ^ 9)
    have hQ : (0 : ℝ) ≤ (n / t ^ 9 : ℕ) := by positivity
    have hmult := mul_le_mul_of_nonneg_left hA.le hQ
    have hmult2 := mul_le_mul_of_nonneg_left hquot (show 0 ≤ ε / 2 by positivity)
    nlinarith
  have hrank : n - K.indepNum ≤ phyloRank Kᶜ := by
    apply embedding_rank_lower_bound hn2 K hKtri hKfour hKconn hKdiam
    change sInf {k | HasTreeEmbedding Kᶜ k} ∈ {k | HasTreeEmbedding Kᶜ k}
    apply Nat.sInf_mem
    exact ⟨n - 1, connected_has_tree_embedding hn2 Kᶜ hKconn⟩
  have hlower : 1 - ε < (phyloRank Kᶜ : ℝ) / n := by
    have hnat : n ≤ phyloRank Kᶜ + K.indepNum := by omega
    have hreal : (n : ℝ) ≤ (phyloRank Kᶜ : ℝ) + K.indepNum := by exact_mod_cast hnat
    apply (lt_div_iff₀ hnpos).mpr
    nlinarith
  have hbound : ∀ x ∈ {x | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ x = (phyloRank G : ℝ) / n}, x ≤ 1 := by
    rintro x ⟨G, hG, rfl⟩
    have hr : phyloRank G ≤ n - 1 :=
      Nat.sInf_le (connected_has_tree_embedding hn2 G hG)
    apply (div_le_iff₀ hnpos).mpr
    have hr' : phyloRank G ≤ n := hr.trans (Nat.sub_le _ _)
    simpa using (show (phyloRank G : ℝ) ≤ (n : ℝ) by exact_mod_cast hr')
  have hfinite : Set.Finite {x | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ x = (phyloRank G : ℝ) / n} := by
    apply (Set.finite_range (fun G : SimpleGraph (Fin n) => (phyloRank G : ℝ) / n)).subset
    rintro x ⟨G, _, rfl⟩
    exact ⟨G, rfl⟩
  have hbdd : BddAbove {x | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ x = (phyloRank G : ℝ) / n} := hfinite.bddAbove
  have hmem : (phyloRank Kᶜ : ℝ) / n ∈ {x | ∃ G : SimpleGraph (Fin n),
      G.Connected ∧ x = (phyloRank G : ℝ) / n} := ⟨Kᶜ, hKconn, rfl⟩
  have hmax : 1 - ε < maxDensity n := hlower.trans_le (le_csSup hbdd hmem)
  have hupper : maxDensity n ≤ 1 := csSup_le ⟨_, hmem⟩ hbound
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith


#print axioms result

end D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRank

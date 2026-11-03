/- GID: D5/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/SolidResolvingTournamentProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite distance profiles and their small-landmark chain bounds. -/

/-
admission_basis: escape-witness
escape_witness: D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentProfiles.card_le_of_chain_cover
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/23622
card_le_of_chain_cover — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: cardinal_le_profile_chains.
  Direct frozen dependencies: none.
profile_finite_bound — proof_shape: bind-only; escape_witness: none; consumers: strong_enat_profile_bound.
  Direct frozen dependencies: none.
nat_profile_bound_3_2 — proof_shape: bind-only; escape_witness: none; consumers: landmark_bound_3, strong_profile_cover_3_2.
  Direct frozen dependencies: none.
nat_profile_bound_4_4 — proof_shape: bind-only; escape_witness: none; consumers: strong_profile_cover_4_4, landmark_bound_4.
  Direct frozen dependencies: none.
nat_profile_bound_5_8 — proof_shape: bind-only; escape_witness: none; consumers: strong_profile_cover_5_8, landmark_bound_5.
  Direct frozen dependencies: none.
nat_profile_bound_5_10 — proof_shape: bind-only; escape_witness: none; consumers: landmark_bound_5, strong_profile_cover_5_10.
  Direct frozen dependencies: none.
nat_profile_bound_5_12 — proof_shape: bind-only; escape_witness: none; consumers: strong_profile_cover_5_12, landmark_bound_5.
  Direct frozen dependencies: none.
nat_profile_bound_5_40 — proof_shape: bind-only; escape_witness: none; consumers: strong_profile_cover_5_40, landmark_bound_5.
  Direct frozen dependencies: none.
nat_profile_bound_5_41 — proof_shape: bind-only; escape_witness: none; consumers: strong_profile_cover_5_41, landmark_bound_5.
  Direct frozen dependencies: none.
nat_profile_bound_5_76 — proof_shape: bind-only; escape_witness: none; consumers: landmark_bound_5, strong_profile_cover_5_76.
  Direct frozen dependencies: none.
profile_mem_of_certificate — proof_shape: bind-only; escape_witness: none; consumers: nonstrong_antichain_bound_5_11, strong_profile_cover_5_12, strong_profile_cover_5_40, nonstrong_antichain_bound_4_2, nonstrong_antichain_bound_5_4, nonstrong_antichain_bound_3_0, nonstrong_antichain_bound_5_5, strong_profile_cover_5_41, strong_profile_cover_4_4, nonstrong_antichain_bound_5_2, nonstrong_antichain_bound_4_5, strong_profile_cover_5_8, nonstrong_antichain_bound_5_0, nonstrong_antichain_bound_4_0, strong_profile_cover_5_10, strong_profile_cover_3_2, nonstrong_antichain_bound_5_9, strong_profile_cover_5_76.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
cardinal_le_profile_chains — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: nonstrong_antichain_bound_5_11, strong_profile_antichain_bound_5_12, strong_profile_antichain_bound_5_10, nonstrong_antichain_bound_4_2, nonstrong_antichain_bound_5_4, nonstrong_antichain_bound_3_0, strong_profile_antichain_bound_5_40, nonstrong_antichain_bound_5_5, strong_profile_antichain_bound_3_2, strong_profile_antichain_bound_5_8, strong_profile_antichain_bound_5_76, nonstrong_antichain_bound_5_2, nonstrong_antichain_bound_4_5, strong_profile_antichain_bound_5_41, nonstrong_antichain_bound_5_0, nonstrong_antichain_bound_4_0, strong_profile_antichain_bound_4_4, nonstrong_antichain_bound_5_9.
  Direct frozen dependencies: none.
strong_profile_antichain_bound_3_2 — proof_shape: bind-only; escape_witness: none; consumers: landmark_bound_3.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_4_4 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_4.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_8 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_10 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_12 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_40 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_41 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
strong_profile_antichain_bound_5_76 — proof_shape: content; escape_witness: card_le_of_chain_cover; consumers: landmark_bound_5.
  Direct frozen dependencies: D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.enumTuple (sha256:d7611af7612c0cc1e496d42c844e113e6097c45afced6e8c6a48249818da7463); D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation.mem_enumTuple (sha256:96dead7eed9a97499f6198b40c29d4a22f920bc9b74dc3ad69e136ea59d5b58a).
-/

import D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.ENat.Lattice

namespace D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentProfiles

open D5.S3.ObserverMemory.Algorithms.UniformDescriptorPresentation (enumTuple mem_enumTuple)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
universe uSolid

lemma card_le_of_chain_cover {U P : Type*} [Fintype U] [Preorder P]
    (f : U → P) (m : ℕ) (chains : Fin m → Set P)
    (cover : ∀ u, ∃ i, f u ∈ chains i)
    (chain : ∀ i a b, a ∈ chains i → b ∈ chains i → a ≤ b ∨ b ≤ a)
    (antichain : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ m := by
  classical
  let pick : U → Fin m := fun u => Classical.choose (cover u)
  have hpick : ∀ u, f u ∈ chains (pick u) := fun u => Classical.choose_spec (cover u)
  have hinj : Function.Injective pick := by
    intro u v huv
    by_contra hne
    have hcomp := chain (pick u) (f u) (f v) (hpick u) (by simpa [huv] using hpick v)
    rcases hcomp with hle | hle
    · exact (antichain hne).1 hle
    · exact (antichain hne).2 hle
  simpa using Fintype.card_le_of_injective pick hinj

lemma profile_finite_bound {k R : Nat} (D : Fin k → Fin k → Nat)
    (hD : ∀ i j, D i j ≤ R) (j₀ : Fin k) (x : Fin k → ℕ∞)
    (hB : ∀ j, ∃ i, x i < (D i j : ℕ∞))
    (hC : ∀ i j, x i ≤ (D i j : ℕ∞) + x j) :
    ∃ y : Fin k → Nat, (∀ i, (y i : ℕ∞) = x i) ∧ (∀ i, y i ≤ 2*R-1) := by
  obtain ⟨a, ha⟩ := hB j₀
  let n := (x a).toNat
  have hn : (n : ℕ∞) = x a := ENat.natCast_toNat (ne_top_of_lt ha)
  have hnR : n < R := by
    have hnD : (n : ℕ∞) < (D a j₀ : ℕ∞) := by rw [hn]; exact ha
    exact (ENat.coe_lt_coe.mp hnD).trans_le (hD a j₀)
  have hxbound : ∀ i, x i ≤ ((R+n : Nat) : ℕ∞) := by
    intro i
    calc
      x i ≤ (D i a : ℕ∞) + x a := hC i a
      _ ≤ (R : ℕ∞) + (n : ℕ∞) := by
        rw [← hn]
        exact add_le_add (ENat.natCast_le_natCast.mpr (hD i a)) le_rfl
      _ = ((R+n : Nat) : ℕ∞) := (ENat.coe_add R n).symm
  have hxfinite : ∀ i, x i ≠ ⊤ := fun i =>
    ne_top_of_lt (lt_of_le_of_lt (hxbound i) (ENat.coe_lt_top _))
  refine ⟨fun i => (x i).toNat, fun i => ENat.coe_toNat (hxfinite i), ?_⟩
  intro i
  have hi : (x i).toNat ≤ R+n := by
    have h := hxbound i
    rw [← ENat.coe_toNat (hxfinite i)] at h
    exact ENat.coe_le_coe.mp h
  change (x i).toNat ≤ 2*R-1
  omega

def D32 : Fin 3 → Fin 3 → Nat := ![![0,2,1],![1,0,2],![2,1,0]]

theorem nat_profile_bound_3_2 (x : Fin 3 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D32 i j)
    (hC : ∀ i j, x i ≤ D32 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 0 at hb2
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 1 + x 2 := hC 0 2
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 2 + x 2 := hC 1 2
  have hc20 : x 2 ≤ 2 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega

def D44 : Fin 4 → Fin 4 → Nat := ![![0,2,2,1],![1,0,3,2],![1,1,0,2],![2,1,1,0]]

theorem nat_profile_bound_4_4 (x : Fin 4 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D44 i j)
    (hC : ∀ i j, x i ≤ D44 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 1 ∨ x 3 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 3 ∨ x 2 < 0 ∨ x 3 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 0 at hb3
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 1 + x 3 := hC 0 3
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 3 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 2 + x 3 := hC 1 3
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 2 + x 3 := hC 2 3
  have hc30 : x 3 ≤ 2 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 1 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega

def D58 : Fin 5 → Fin 5 → Nat := ![![0,2,2,2,1],![1,0,3,3,2],![1,1,0,3,2],![1,1,1,0,2],![2,1,1,1,0]]

theorem nat_profile_bound_5_8 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D58 i j)
    (hC : ∀ i j, x i ≤ D58 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 3 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 2 ∨ x 1 < 3 ∨ x 2 < 3 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 2 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 2 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 3 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 3 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 2 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 3 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 2 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 1 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 1 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 2 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 1 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

def D510 : Fin 5 → Fin 5 → Nat := ![![0,2,1,2,1],![1,0,2,3,2],![2,1,0,4,3],![1,1,1,0,2],![2,1,1,1,0]]

theorem nat_profile_bound_5_10 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D510 i j)
    (hC : ∀ i j, x i ≤ D510 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 2 ∨ x 3 < 1 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 2 ∨ x 1 < 3 ∨ x 2 < 4 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 3 ∨ x 3 < 2 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 1 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 2 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 2 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 3 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 2 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 2 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 4 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 3 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 1 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 1 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 2 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 1 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

def D512 : Fin 5 → Fin 5 → Nat := ![![0,2,2,1,1],![1,0,3,2,2],![1,1,0,2,2],![2,1,1,0,3],![2,1,1,1,0]]

theorem nat_profile_bound_5_12 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D512 i j)
    (hC : ∀ i j, x i ≤ D512 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 1 ∨ x 3 < 2 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 3 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 3 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 1 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 3 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 2 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 2 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 2 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 2 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 2 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 1 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 3 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 1 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

def D540 : Fin 5 → Fin 5 → Nat := ![![0,2,2,2,1],![1,0,2,1,2],![1,1,0,2,2],![1,2,1,0,2],![2,1,1,1,0]]

theorem nat_profile_bound_5_40 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D540 i j)
    (hC : ∀ i j, x i ≤ D540 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 2 ∨ x 4 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 2 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 2 ∨ x 1 < 1 ∨ x 2 < 2 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 2 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 2 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 2 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 1 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 2 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 2 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 2 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 1 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 2 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 2 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 1 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

def D541 : Fin 5 → Fin 5 → Nat := ![![0,1,2,2,1],![2,0,2,1,3],![1,1,0,2,2],![1,2,1,0,2],![2,1,1,1,0]]

theorem nat_profile_bound_5_41 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D541 i j)
    (hC : ∀ i j, x i ≤ D541 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 2 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 1 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 2 ∨ x 4 < 1 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 2 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 2 ∨ x 1 < 1 ∨ x 2 < 2 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 3 ∨ x 2 < 2 ∨ x 3 < 2 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 1 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 2 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 2 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 2 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 1 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 3 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 2 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 2 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 1 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 2 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 2 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 1 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

def D576 : Fin 5 → Fin 5 → Nat := ![![0,2,2,1,1],![1,0,2,2,1],![1,1,0,2,2],![2,1,1,0,2],![2,2,1,1,0]]

theorem nat_profile_bound_5_76 (x : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ x i) (hB : ∀ j, ∃ i, x i < D576 i j)
    (hC : ∀ i j, x i ≤ D576 i j + x j) : ∀ i, x i ≤ 2 := by
  have ha0 : 1 ≤ x 0 := hA 0
  have ha1 : 1 ≤ x 1 := hA 1
  have ha2 : 1 ≤ x 2 := hA 2
  have ha3 : 1 ≤ x 3 := hA 3
  have ha4 : 1 ≤ x 4 := hA 4
  have hb0 := hB 0
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb0
  change x 0 < 0 ∨ x 1 < 1 ∨ x 2 < 1 ∨ x 3 < 2 ∨ x 4 < 2 at hb0
  have hb1 := hB 1
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb1
  change x 0 < 2 ∨ x 1 < 0 ∨ x 2 < 1 ∨ x 3 < 1 ∨ x 4 < 2 at hb1
  have hb2 := hB 2
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb2
  change x 0 < 2 ∨ x 1 < 2 ∨ x 2 < 0 ∨ x 3 < 1 ∨ x 4 < 1 at hb2
  have hb3 := hB 3
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb3
  change x 0 < 1 ∨ x 1 < 2 ∨ x 2 < 2 ∨ x 3 < 0 ∨ x 4 < 1 at hb3
  have hb4 := hB 4
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, or_false] at hb4
  change x 0 < 1 ∨ x 1 < 1 ∨ x 2 < 2 ∨ x 3 < 2 ∨ x 4 < 0 at hb4
  have hc01 : x 0 ≤ 2 + x 1 := hC 0 1
  have hc02 : x 0 ≤ 2 + x 2 := hC 0 2
  have hc03 : x 0 ≤ 1 + x 3 := hC 0 3
  have hc04 : x 0 ≤ 1 + x 4 := hC 0 4
  have hc10 : x 1 ≤ 1 + x 0 := hC 1 0
  have hc12 : x 1 ≤ 2 + x 2 := hC 1 2
  have hc13 : x 1 ≤ 2 + x 3 := hC 1 3
  have hc14 : x 1 ≤ 1 + x 4 := hC 1 4
  have hc20 : x 2 ≤ 1 + x 0 := hC 2 0
  have hc21 : x 2 ≤ 1 + x 1 := hC 2 1
  have hc23 : x 2 ≤ 2 + x 3 := hC 2 3
  have hc24 : x 2 ≤ 2 + x 4 := hC 2 4
  have hc30 : x 3 ≤ 2 + x 0 := hC 3 0
  have hc31 : x 3 ≤ 1 + x 1 := hC 3 1
  have hc32 : x 3 ≤ 1 + x 2 := hC 3 2
  have hc34 : x 3 ≤ 2 + x 4 := hC 3 4
  have hc40 : x 4 ≤ 2 + x 0 := hC 4 0
  have hc41 : x 4 ≤ 2 + x 1 := hC 4 1
  have hc42 : x 4 ≤ 1 + x 2 := hC 4 2
  have hc43 : x 4 ≤ 1 + x 3 := hC 4 3
  intro i
  fin_cases i
  · change x 0 ≤ 2
    omega
  · change x 1 ≤ 2
    omega
  · change x 2 ≤ 2
    omega
  · change x 3 ≤ 2
    omega
  · change x 4 ≤ 2
    omega

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def acBool {k b : Nat} (D : Fin k → Fin k → Nat) (x : Fin k → Fin b) : Bool :=
  (List.finRange k).all (fun i => decide (1 ≤ (x i).val)) &&
  (List.finRange k).all (fun j =>
    (List.finRange k).any (fun i => decide ((x i).val < D i j))) &&
  (List.finRange k).all (fun i =>
    (List.finRange k).all (fun j => decide ((x i).val ≤ D i j + (x j).val)))

private lemma acBool_iff {k b : Nat} (D : Fin k → Fin k → Nat) (x : Fin k → Fin b) :
    acBool D x = true ↔
    (∀ i, 1 ≤ (x i).val) ∧ (∀ j, ∃ i, (x i).val < D i j) ∧
      (∀ i j, (x i).val ≤ D i j + (x j).val) := by
  simp [acBool, and_assoc]

private def profiles32 : List (Fin 3 → Fin 3) := [![1,1,1]]

private theorem profile_certificate_3_2 :
    (enumTuple (List.finRange 3) 3).all (fun x => !acBool D32 x || decide (x ∈ profiles32)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles44 : List (Fin 4 → Fin 3) := [![1,1,1,1],![1,1,2,1],![1,2,1,1]]

private theorem profile_certificate_4_4 :
    (enumTuple (List.finRange 3) 4).all (fun x => !acBool D44 x || decide (x ∈ profiles44)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles58 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,2,1],![1,1,2,2,1],![1,1,2,1,1],![1,2,2,1,1],![1,2,1,1,1],![1,2,1,2,1]]

private theorem profile_certificate_5_8 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D58 x || decide (x ∈ profiles58)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles510 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,1,2],![1,1,1,2,2],![1,1,1,2,1],![1,1,2,2,1],![1,1,2,1,1]]

private theorem profile_certificate_5_10 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D510 x || decide (x ∈ profiles510)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles512 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,1,2],![1,1,2,1,2],![1,1,1,2,1],![1,2,1,2,1],![1,1,2,1,1],![1,1,2,2,1],![1,2,1,1,1],![1,2,1,1,2]]

private theorem profile_certificate_5_12 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D512 x || decide (x ∈ profiles512)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles540 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,2,1],![1,1,2,2,1],![1,1,2,1,1],![1,2,2,1,1],![1,2,1,1,1],![1,2,1,2,1],![2,1,1,1,1]]

private theorem profile_certificate_5_40 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D540 x || decide (x ∈ profiles540)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles541 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,1,2],![2,1,1,1,2],![1,1,2,1,1],![1,1,2,1,2],![1,2,1,1,1],![1,2,2,1,1],![2,1,1,1,1]]

private theorem profile_certificate_5_41 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D541 x || decide (x ∈ profiles541)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def profiles576 : List (Fin 5 → Fin 3) := [![1,1,1,1,1],![1,1,1,1,2],![1,1,2,1,2],![1,1,1,2,1],![1,2,1,2,1],![1,1,2,1,1],![2,1,2,1,1],![1,2,1,1,1],![1,2,1,1,2],![2,1,1,1,1],![2,1,1,2,1]]

private theorem profile_certificate_5_76 :
    (enumTuple (List.finRange 3) 5).all (fun x => !acBool D576 x || decide (x ∈ profiles576)) = true := by exact Bool.eq_false_imp_eq_true.mp (congrFun rfl)

private def chains32 : List (List (Fin 3 → Fin 3)) := [[![1,1,1]]]

private theorem chain_certificate_3_2 :
    chains32.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains32.flatten = profiles32 ∧ chains32.length ≤ 1 := by decide

private def chains44 : List (List (Fin 4 → Fin 3)) := [[![1,1,1,1],![1,1,2,1]],[![1,2,1,1]]]

private theorem chain_certificate_4_4 :
    chains44.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains44.flatten = profiles44 ∧ chains44.length ≤ 2 := by decide

private def chains58 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,2,1],![1,1,2,2,1]],[![1,1,2,1,1],![1,2,2,1,1]],[![1,2,1,1,1],![1,2,1,2,1]]]

private theorem chain_certificate_5_8 :
    chains58.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains58.flatten = profiles58 ∧ chains58.length ≤ 5 := by decide

private def chains510 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,1,2],![1,1,1,2,2]],[![1,1,1,2,1],![1,1,2,2,1]],[![1,1,2,1,1]]]

private theorem chain_certificate_5_10 :
    chains510.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains510.flatten = profiles510 ∧ chains510.length ≤ 5 := by decide

private def chains512 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,1,2],![1,1,2,1,2]],[![1,1,1,2,1],![1,2,1,2,1]],[![1,1,2,1,1],![1,1,2,2,1]],[![1,2,1,1,1],![1,2,1,1,2]]]

private theorem chain_certificate_5_12 :
    chains512.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains512.flatten = profiles512 ∧ chains512.length ≤ 5 := by decide

private def chains540 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,2,1],![1,1,2,2,1]],[![1,1,2,1,1],![1,2,2,1,1]],[![1,2,1,1,1],![1,2,1,2,1]],[![2,1,1,1,1]]]

private theorem chain_certificate_5_40 :
    chains540.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains540.flatten = profiles540 ∧ chains540.length ≤ 5 := by decide

private def chains541 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,1,2],![2,1,1,1,2]],[![1,1,2,1,1],![1,1,2,1,2]],[![1,2,1,1,1],![1,2,2,1,1]],[![2,1,1,1,1]]]

private theorem chain_certificate_5_41 :
    chains541.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains541.flatten = profiles541 ∧ chains541.length ≤ 5 := by decide

private def chains576 : List (List (Fin 5 → Fin 3)) := [[![1,1,1,1,1],![1,1,1,1,2],![1,1,2,1,2]],[![1,1,1,2,1],![1,2,1,2,1]],[![1,1,2,1,1],![2,1,2,1,1]],[![1,2,1,1,1],![1,2,1,1,2]],[![2,1,1,1,1],![2,1,1,2,1]]]

private theorem chain_certificate_5_76 :
    chains576.all (fun ch => decide (ch.Pairwise (fun x y => x ≤ y ∨ y ≤ x))) = true ∧
    chains576.flatten = profiles576 ∧ chains576.length ≤ 5 := by decide

lemma profile_mem_of_certificate {k : Nat} (D : Fin k → Fin k → Nat)
    (ps : List (Fin k → Fin 3))
    (hcert : (enumTuple (List.finRange 3) k).all (fun x => !acBool D x || decide (x ∈ ps)) = true)
    (y : Fin k → Nat) (hy : ∀ i, y i < 3)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D i j)
    (hC : ∀ i j, y i ≤ D i j + y j) :
    ∃ x : Fin k → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ ps := by
  let x : Fin k → Fin 3 := fun i => ⟨y i, hy i⟩
  have hx : acBool D x = true := (acBool_iff D x).mpr ⟨hA, hB, hC⟩
  have hp := (List.all_eq_true.mp hcert) x (mem_enumTuple (List.finRange 3) k x (by intro i; simp))
  have hlist : decide (x ∈ ps) = true := by simpa only [hx, Bool.not_true, Bool.false_or] using hp
  exact ⟨x, fun _ => rfl, of_decide_eq_true hlist⟩

private theorem strong_profile_cover_3_2 (y : Fin 3 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D32 i j)
    (hC : ∀ i j, y i ≤ D32 i j + y j) :
    ∃ x : Fin 3 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles32 := by
  apply profile_mem_of_certificate D32 profiles32 profile_certificate_3_2 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_3_2 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_4_4 (y : Fin 4 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D44 i j)
    (hC : ∀ i j, y i ≤ D44 i j + y j) :
    ∃ x : Fin 4 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles44 := by
  apply profile_mem_of_certificate D44 profiles44 profile_certificate_4_4 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_4_4 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_8 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D58 i j)
    (hC : ∀ i j, y i ≤ D58 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles58 := by
  apply profile_mem_of_certificate D58 profiles58 profile_certificate_5_8 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_8 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_10 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D510 i j)
    (hC : ∀ i j, y i ≤ D510 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles510 := by
  apply profile_mem_of_certificate D510 profiles510 profile_certificate_5_10 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_10 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_12 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D512 i j)
    (hC : ∀ i j, y i ≤ D512 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles512 := by
  apply profile_mem_of_certificate D512 profiles512 profile_certificate_5_12 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_12 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_40 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D540 i j)
    (hC : ∀ i j, y i ≤ D540 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles540 := by
  apply profile_mem_of_certificate D540 profiles540 profile_certificate_5_40 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_40 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_41 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D541 i j)
    (hC : ∀ i j, y i ≤ D541 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles541 := by
  apply profile_mem_of_certificate D541 profiles541 profile_certificate_5_41 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_41 y hA hB hC i)) hA hB hC

private theorem strong_profile_cover_5_76 (y : Fin 5 → Nat)
    (hA : ∀ i, 1 ≤ y i) (hB : ∀ j, ∃ i, y i < D576 i j)
    (hC : ∀ i j, y i ≤ D576 i j + y j) :
    ∃ x : Fin 5 → Fin 3, (∀ i, (x i).val = y i) ∧ x ∈ profiles576 := by
  apply profile_mem_of_certificate D576 profiles576 profile_certificate_5_76 y
    (fun i => Nat.lt_succ_iff.mpr (nat_profile_bound_5_76 y hA hB hC i)) hA hB hC

lemma cardinal_le_profile_chains {U : Type*} [Fintype U] {k : Nat}
    (f : U → Fin k → Nat) (chains : List (List (Fin k → Fin 3)))
    (cover : ∀ u, ∃ z : Fin k → Fin 3,
      (∀ j, (z j).val = f u j) ∧ z ∈ chains.flatten)
    (chain : ∀ ch ∈ chains, ∀ a ∈ ch, ∀ b ∈ ch,
      (∀ j, (a j).val ≤ (b j).val) ∨ (∀ j, (b j).val ≤ (a j).val))
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ chains.length := by
  let C : Fin chains.length → Set (Fin k → Nat) := fun i =>
    {y | ∃ z ∈ chains.get i, ∀ j, (z j).val = y j}
  apply card_le_of_chain_cover f chains.length C ?_ ?_ anti
  · intro u
    obtain ⟨z, hzu, hz⟩ := cover u
    obtain ⟨ch, hch, hzc⟩ := List.mem_flatten.mp hz
    obtain ⟨i, hi⟩ := List.get_of_mem hch
    exact ⟨i, z, by change z ∈ chains.get i; rw [hi]; exact hzc, hzu⟩
  · intro i a b ha hb
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨y, hy, hyb⟩ := hb
    have hch : chains.get i ∈ chains := List.mem_iff_get.mpr ⟨i, rfl⟩
    rcases chain _ hch x hx y hy with h | h
    · left; intro j; rw [← hxa j, ← hyb j]; exact h j
    · right; intro j; rw [← hxa j, ← hyb j]; exact h j

theorem strong_profile_antichain_bound_3_2 {U : Type*} [Fintype U]
    (f : U → Fin 3 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D32 i j)
    (hC : ∀ u i j, f u i ≤ D32 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 1 := by
  have hc := chain_certificate_3_2
  apply (cardinal_le_profile_chains f chains32 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_3_2 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_4_4 {U : Type*} [Fintype U]
    (f : U → Fin 4 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D44 i j)
    (hC : ∀ u i j, f u i ≤ D44 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 2 := by
  have hc := chain_certificate_4_4
  apply (cardinal_le_profile_chains f chains44 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_4_4 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_8 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D58 i j)
    (hC : ∀ u i j, f u i ≤ D58 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_8
  apply (cardinal_le_profile_chains f chains58 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_8 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_10 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D510 i j)
    (hC : ∀ u i j, f u i ≤ D510 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_10
  apply (cardinal_le_profile_chains f chains510 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_10 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_12 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D512 i j)
    (hC : ∀ u i j, f u i ≤ D512 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_12
  apply (cardinal_le_profile_chains f chains512 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_12 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_40 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D540 i j)
    (hC : ∀ u i j, f u i ≤ D540 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_40
  apply (cardinal_le_profile_chains f chains540 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_40 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_41 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D541 i j)
    (hC : ∀ u i j, f u i ≤ D541 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_41
  apply (cardinal_le_profile_chains f chains541 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_41 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

theorem strong_profile_antichain_bound_5_76 {U : Type*} [Fintype U]
    (f : U → Fin 5 → Nat)
    (hA : ∀ u i, 1 ≤ f u i)
    (hB : ∀ u j, ∃ i, f u i < D576 i j)
    (hC : ∀ u i j, f u i ≤ D576 i j + f u j)
    (anti : ∀ ⦃u v : U⦄, u ≠ v → ¬ f u ≤ f v ∧ ¬ f v ≤ f u) :
    Fintype.card U ≤ 5 := by
  have hc := chain_certificate_5_76
  apply (cardinal_le_profile_chains f chains576 ?_ ?_ anti).trans hc.2.2
  · intro u
    obtain ⟨z, hz, hm⟩ := strong_profile_cover_5_76 (f u) (hA u) (hB u) (hC u)
    exact ⟨z, hz, hc.2.1.symm ▸ hm⟩
  · intro ch hch
    have hp := of_decide_eq_true ((List.all_eq_true.mp hc.1) ch hch)
    have hflip := hp.imp (fun h => h.symm)
    have hr : ∀ z ∈ ch, z ≤ z ∨ z ≤ z := fun z _ => Or.inl le_rfl
    intro a ha b hb
    exact List.Pairwise.forall_of_forall_of_flip hr hp hflip ha hb

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

end D5.S3.Combinatorics.Graph.Walks.SolidResolvingTournamentProfiles

/- GID: D5/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/ConvergentMaximalFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convergent branches extend to an unrestricted maximal AD family. -/

import D5.S3.Topology.AlmostDisjoint.ConvergentBranches

open Set Filter Topology
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches

namespace D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily

/-- An almost-disjoint family consists of infinite sets with finite pairwise intersections. -/
def ADFamily {α : Type*} (M : Set (Set α)) : Prop :=
  (∀ A ∈ M, A.Infinite) ∧ M.Pairwise (fun A B => (A ∩ B).Finite)

/-- Every infinite subset meets some member infinitely. -/
def MADFamily {α : Type*} (M : Set (Set α)) : Prop :=
  ADFamily M ∧ ∀ E : Set α, E.Infinite → ∃ A ∈ M, (E ∩ A).Infinite

private theorem convergent_subfamily {α : Type*} (u : α → unitInterval)
    {E : Set α} (hE : E.Infinite) :
    ∃ A : Set α, A ⊆ E ∧ A.Infinite ∧ ∃ r, ConvergesOn u A r := by
  let e : ℕ → α := fun n => (hE.natEmbedding E n).val
  have he : Function.Injective e := by
    intro n m h
    exact (hE.natEmbedding E).injective (Subtype.ext h)
  obtain ⟨r, φ, hφ, hr⟩ := CompactSpace.tendsto_subseq (u ∘ e)
  refine ⟨range (e ∘ φ), ?_, infinite_range_of_injective (he.comp hφ.injective), r, ?_⟩
  · rintro a ⟨n, rfl⟩
    exact (hE.natEmbedding E (φ n)).property
  · exact convergesOn_range (e ∘ φ) u r hr

private theorem extend_convergent_ad {α : Type*} (u : α → unitInterval)
    (F : Set (Set α)) (hF : ADFamily F)
    (hcF : ∀ A ∈ F, ∃ r, ConvergesOn u A r) :
    ∃ M : Set (Set α), F ⊆ M ∧ MADFamily M ∧ ∀ A ∈ M, ∃ r, ConvergesOn u A r := by
  classical
  let Good : Set (Set (Set α)) := {M | ADFamily M ∧ ∀ A ∈ M, ∃ r, ConvergesOn u A r}
  have hub : ∀ c ⊆ Good, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ Good, ∀ N ∈ c, N ⊆ ub := by
    intro c hc hchain _
    refine ⟨⋃₀ c, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro A hA
      obtain ⟨N, hN, hAN⟩ := mem_sUnion.mp hA
      exact (hc hN).1.1 A hAN
    · intro A hA B hB hAB
      obtain ⟨N, hN, hAN⟩ := mem_sUnion.mp hA
      obtain ⟨P, hP, hBP⟩ := mem_sUnion.mp hB
      rcases hchain.total hN hP with hNP | hPN
      · exact (hc hP).1.2 (hNP hAN) hBP hAB
      · exact (hc hN).1.2 hAN (hPN hBP) hAB
    · intro A hA
      obtain ⟨N, hN, hAN⟩ := mem_sUnion.mp hA
      exact (hc hN).2 A hAN
    · intro N hN A hAN
      exact mem_sUnion.mpr ⟨N, hN, hAN⟩
  obtain ⟨M, hFM, hM⟩ := zorn_subset_nonempty Good hub F ⟨hF, hcF⟩
  · refine ⟨M, hFM, ⟨hM.prop.1, ?_⟩, hM.prop.2⟩
    intro E hE
    by_contra h
    have hfin : ∀ A ∈ M, (E ∩ A).Finite := by
      intro A hA
      exact not_infinite.mp (fun hinf => h ⟨A, hA, hinf⟩)
    obtain ⟨A, hAE, hAi, r, hr⟩ := convergent_subfamily u hE
    have hAfin : ∀ B ∈ M, (A ∩ B).Finite := fun B hB =>
      (hfin B hB).subset (inter_subset_inter_left _ hAE)
    have hAM : A ∉ M := by
      intro hA
      exact hAi (by simpa using hAfin A hA)
    have hgood : insert A M ∈ Good := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro B hB
        rcases mem_insert_iff.mp hB with rfl | hB
        · exact hAi
        · exact hM.prop.1.1 B hB
      · intro B hB C hC hBC
        by_cases hBA : B = A
        · rw [hBA]
          have hCM : C ∈ M := (mem_insert_iff.mp hC).resolve_left
            (fun hCA => hBC (hBA.trans hCA.symm))
          exact hAfin C hCM
        · have hBM : B ∈ M := (mem_insert_iff.mp hB).resolve_left hBA
          by_cases hCA : C = A
          · rw [hCA, inter_comm]
            exact hAfin B hBM
          · exact hM.prop.1.2 hBM ((mem_insert_iff.mp hC).resolve_left hCA) hBC
      · intro B hB
        rcases mem_insert_iff.mp hB with rfl | hB
        · exact ⟨r, hr⟩
        · exact hM.prop.2 B hB
    have heq := hM.eq_of_subset hgood (subset_insert A M)
    exact hAM (heq.symm ▸ mem_insert A M)

/-- Actual existence, with no hypothesized maximal family or convergence qualification
on maximality. Every four-letter branch is retained as a family member. -/
theorem exists_convergent_mad :
    ∃ M : Set (Set Word), range branchSet ⊆ M ∧ MADFamily M ∧
      ∀ A ∈ M, ∃ r : unitInterval, ConvergesOn wordValue A r := by
  have hb := (branch_system 0).2
  apply extend_convergent_ad wordValue (range branchSet)
  · constructor
    · rintro A ⟨x, rfl⟩
      exact hb.1 x
    · rintro A ⟨x, rfl⟩ B ⟨y, rfl⟩ hxy
      apply hb.2.1 x y
      intro h
      exact hxy (congrArg branchSet h)
  · rintro A ⟨x, rfl⟩
    exact ⟨limitValue x, hb.2.2.1 x⟩

end D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily

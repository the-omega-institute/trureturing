/- GID: D5/S3/Topology/AlmostDisjoint/ColorFiberDiagonal
   generality: G
   mirror-B: D5/B/S3/Topology/AlmostDisjoint/ColorFiberDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Maximality forces uncountable partitioner fibers at every color support. -/

import D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal

open Set Filter Topology
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.ConvergentMaximalFamily
open D5.S3.Topology.AlmostDisjoint.NeighborhoodIdeal

namespace D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal

/-- A partitioner assigns each infinite family member an eventual color. -/
def Partitions {α ι : Type*} (M : ι → Set α) (D : Set α) : Prop :=
  ∀ i, (M i \ D).Finite ∨ (M i ∩ D).Finite

private theorem convergesOn_eq_of_infinite_inter {α Y : Type*}
    [TopologicalSpace Y] [T2Space Y] (u : α → Y) {A B : Set α} {r s : Y}
    (hA : ConvergesOn u A r) (hB : ConvergesOn u B s) (hAB : (A ∩ B).Infinite) :
    r = s := by
  by_contra hne
  obtain ⟨V, W, hV, hW, hrV, hsW, hVW⟩ := t2_separation hne
  apply hAB
  apply ((hA V (hV.mem_nhds hrV)).union (hB W (hW.mem_nhds hsW))).subset
  rintro a ⟨haA, haB⟩
  by_cases haV : u a ∈ V
  · right
    exact ⟨haB, fun haW => Set.disjoint_left.mp hVW haV haW⟩
  · exact Or.inl ⟨haA, haV⟩

/-- A color support cannot have only countably many convergent family labels
of that eventual color. The family is maximal among all infinite subsets,
not only the convergent ones. -/
theorem color_support_fiber_uncountable {ι : Type*} [Nonempty ι]
    (M : ι → Set ℕ) (u : ℕ → unitInterval) (l : ι → unitInterval)
    (hmad : MADFamily (range M)) (hc : ∀ i, ConvergesOn u (M i) (l i))
    (D : Set ℕ) (hpartition : Partitions M D)
    (r : unitInterval) (hr : r ∈ ColorSupport M u D) :
    ¬ {i | l i = r ∧ (M i \ D).Finite}.Countable := by
  classical
  intro hcount
  let e : ℕ → ι := Set.enumerateCountable hcount (Classical.choice inferInstance)
  have hcover : {i | l i = r ∧ (M i \ D).Finite} ⊆ range e :=
    Set.subset_range_enumerate hcount _
  have hex : ∀ k : ℕ, ∃ n : ℕ,
      n ∈ D ∧ k < n ∧ dist (u n) r < (1 : ℝ) / (k + 1) ∧
      ∀ j ≤ k, n ∉ M (e j) := by
    intro k
    let F : Finset ι := (Finset.range (k + 1)).image e
    have hsmall := hr (Metric.ball r ((1 : ℝ) / (k + 1)))
      (Metric.ball_mem_nhds r (by positivity))
    by_contra hno
    apply hsmall
    refine ⟨F, {n | n ≤ k}, finite_le_nat k, ?_⟩
    rintro n ⟨hnV, hnD⟩
    by_cases hnk : n ≤ k
    · exact Or.inr hnk
    · left
      have hnball : dist (u n) r < (1 : ℝ) / (k + 1) := hnV
      have hbad : ¬ ∀ j ≤ k, n ∉ M (e j) := by
        intro havoid
        exact hno ⟨n, hnD, Nat.lt_of_not_ge hnk, hnball, havoid⟩
      push_neg at hbad
      obtain ⟨j, hj, hn⟩ := hbad
      exact mem_iUnion.mpr ⟨e j, mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩, hn⟩⟩
  choose f hf using hex
  have hE : (range f).Infinite := by
    intro hfin
    obtain ⟨k, hk⟩ := hfin.bddAbove
    exact (not_lt_of_ge (hk (mem_range_self k))) (hf k).2.1
  have hfD : range f ⊆ D := by
    rintro n ⟨k, rfl⟩
    exact (hf k).1
  have hft : Tendsto (u ∘ f) atTop (𝓝 r) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => (hf k).2.2.1.le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hcE : ConvergesOn u (range f) r := convergesOn_range f u r hft
  obtain ⟨A, ⟨i, rfl⟩, hi⟩ := hmad.2 (range f) hE
  have hlimit : l i = r :=
    (convergesOn_eq_of_infinite_inter u hcE (hc i) hi).symm
  have hcolor : (M i \ D).Finite := by
    rcases hpartition i with h | h
    · exact h
    · exact (hi (h.subset (fun n hn => ⟨hn.2, hfD hn.1⟩))).elim
  obtain ⟨j, hj⟩ := hcover ⟨hlimit, hcolor⟩
  apply hi
  apply ((finite_lt_nat j).image f).subset
  rintro n ⟨⟨k, rfl⟩, hnM⟩
  refine ⟨k, ?_, rfl⟩
  by_contra hkj
  exact (hf k).2.2.2 j (Nat.le_of_not_gt hkj) (by simpa only [hj] using hnM)

end D5.S3.Topology.AlmostDisjoint.ColorFiberDiagonal

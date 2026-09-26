/- GID: D5/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DagSemantics/DepthFirst/Postorder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: DFS postorder uniqueness, support, and return paths for forward edges. -/

import D5.S3.ConceptDynamics.DagSemantics.DepthFirst.ForestInvariant
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup

namespace AdjListClass.IsDFSForest

variable
  {V : Type*} {Info : Type*}
  {EColl : Type*} [ToList EColl Info] [EmptyCollection EColl]
  [LawfulEmptyCollection EColl Info]
  {StarColl : Type*} [DefaultDict.ReadOnly StarColl V EColl fun _ ↦ ∅]
  {G : Type*} [AdjListClass G V Info EColl StarColl] {g : G}
  {i o : Set V} {f : Forest V}

/-- A DFS postorder is duplicate-free, enumerates the forest support, and every
forward edge in that order has a return path. The last clause exposes exactly
where acyclicity rules out an incorrectly ordered dependency. -/
theorem post_spec (hf : IsDFSForest g i o f) :
    f.post.Nodup ∧
      (∀ v, v ∈ f.post ↔ v ∈ f.support) ∧
      f.post.Pairwise (fun earlier later => Adj g earlier later → Reachable g later earlier) := by
  induction hf with
  | nil i => simp [Forest.post, Forest.support]
  | @node i o v c s m hv hc roots succ hs ihc ihs =>
    rcases ihc with ⟨hcn, hcm, hcp⟩
    rcases ihs with ⟨hsn, hsm, hsp⟩
    have hvm : v ∈ m := by
      rw [← hc.union]
      exact Or.inl (Or.inl rfl)
    have hcsub : c.support ⊆ m := by
      intro x hx
      rw [← hc.union]
      exact Or.inr hx
    have hnotc : v ∉ c.support := by
      intro hvc
      have hmem : v ∈ insert v i ∩ c.support := ⟨Or.inl rfl, hvc⟩
      rw [hc.inter] at hmem
      exact hmem
    have hdis : ∀ x ∈ m, x ∉ s.support := by
      intro x hxm hxs
      have hmem : x ∈ m ∩ s.support := ⟨hxm, hxs⟩
      rw [hs.inter] at hmem
      exact hmem
    refine ⟨?_, ?_, ?_⟩
    · simp only [Forest.post, List.nodup_append, List.nodup_cons]
      refine ⟨hcn, ⟨?_, hsn⟩, ?_⟩
      · exact fun h => hdis v hvm ((hsm v).mp h)
      · intro x hxc y hxs hxy
        subst y
        rcases List.mem_cons.mp hxs with hxv | hxs
        · subst x
          exact hnotc ((hcm v).mp hxc)
        · exact hdis x (hcsub ((hcm x).mp hxc)) ((hsm x).mp hxs)
    · intro x
      simp only [Forest.post, List.mem_append, List.mem_cons, hcm, hsm,
        Forest.support, Set.mem_insert_iff, Set.mem_union]
      tauto
    · simp only [Forest.post, List.pairwise_append, List.pairwise_cons]
      refine ⟨hcp, ⟨?_, hsp⟩, ?_⟩
      · intro x hxs hvx
        exact (hdis x (succ (by exact ⟨v, rfl, hvx⟩)) ((hsm x).mp hxs)).elim
      · intro x hxc y hys hxy
        rcases List.mem_cons.mp hys with hyv | hys
        · subst y
          obtain ⟨r, hr, hrx⟩ := hc.sound x ((hcm x).mp hxc)
          have hvr : Adj g v r := by
            obtain ⟨a, ha, har⟩ := roots hr
            simpa only [Set.mem_singleton_iff] using ha ▸ har
          exact Nonempty.map2 .comp (hvr.map (·.toPath)) hrx
        · exact (hdis y (hc.succSet_support_subset
            ⟨x, (hcm x).mp hxc, hxy⟩) ((hsm y).mp hys)).elim

end AdjListClass.IsDFSForest

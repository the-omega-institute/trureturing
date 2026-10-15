/- GID: D5/S3/Combinatorics/Graph/Walks/ActualOpenedChildInventory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualOpenedChildInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover the Actual Opened P Child Inventory. -/
import D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualOpenedChildInventory

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- The ordinary P supplier path has the full previous joint inventory,
with only its actual second prefix edge removed and every old marked edge
restored. The original source cycle and both actual partitions stay fixed. -/
theorem actual_opened_child_from_joint_partition
    {base ℓ s t z x y : V}
    (w : G.Walk base base) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ w.edges)
    (d : G.Walk ℓ z) (tail : G.Walk t z)
    (hₐ : G.Adj ℓ s) (h_b : G.Adj s t)
    (hd : d = (tail.cons h_b).cons hₐ)
    (rest : List (Piece G))
    (hjfull : ∀ v,
      ((⟨ℓ, z, d⟩ :: rest).flatMap fun p : Piece G => p.walk.support).count v = 1)
    (hje : ∀ e, e ∈ ((⟨ℓ, z, d⟩ :: rest).flatMap fun p : Piece G => p.walk.edges) ↔
      e ∈ w.edges ∧ e ∉ E)
    (q : G.Walk x y) (hq : q.IsHamiltonian)
    (hopen : ∀ e, e ∈ q.edges ↔ e ∈ w.edges ∧ e ≠ s(s, t)) :
    q.support.Perm (d.support ++ rest.flatMap fun p => p.walk.support) ∧
    q.edges.Perm ((rest.flatMap fun p => p.walk.edges) ++
      tail.edges ++ [s(ℓ, s)] ++ E.toList) := by
  classical
  have hjn : ((⟨ℓ, z, d⟩ :: rest).flatMap fun p : Piece G => p.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun v => by rw [hjfull v])
  let kept := s(ℓ, s) :: (tail.edges ++ rest.flatMap fun p => p.walk.edges)
  have hn := actual_path_partition_edges_nodup (⟨ℓ, z, d⟩ :: rest) hjn
  have hnold : (s(ℓ, s) :: s(s, t) ::
      (tail.edges ++ rest.flatMap fun p => p.walk.edges)).Nodup := by
    simpa only [List.flatMap_cons, hd, SimpleGraph.Walk.edges_cons,
      List.cons_append] using hn
  obtain ⟨ha, hna⟩ := List.nodup_cons.mp hnold
  obtain ⟨hb, hnb⟩ := List.nodup_cons.mp hna
  have hnkept : kept.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, hnb⟩
    intro h
    exact ha (List.mem_cons_of_mem _ h)
  have hab : s(ℓ, s) ≠ s(s, t) := by
    intro he
    exact ha (List.mem_cons.mpr (Or.inl he))
  have hcutjoint : s(s, t) ∈
      ((⟨ℓ, z, d⟩ :: rest).flatMap fun p : Piece G => p.walk.edges) := by
    simp only [List.flatMap_cons, hd, SimpleGraph.Walk.edges_cons,
      List.cons_append, List.mem_cons]
    exact Or.inr (Or.inl True.intro)
  have hcutE : s(s, t) ∉ E := (hje _).mp hcutjoint |>.2
  have hk (e : Sym2 V) : e ∈ kept ↔
      e ∈ ((⟨ℓ, z, d⟩ :: rest).flatMap fun p : Piece G => p.walk.edges) ∧
        e ≠ s(s, t) := by
    simp only [kept, List.flatMap_cons, hd, SimpleGraph.Walk.edges_cons,
      List.cons_append, List.mem_cons]
    constructor
    · intro he
      refine ⟨?_, ?_⟩
      · rcases he with he | he
        · exact Or.inl he
        · exact Or.inr (Or.inr he)
      · rcases he with he | he
        · intro hc
          exact hab (he.symm.trans hc)
        · intro hc
          exact hb (hc ▸ he)
    · rintro ⟨he, hne⟩
      rcases he with he | he | he
      · exact Or.inl he
      · exact (hne he).elim
      · exact Or.inr he
  have hdis : List.Disjoint kept E.toList := by
    apply List.disjoint_left.mpr
    intro e he hElist
    exact ((hje e).mp ((hk e).mp he).1).2 (Finset.mem_toList.mp hElist)
  have hnall : (kept ++ E.toList).Nodup :=
    List.nodup_append'.mpr ⟨hnkept, E.nodup_toList, hdis⟩
  have hperm : q.edges.Perm (kept ++ E.toList) := by
    apply (List.perm_ext_iff_of_nodup hq.isPath.isTrail.edges_nodup hnall).mpr
    intro e
    rw [hopen e, List.mem_append, Finset.mem_toList, hk e, hje e]
    constructor
    · rintro ⟨he, hne⟩
      by_cases heE : e ∈ E
      · exact Or.inr heE
      · exact Or.inl ⟨⟨he, heE⟩, hne⟩
    · rintro (⟨⟨he, _⟩, hne⟩ | heE)
      · exact ⟨he, hne⟩
      · refine ⟨hE e heE, ?_⟩
        intro he
        exact hcutE (he ▸ heE)
  refine ⟨?_, hperm.trans ?_⟩
  · apply List.perm_iff_count.mpr
    intro v
    rw [hq v]
    simpa only [List.flatMap_cons] using (hjfull v).symm
  · apply List.perm_iff_count.mpr
    intro e
    simp only [kept, List.count_append, List.count_cons, List.count_nil]
    omega

#print axioms actual_opened_child_from_joint_partition

end D5.S3.Combinatorics.Graph.Walks.ActualOpenedChildInventory

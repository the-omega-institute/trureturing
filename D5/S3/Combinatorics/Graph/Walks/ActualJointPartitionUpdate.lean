/- GID: D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual recombination exhausts one supplied Hamilton cycle and retains exactly its uncut edges with distinct actual cuts. -/
import D5.S3.Combinatorics.Graph.Walks.ActualJointThreePathUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointThreePathUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

private theorem filter_complement_of_nodup {α : Type*} [DecidableEq α]
    (kept removed : List α) (hn : (kept ++ removed).Nodup) :
    (kept ++ removed).filter (fun e => decide (e ∉ removed.toFinset)) = kept := by
  have hd := (List.nodup_append'.mp hn).2.2
  have hk : kept.filter (fun e => decide (e ∉ removed.toFinset)) = kept := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq, List.mem_toFinset]
    intro hr
    exact List.disjoint_left.mp hd he hr
  have hr : removed.filter (fun e => decide (e ∉ removed.toFinset)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he hnot
    exact (of_decide_eq_true hnot) (List.mem_toFinset.mpr he)
  rw [List.filter_append, hk, hr, List.append_nil]

private theorem pieces_support_length (pieces : List (Piece G)) :
    (pieces.flatMap fun z => z.walk.support).length =
      (pieces.flatMap fun z => z.walk.edges).length + pieces.length := by
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_edges]
    omega

/-- Exhaustive recombination is performed on the same actual Hamilton
cycle. `deleted` contains the old P marked edges, as obtained from the
previous actual joint partition. The P supplier edge `s(s,t)` is already
absent from this parent cycle: its source inventory uses `tail` and the
single retained a edge. Only the two Q cuts are newly deleted from that
inventory. Source-cycle simplicity earns all target cut distinctness and
excludes every target cut from the recombined paths. -/
theorem actual_joint_partition_of_cycle_inventory
    {base ℓ s t z a ℓ₀ r₀ ℓ₁ r₁ b : V}
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (rest : List (Piece G))
    (d : G.Walk ℓ z) (tail : G.Walk t z)
    (hₐ : G.Adj ℓ s) (h_b : G.Adj s t)
    (hd : d = (tail.cons h_b).cons hₐ)
    (Λ : G.Walk a b)
    (q₀ : G.Walk a ℓ₀) (q₁ : G.Walk r₀ ℓ₁) (q₂ : G.Walk r₁ b)
    (hQs : q₀.support ++ q₁.support ++ q₂.support = Λ.support)
    (hQe : q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
      Λ.edges)
    (chain : G.Walk b s) (hchain : ¬ chain.Nil) (hseam : G.Adj t a)
    (deleted : List (Sym2 V))
    (hsourceSupport : c.support.tail.Perm
      ((d.support ++ Λ.support ++ chain.support.tail.dropLast) ++
        (rest.flatMap fun p => p.walk.support)))
    (hsourceEdges : c.edges.Perm
      ((rest.flatMap fun p => p.walk.edges) ++ tail.edges ++ [s(ℓ, s)] ++
        Λ.edges ++ chain.edges ++ [s(t, a)] ++ deleted)) :
    ∃ new₀ : G.Walk z ℓ₀, ∃ new₁ : G.Walk r₀ ℓ₁, ∃ new₂ : G.Walk r₁ ℓ,
      let pieces : List (Piece G) :=
        [⟨z, ℓ₀, new₀⟩, ⟨r₀, ℓ₁, new₁⟩, ⟨r₁, ℓ, new₂⟩] ++ rest
      let cuts := (s(ℓ₀, r₀) :: s(ℓ₁, r₁) :: deleted).toFinset
      (∀ p ∈ pieces, p.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun p => p.walk.support).count v = 1) ∧
      (pieces.flatMap fun p => p.walk.support).Perm c.support.tail ∧
      (pieces.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ cuts)) ∧
      (∀ e, e ∈ (pieces.flatMap fun p => p.walk.edges) ↔
        e ∈ c.edgeSet ∧ e ∉ cuts) ∧
      (∀ e ∈ cuts, e ∈ c.edgeSet) ∧ pieces.length = cuts.card ∧
      new₀ = tail.reverse.append (q₀.cons hseam) ∧
      new₁ = q₁ ∧ new₂ = (q₂.append chain).concat hₐ.symm ∧
      (s(ℓ₀, r₀) :: s(ℓ₁, r₁) :: deleted).Nodup := by
  classical
  have hccount : ∀ v, c.support.tail.count v = 1 :=
    (SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp hc).2
  have hnsource : ((d.support ++ Λ.support ++ chain.support.tail.dropLast) ++
      (rest.flatMap fun p => p.walk.support)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro v
    rw [← hsourceSupport.count_eq v, hccount v]
  have hnregion : (d.support ++ Λ.support ++ chain.support.tail.dropLast).Nodup :=
    (List.nodup_append'.mp hnsource).1
  obtain ⟨new₀, new₁, new₂, _, _, _, _, hs, he, he₀, he₁, he₂⟩ :=
    actual_joint_three_path_update d tail hₐ h_b hd Λ q₀ q₁ q₂ hQs
      chain hchain hseam hnregion
  let pieces : List (Piece G) :=
    [⟨z, ℓ₀, new₀⟩, ⟨r₀, ℓ₁, new₁⟩, ⟨r₁, ℓ, new₂⟩] ++ rest
  let removed : List (Sym2 V) := s(ℓ₀, r₀) :: s(ℓ₁, r₁) :: deleted
  let cuts := removed.toFinset
  have hsupport : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail := by
    have h := hs.append (List.Perm.refl (rest.flatMap fun p => p.walk.support))
    simpa only [pieces, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc] using h.trans hsourceSupport.symm
  have hcount (v : V) : (pieces.flatMap fun p => p.walk.support).count v = 1 :=
    (hsupport.count_eq v).trans (hccount v)
  have hn : (pieces.flatMap fun p => p.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun v => by rw [hcount v])
  have hpaths (p : Piece G) (hp : p ∈ pieces) : p.walk.IsPath :=
    SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp hn).1 p hp)
  have hecounts (e : Sym2 V) := he.count_eq e
  have htargetEdges : c.edges.Perm
      ((pieces.flatMap fun p => p.walk.edges) ++ removed) := by
    apply hsourceEdges.trans
    apply List.perm_iff_count.mpr
    intro e
    have h := hecounts e
    simp only [List.count_append, List.count_cons, List.count_nil] at h
    rw [← hQe]
    simp only [pieces, removed, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.count_append, List.count_cons, List.count_nil]
    omega
  have hened : ((pieces.flatMap fun p => p.walk.edges) ++ removed).Nodup :=
    htargetEdges.nodup_iff.mp hc.isCycle.isTrail.edges_nodup
  have hremoved : removed.Nodup := (List.nodup_append'.mp hened).2.1
  have hfiltered : (c.edges.filter fun e => decide (e ∉ cuts)).Perm
      (pieces.flatMap fun p => p.walk.edges) := by
    have h := List.Perm.filter (fun e => decide (e ∉ cuts)) htargetEdges
    simpa only [cuts, filter_complement_of_nodup _ _ hened] using h
  have hcuts (e : Sym2 V) (hecut : e ∈ cuts) : e ∈ c.edgeSet := by
    change e ∈ c.edges
    apply htargetEdges.mem_iff.mpr
    apply List.mem_append.mpr
    exact Or.inr (List.mem_toFinset.mp hecut)
  have hlength : pieces.length = cuts.card := by
    have hslen := hsupport.length_eq
    have helen := htargetEdges.length_eq
    have hplen := pieces_support_length pieces
    have hrcard : cuts.card = removed.length := List.toFinset_card_of_nodup hremoved
    simp only [List.length_tail, SimpleGraph.Walk.length_support,
      List.length_append, SimpleGraph.Walk.length_edges] at hslen helen
    rw [hrcard]
    omega
  refine ⟨new₀, new₁, new₂, hpaths, hcount, hsupport, hfiltered.symm, ?_,
    hcuts, hlength, he₀, he₁, he₂, hremoved⟩
  intro e
  rw [← hfiltered.mem_iff]
  simp only [List.mem_filter, decide_eq_true_eq, SimpleGraph.Walk.mem_edgeSet]
  rfl

#print axioms actual_joint_partition_of_cycle_inventory

end D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

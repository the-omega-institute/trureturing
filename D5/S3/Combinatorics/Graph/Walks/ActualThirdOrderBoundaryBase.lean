/- GID: D5/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualThirdOrderBoundaryBase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eight actual third-order joint paths restore both exhaustive four-path boundary partitions on the same Hamilton cycle. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private actual_joint_split_cut_inventory from
  D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
open private filter_complement_of_nodup from
  D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

private abbrev R (p : Bool × Fin 4 × Bool → V) (t : Bool) (i : Fin 4) : V :=
  p (t, i, false)
private abbrev L (p : Bool × Fin 4 × Bool → V) (t : Bool) (i : Fin 4) : V :=
  p (t, i, true)
private def cut (p : Bool × Fin 4 × Bool → V) (t : Bool) (i : Fin 4) : Sym2 V :=
  s(R p t i, L p t i)
private def cuts (p : Bool × Fin 4 × Bool → V) (t : Bool) : Finset (Sym2 V) :=
  Finset.univ.image (cut p t)

private theorem cut_injective (p : Bool × Fin 4 × Bool → V) (hp : Function.Injective p)
    (t : Bool) : Function.Injective (cut p t) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
  · exact congrArg (fun q : Bool × Fin 4 × Bool => q.2.1) (hp h)
  · have hside := congrArg (fun q : Bool × Fin 4 × Bool => q.2.2) (hp h)
    cases hside

private theorem cuts_toList (p : Bool × Fin 4 × Bool → V) (hp : Function.Injective p)
    (t : Bool) : (cuts p t).toList.Perm (List.ofFn (cut p t)) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
    (List.nodup_ofFn.mpr (cut_injective p hp t))).mpr
  intro e
  simp only [cuts, Finset.mem_toList, Finset.mem_image, Finset.mem_univ, true_and,
    List.mem_ofFn]

private theorem partition_from_restored_edges {base : V} (c : G.Walk base base)
    (hc : c.IsCycle) (E : Finset (Sym2 V)) (ps : List (Piece G))
    (hs : (ps.flatMap fun q => q.walk.support).Perm c.support.tail)
    (he : c.edges.Perm ((ps.flatMap fun q => q.walk.edges) ++ E.toList)) :
    ActualCyclePartition c E ps := by
  have hn : ((ps.flatMap fun q => q.walk.edges) ++ E.toList).Nodup :=
    he.nodup_iff.mp hc.isTrail.edges_nodup
  have hf := List.Perm.filter (fun e => decide (e ∉ E)) he
  rw [show ((ps.flatMap fun q => q.walk.edges) ++ E.toList).filter
      (fun e => decide (e ∉ E)) = ps.flatMap fun q => q.walk.edges by
    simpa only [Finset.toList_toFinset] using
      filter_complement_of_nodup _ E.toList hn] at hf
  refine ⟨hs, hf.symm, ?_⟩
  intro e heE
  exact he.mem_iff.mpr (List.mem_append.mpr (Or.inr (Finset.mem_toList.mpr heE)))

/-- The eight literal J3 paths yield B3^0=O3 and B3^1=E3 by actual
restoration. The first primary path is the actual distinguished J path d;
the first opposite path starts with cross.reverse and the restored zero
cut. This initializes exactly the simultaneous state needed from k3 on. -/
theorem actual_third_order_boundary_base {base : V}
    (p : Bool × Fin 4 × Bool → V) (hp : Function.Injective p)
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (d : G.Walk (L p false 0) (L p false 2))
    (cross : G.Walk (R p false 0) (L p true 0))
    (g : G.Walk (R p true 0) (L p true 1))
    (a : G.Walk (R p false 1) (R p false 2))
    (b : G.Walk (L p true 3) (R p false 3))
    (q : G.Walk (R p true 2) (L p false 3))
    (e : G.Walk (R p true 1) (R p true 3))
    (f : G.Walk (L p true 2) (L p false 1))
    (hjoint : ActualCyclePartition c (cuts p false ∪ cuts p true)
      [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a⟩,
        ⟨_, _, b⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩]) :
    ∃ primary₁ : G.Walk (R p false 0) (R p false 3),
      ∃ primary₂ : G.Walk (L p false 1) (L p false 3),
      ∃ opposite₀ : G.Walk (L p true 0) (L p true 2),
      ∃ opposite₂ : G.Walk (R p true 2) (L p true 3),
      ActualTwoOrderPartitions c (cuts p false) (cuts p true)
        [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a⟩,
          ⟨_, _, b⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩]
        [⟨_, _, d⟩, ⟨_, _, a⟩, ⟨_, _, primary₁⟩, ⟨_, _, primary₂⟩]
        [⟨_, _, opposite₀⟩, ⟨_, _, g⟩, ⟨_, _, e⟩, ⟨_, _, opposite₂⟩] ∧
      ∃ hzero : G.Adj (R p false 0) (L p false 0),
        ∃ tail : G.Walk (L p false 2) (L p true 2),
          opposite₀ = (cross.reverse.concat hzero).append (d.append tail) := by
  classical
  let K := cuts p false
  let H := cuts p true
  let joint : List (Piece G) :=
    [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a⟩,
      ⟨_, _, b⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩]
  have hdisjoint : Disjoint K H := by
    apply Finset.disjoint_left.mpr
    intro z hzK hzH
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzK
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzH
    have he : cut p false i = cut p true j := hi.trans hj.symm
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
    · have ht := congrArg (fun z : Bool × Fin 4 × Bool => z.1) (hp h)
      cases ht
    · have ht := congrArg (fun z : Bool × Fin 4 × Bool => z.1) (hp h)
      cases ht
  have hactual (t : Bool) (i : Fin 4) : G.Adj (R p t i) (L p t i) := by
    apply c.adj_of_mem_edges
    apply hjoint.cut_mem
    apply Finset.mem_union.mpr
    have hi : cut p t i ∈ cuts p t := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    cases t
    · exact Or.inl hi
    · exact Or.inr hi
  let primary₁ := cross.append ((g.append ((e.append
    (b.cons (hactual true 3))).cons (hactual true 1).symm)).cons (hactual true 0).symm)
  let primary₂ := f.reverse.append (q.cons (hactual true 2).symm)
  let tail := a.reverse.append (f.reverse.cons (hactual false 1))
  let opposite₀ := cross.reverse.append ((d.append
    (tail.cons (hactual false 2).symm)).cons (hactual false 0))
  let opposite₂ := q.append (b.reverse.cons (hactual false 3).symm)
  let primary : List (Piece G) :=
    [⟨_, _, d⟩, ⟨_, _, a⟩, ⟨_, _, primary₁⟩, ⟨_, _, primary₂⟩]
  let opposite : List (Piece G) :=
    [⟨_, _, opposite₀⟩, ⟨_, _, g⟩, ⟨_, _, e⟩, ⟨_, _, opposite₂⟩]
  have hps : (primary.flatMap fun z => z.walk.support).Perm c.support.tail := by
    apply List.Perm.trans _ hjoint.support
    apply List.perm_iff_count.mpr
    intro v
    simp only [primary, primary₁, primary₂, joint, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_reverse,
      List.count_append, List.count_reverse]
    omega
  have hos : (opposite.flatMap fun z => z.walk.support).Perm c.support.tail := by
    apply List.Perm.trans _ hjoint.support
    apply List.perm_iff_count.mpr
    intro v
    simp only [opposite, opposite₀, opposite₂, tail, joint, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_reverse,
      List.count_append, List.count_reverse]
    omega
  have hcutK := cuts_toList p hp false
  have hcutH := cuts_toList p hp true
  have hsource := actual_joint_split_cut_inventory c hc.isCycle
    (joint.flatMap fun z => z.walk.edges) K H hdisjoint hjoint.edges hjoint.cut_mem
  have hpe : c.edges.Perm ((primary.flatMap fun z => z.walk.edges) ++ K.toList) := by
    apply hsource.trans
    apply List.perm_iff_count.mpr
    intro z
    have hH := hcutH.count_eq z
    change H.toList.count z =
      ([cut p true 0, cut p true 1, cut p true 2, cut p true 3] : List (Sym2 V)).count z at hH
    simp only [List.count_cons, List.count_nil] at hH
    simp only [primary, primary₁, primary₂, joint, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_reverse,
      cut, Sym2.eq_swap, List.count_append, List.count_cons, List.count_nil,
      List.count_reverse, beq_iff_eq] at hH ⊢
    omega
  have hsourceOpp : c.edges.Perm
      ((joint.flatMap fun z => z.walk.edges) ++ K.toList ++ H.toList) := by
    exact actual_joint_split_cut_inventory c hc.isCycle _ H K hdisjoint.symm
      (by simpa only [Finset.union_comm] using hjoint.edges)
      (by simpa only [Finset.union_comm] using hjoint.cut_mem)
  have hoe : c.edges.Perm ((opposite.flatMap fun z => z.walk.edges) ++ H.toList) := by
    apply hsourceOpp.trans
    apply List.perm_iff_count.mpr
    intro z
    have hK := hcutK.count_eq z
    change K.toList.count z =
      ([cut p false 0, cut p false 1, cut p false 2, cut p false 3] : List (Sym2 V)).count z at hK
    simp only [List.count_cons, List.count_nil] at hK
    simp only [opposite, opposite₀, opposite₂, tail, joint, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_reverse,
      cut, Sym2.eq_swap, List.count_append, List.count_cons, List.count_nil,
      List.count_reverse, beq_iff_eq] at hK ⊢
    omega
  refine ⟨primary₁, primary₂, opposite₀, opposite₂,
    ⟨hc.isCycle, hdisjoint, hjoint,
      partition_from_restored_edges c hc.isCycle K primary hps hpe,
      partition_from_restored_edges c hc.isCycle H opposite hos hoe⟩,
    hactual false 0, tail.cons (hactual false 2).symm, ?_⟩
  simp only [opposite₀, SimpleGraph.Walk.concat_append]

#print axioms actual_third_order_boundary_base

end D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase

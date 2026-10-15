/- GID: D5/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualSimultaneousBoundaryAdvance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One supplied current joint partition simultaneously earns both restored boundary inventories and their literal distinguished prefixes. -/
import D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs
import D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualJointEndpointPairs
open D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory
open D5.S3.Combinatorics.Graph.Walks.ActualPriorBoundaryInputs
open D5.S3.Combinatorics.Graph.Walks.ActualSingleOrderBoundaryUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Exact support and filtered-edge inventories of a particular cycle.
Keeping the cycle as a parameter prevents separately chosen realizations
from entering the three parts of a simultaneous state. -/
structure ActualCyclePartition {base : V} (w : G.Walk base base)
    (cuts : Finset (Sym2 V)) (pieces : List (Piece G)) : Prop where
  support : (pieces.flatMap fun p => p.walk.support).Perm w.support.tail
  edges : (pieces.flatMap fun p => p.walk.edges).Perm
    (w.edges.filter fun e => decide (e ∉ cuts))
  cut_mem : ∀ e ∈ cuts, e ∈ w.edges

/-- All three partitions refer to this same actual cycle; the two single
orders delete opposite groups of its joint cuts. -/
structure ActualTwoOrderPartitions {base : V} (w : G.Walk base base)
    (K H : Finset (Sym2 V)) (joint primary opposite : List (Piece G)) : Prop where
  cycle : w.IsCycle
  disjoint : Disjoint K H
  joint_partition : ActualCyclePartition w (K ∪ H) joint
  primary_partition : ActualCyclePartition w K primary
  opposite_partition : ActualCyclePartition w H opposite

/-- Close both actual boundary updates at once. Current joint cuts
exchange the old orders after erasing the two new zero cuts. The new
distinguished J piece is exactly new₀.reverse and the new crossing piece
is exactly new₁. Their actual prefixes in the two returned full boundaries
are conclusions, so they can feed the next step without new route axioms. -/
theorem actual_simultaneous_boundary_advance
    {priorBase base ℓ z r x y₀ y₁ ℓ₀ r₀ ℓ₁ r₁ : V}
    (prior : G.Walk priorBase priorBase)
    (d : G.Walk ℓ z) (cross : G.Walk r x) (jointrest : List (Piece G))
    (old₀ : G.Walk ℓ y₀) (primaryrest : List (Piece G))
    (old₁ : G.Walk x y₁) (oppositerest : List (Piece G))
    (oldK oldH : Finset (Sym2 V))
    (hprior : ActualTwoOrderPartitions prior oldK oldH
      (⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest)
      (⟨ℓ, y₀, old₀⟩ :: primaryrest) (⟨x, y₁, old₁⟩ :: oppositerest))
    (hpriorSeam : s(r, ℓ) ∈ oldK)
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (new₀ : G.Walk z ℓ₀) (new₁ : G.Walk r₀ ℓ₁) (new₂ : G.Walk r₁ ℓ)
    (K H : Finset (Sym2 V)) (hdisjoint : Disjoint K H)
    (hcurrent : ActualCyclePartition c (K ∪ H)
      (⟨z, ℓ₀, new₀⟩ :: ⟨r₀, ℓ₁, new₁⟩ :: ⟨r₁, ℓ, new₂⟩ ::
        ⟨r, x, cross⟩ :: jointrest))
    (hzero₀ : s(ℓ₀, r₀) ∈ K) (hzero₁ : s(ℓ₁, r₁) ∈ H)
    (herase₀ : K.erase s(ℓ₀, r₀) = oldH)
    (herase₁ : H.erase s(ℓ₁, r₁) = oldK) :
    ∃ primary₀ : G.Walk ℓ₀ y₁, ∃ primary₁ : G.Walk r₀ x,
      ∃ opposite₀ : G.Walk ℓ₁ y₀, ∃ opposite₁ : G.Walk r₁ ℓ,
      let joint : List (Piece G) :=
        ⟨ℓ₀, z, new₀.reverse⟩ :: ⟨r₀, ℓ₁, new₁⟩ :: ⟨r₁, ℓ, new₂⟩ ::
          ⟨r, x, cross⟩ :: jointrest
      let primary : List (Piece G) :=
        [⟨ℓ₀, y₁, primary₀⟩, ⟨r₀, x, primary₁⟩] ++ oppositerest
      let opposite : List (Piece G) :=
        [⟨ℓ₁, y₀, opposite₀⟩, ⟨r₁, ℓ, opposite₁⟩] ++ primaryrest
      ActualTwoOrderPartitions c K H joint primary opposite ∧
      (∀ p ∈ joint ++ primary ++ opposite, p.walk.IsPath) ∧
      endpointPairs primary =
        (endpointPairs (⟨x, y₁, old₁⟩ :: oppositerest)).erase s(x, y₁) ∪
          {s(ℓ₀, y₁), s(r₀, x)} ∧
      endpointPairs opposite =
        (endpointPairs (⟨ℓ, y₀, old₀⟩ :: primaryrest)).erase s(ℓ, y₀) ∪
          {s(ℓ₁, y₀), s(r₁, ℓ)} ∧
      s(r₀, ℓ₀) ∈ K ∧
      ∃ hnext : G.Adj r₀ ℓ₀, ∃ tail₀ : G.Walk z y₀, ∃ tail₁ : G.Walk z y₁,
        tail₀.IsPath ∧ tail₁.IsPath ∧
        primary₀ = new₀.reverse.append tail₁ ∧
        opposite₀ = (new₁.reverse.concat hnext).append (new₀.reverse.append tail₀) ∧
        opposite₁ = new₂ := by
  classical
  let remaining : List (Piece G) := ⟨r, x, cross⟩ :: jointrest
  have hcurrentSupport : c.support.tail.Perm
      (new₀.support ++ new₁.support ++ new₂.support ++
        remaining.flatMap fun p => p.walk.support) := by
    simpa only [remaining, List.flatMap_cons, List.append_assoc] using hcurrent.support.symm
  have hcurrentEdges : (new₀.edges ++ new₁.edges ++ new₂.edges ++
      remaining.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ K ∪ H)) := by
    simpa only [remaining, List.flatMap_cons, List.append_assoc] using hcurrent.edges
  have hpriorSwapped : ((⟨ℓ, z, d⟩ :: ⟨r, x, cross⟩ :: jointrest).flatMap
      fun p : Piece G => p.walk.edges).Perm
        (prior.edges.filter fun e => decide (e ∉ oldH ∪ oldK)) := by
    simpa only [Finset.union_comm] using hprior.joint_partition.edges
  have hpriorCutsSwapped : ∀ e ∈ oldH ∪ oldK, e ∈ prior.edges := by
    simpa only [Finset.union_comm] using hprior.joint_partition.cut_mem
  obtain ⟨_, _, _, hn₀, hs₀, he₀, tail₀, hfactor₀, htail₀⟩ :=
    actual_prior_primary_boundary_inputs prior hprior.cycle d remaining old₀ primaryrest
      oldK oldH hprior.disjoint hprior.joint_partition.support hprior.primary_partition.support
      hprior.joint_partition.edges hprior.primary_partition.edges hprior.joint_partition.cut_mem
  obtain ⟨hpriorRestore, _, _, _, hn₁, hs₁, he₁, tail₁, hfactor₁, htail₁⟩ :=
    actual_prior_opposite_boundary_inputs prior hprior.cycle d cross jointrest old₁ oppositerest
      oldH oldK hprior.disjoint.symm hprior.joint_partition.support hprior.opposite_partition.support
      hpriorSwapped hprior.opposite_partition.edges hpriorCutsSwapped hpriorSeam
  have hs₁' : (old₁.support ++ oppositerest.flatMap fun p => p.walk.support).Perm
      (d.support ++ remaining.flatMap fun p => p.walk.support) := by
    simpa only [remaining, List.flatMap_cons, List.append_assoc] using hs₁
  have he₁' : (old₁.edges ++ oppositerest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (remaining.flatMap fun p => p.walk.edges) ++
        (H.erase s(ℓ₁, r₁)).toList) := by
    rw [herase₁]
    simpa only [remaining, List.flatMap_cons, List.append_assoc] using he₁
  have he₀' : (old₀.edges ++ primaryrest.flatMap fun p => p.walk.edges).Perm
      (d.edges ++ (remaining.flatMap fun p => p.walk.edges) ++
        (K.erase s(ℓ₀, r₀)).toList) := by
    rw [herase₀]
    exact he₀
  obtain ⟨hsource₁, _, _⟩ := actual_joint_half_cut_inventory c hc.isCycle _ K H hdisjoint
    hcurrentEdges hcurrent.cut_mem s(ℓ₁, r₁) hzero₁
  have hcurrentSwapped : (new₀.edges ++ new₁.edges ++ new₂.edges ++
      remaining.flatMap fun p => p.walk.edges).Perm
        (c.edges.filter fun e => decide (e ∉ H ∪ K)) := by
    simpa only [Finset.union_comm] using hcurrentEdges
  have hcurrentCutsSwapped : ∀ e ∈ H ∪ K, e ∈ c.edges := by
    simpa only [Finset.union_comm] using hcurrent.cut_mem
  obtain ⟨hsource₀, _, _⟩ := actual_joint_half_cut_inventory c hc.isCycle _ H K hdisjoint.symm
    hcurrentSwapped hcurrentCutsSwapped s(ℓ₀, r₀) hzero₀
  have hrestore₁ : G.Adj ℓ₁ r₁ :=
    c.adj_of_mem_edges (hcurrent.cut_mem _ (Finset.mem_union.mpr (Or.inr hzero₁)))
  have hrestore₀ : G.Adj ℓ₀ r₀ :=
    c.adj_of_mem_edges (hcurrent.cut_mem _ (Finset.mem_union.mpr (Or.inl hzero₀)))
  let front := cross.reverse.concat hpriorRestore
  obtain ⟨primary₀, primary₁, _, _, hps, hpe, _, hpc, _, hpp, hpformula, _⟩ :=
    actual_single_order_boundary_update c hc d front tail₁ old₁ hfactor₁
      oppositerest remaining hn₁ hs₁' (H.erase s(ℓ₁, r₁)).toList K.toList he₁'
      new₀ new₁ new₂ hrestore₁ hcurrentSupport hsource₁
  have hfactor₀' : old₀ = (SimpleGraph.Walk.nil : G.Walk ℓ ℓ).append (d.append tail₀) := by
    simpa only [SimpleGraph.Walk.nil_append] using hfactor₀
  obtain ⟨opposite₀, opposite₁, _, _, hos, hoe, _, hoc, _, hop, hoformula, hoother⟩ :=
    actual_single_order_first_cut_boundary_update c hc d .nil tail₀ old₀ hfactor₀'
      primaryrest remaining hn₀ hs₀ (K.erase s(ℓ₀, r₀)).toList H.toList he₀'
      new₀ new₁ new₂ hrestore₀ hcurrentSupport hsource₀
  let joint : List (Piece G) :=
    ⟨ℓ₀, z, new₀.reverse⟩ :: ⟨r₀, ℓ₁, new₁⟩ :: ⟨r₁, ℓ, new₂⟩ :: remaining
  let primary : List (Piece G) :=
    [⟨ℓ₀, y₁, primary₀⟩, ⟨r₀, x, primary₁⟩] ++ oppositerest
  let opposite : List (Piece G) :=
    [⟨ℓ₁, y₀, opposite₀⟩, ⟨r₁, ℓ, opposite₁⟩] ++ primaryrest
  have hjs : (joint.flatMap fun p => p.walk.support).Perm c.support.tail := by
    apply List.Perm.trans _ hcurrent.support
    simpa only [joint, remaining, List.flatMap_cons, SimpleGraph.Walk.support_reverse,
      List.append_assoc] using
      (List.reverse_perm new₀.support).append (List.Perm.refl
        (new₁.support ++ new₂.support ++ remaining.flatMap fun p => p.walk.support))
  have hje : (joint.flatMap fun p => p.walk.edges).Perm
      (c.edges.filter fun e => decide (e ∉ K ∪ H)) := by
    apply List.Perm.trans _ hcurrent.edges
    simpa only [joint, remaining, List.flatMap_cons, SimpleGraph.Walk.edges_reverse,
      List.append_assoc] using
      (List.reverse_perm new₀.edges).append (List.Perm.refl
        (new₁.edges ++ new₂.edges ++ remaining.flatMap fun p => p.walk.edges))
  have hp : ActualCyclePartition c K primary := by
    refine ⟨hps, ?_, ?_⟩
    · simpa only [Finset.toList_toFinset] using hpe
    · simpa only [Finset.toList_toFinset, SimpleGraph.Walk.mem_edgeSet] using hpc
  have ho : ActualCyclePartition c H opposite := by
    refine ⟨hos, ?_, ?_⟩
    · simpa only [Finset.toList_toFinset] using hoe
    · simpa only [Finset.toList_toFinset, SimpleGraph.Walk.mem_edgeSet] using hoc
  have hj : ActualCyclePartition c (K ∪ H) joint := ⟨hjs, hje, hcurrent.cut_mem⟩
  have path_of_support (pieces : List (Piece G))
      (hs : (pieces.flatMap fun p => p.walk.support).Perm c.support.tail)
      (p : Piece G) (hp : p ∈ pieces) : p.walk.IsPath :=
    SimpleGraph.Walk.IsPath.mk' ((List.nodup_flatMap.mp
      (hs.nodup_iff.mpr hc.isCycle.support_nodup)).1 p hp)
  refine ⟨primary₀, primary₁, opposite₀, opposite₁,
    ⟨hc.isCycle, hdisjoint, hj, hp, ho⟩, ?_, hpp, hop, ?_,
      hrestore₀.symm, tail₀, tail₁, htail₀, htail₁, hpformula, ?_, ?_⟩
  · intro p hmem
    have hmem' : p ∈ (joint ++ primary) ++ opposite := hmem
    rcases List.mem_append.mp hmem' with hfirst | hlast
    · rcases List.mem_append.mp hfirst with hjoint | hprimary
      · exact path_of_support joint hj.support p hjoint
      · exact path_of_support primary hp.support p hprimary
    · exact path_of_support opposite ho.support p hlast
  · simpa only [Sym2.eq_swap] using hzero₀
  · simpa only [SimpleGraph.Walk.concat_append, SimpleGraph.Walk.append_assoc] using hoformula
  · simpa only [SimpleGraph.Walk.reverse_nil, SimpleGraph.Walk.append_nil] using hoother

#print axioms actual_simultaneous_boundary_advance

end D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance

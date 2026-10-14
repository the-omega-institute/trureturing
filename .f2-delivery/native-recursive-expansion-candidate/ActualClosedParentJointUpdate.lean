/- UNCOMPILED actual closed-parent J update.
   Consume the real native parent constructor's literal child-route
   inventories, the actual opened P joint inventory, and the exhaustive
   actual Q slicing. The outside chain and complete next cut partition
   are constructed, not supplied as parent-state certificates. -/
import D5.S3.Combinatorics.Graph.Walks.ActualOuterChainExtraction
import D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualClosedParentJointUpdate

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualOuterChainExtraction
open D5.S3.Combinatorics.Graph.Walks.ActualJointPartitionUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Q is the actual first child path; the opened P is the actual final
child path. The intermediate child paths and all parent seams are those
of the same supplied cycle. P inventories come from the previous joint
partition and its actual supplier-edge opening. Q fragments come from
the earned two-cut order. This constructs the exhaustive next partition
and its three new endpoint pairs, keeping all other P pieces unchanged. -/
theorem actual_closed_parent_joint_partition
    {base ℓ s t z a ℓ₀ r₀ ℓ₁ r₁ b : V}
    (c : G.Walk base base) (hc : c.IsHamiltonianCycle)
    (d : G.Walk ℓ z) (tail : G.Walk t z)
    (hₐ : G.Adj ℓ s) (h_b : G.Adj s t)
    (hd : d = (tail.cons h_b).cons hₐ)
    (rest : List (Piece G))
    (P : G.Walk s t) (deleted : List (Sym2 V))
    (hPs : P.support.Perm (d.support ++ rest.flatMap fun p => p.walk.support))
    (hPe : P.edges.Perm ((rest.flatMap fun p => p.walk.edges) ++
      tail.edges ++ [s(ℓ, s)] ++ deleted))
    (Λ : G.Walk a b)
    (q₀ : G.Walk a ℓ₀) (q₁ : G.Walk r₀ ℓ₁) (q₂ : G.Walk r₁ b)
    (hQs : q₀.support ++ q₁.support ++ q₂.support = Λ.support)
    (hQe : q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
      Λ.edges)
    (others : List (Piece G))
    (hlink : Linked ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩]))
    (hbase : base = a) (hseam : G.Adj t a)
    (hcs : c.support.tail =
      ((⟨a, b, Λ⟩ :: (others ++ [⟨s, t, P⟩])).flatMap
        fun p : Piece G => p.walk.support).reverse)
    (hce : c.edges = s(base, finish ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩])) ::
      (chainEdges ⟨a, b, Λ⟩ (others ++ [⟨s, t, P⟩])).reverse) :
    ∃ chain : G.Walk b s,
      chain.support.tail.dropLast = (others.flatMap fun p => p.walk.support) ∧
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
        new₁ = q₁ ∧ new₂ = (q₂.append chain).concat hₐ.symm := by
  obtain ⟨chain, hchain, hinterior, hs, he⟩ :=
    actual_closed_route_outer_chain ⟨a, b, Λ⟩ ⟨s, t, P⟩ others hlink c hbase hcs hce
  have hsparent : c.support.tail.Perm
      ((d.support ++ Λ.support ++ chain.support.tail.dropLast) ++
        (rest.flatMap fun p => p.walk.support)) := by
    apply hs.trans
    apply List.perm_iff_count.mpr
    intro v
    have hp := hPs.count_eq v
    simp only [List.count_append] at hp ⊢
    omega
  have heparent : c.edges.Perm
      ((rest.flatMap fun p => p.walk.edges) ++ tail.edges ++ [s(ℓ, s)] ++
        Λ.edges ++ chain.edges ++ [s(t, a)] ++ deleted) := by
    apply he.trans
    apply List.perm_iff_count.mpr
    intro e
    have hp := hPe.count_eq e
    simp only [List.count_append, List.count_cons, List.count_nil] at hp ⊢
    omega
  refine ⟨chain, hinterior, ?_⟩
  exact actual_joint_partition_of_cycle_inventory c hc rest d tail hₐ h_b hd
    Λ q₀ q₁ q₂ hQs hQe chain hchain hseam deleted hsparent heparent

#print axioms actual_closed_parent_joint_partition

end D5.S3.Combinatorics.Graph.Walks.ActualClosedParentJointUpdate

/- GID: D5/S3/Combinatorics/Graph/Walks/AmoebaConfinement
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AmoebaConfinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Copy]
   utility: none
   digest: Ordinary amoeba extensions and minimum total-edge growth in finite trees. -/

/-
   HasExtension: proof_shape: content; escape_witness: the explicit injective
   extensionGraph witness with all arm occurrences and positions simultaneously
   distinct; consumers: dead_of_hasExtension, hasExtension_one.
   MinimumGrowth: proof_shape: content; escape_witness: the universal comparison
   over every finite containing host and total edge count; consumers: Dead,
   dead_of_hasExtension.
   Dead: proof_shape: content; escape_witness: the all-minimizers Coincides
   characterization; consumers: dead_of_hasExtension, total_confinement.
   TotallyConfined: proof_shape: content; escape_witness: the arbitrary-initial-
   host and all-copy confining-host predicate; consumers: total_confinement.
   coincides_of_edge_count: proof_shape: bind-only; escape_witness: bind-only;
   consumed helper: dead_of_hasExtension -> coincides_of_edge_count on its live
   proof path, using upstream tree cardinality and injectivity facts.
   dead_of_hasExtension: proof_shape: bind-only; escape_witness: bind-only;
   consumed helper: total_confinement -> dead_of_hasExtension on its live
   proof path (AmoebaHost), instantiating MinimumGrowth at the current host.
   exists_safe_degree: proof_shape: bind-only; escape_witness: bind-only;
   consumed helper: exists_buffered_host -> exists_safe_degree on its live
   proof path (AmoebaHost).
   admission_basis: open-problem-resolution (#23364; Proved)
   Direct frozen dependencies: none (pinned Mathlib and same-delivery modules).
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement

open SimpleGraph
open scoped BigOperators

noncomputable section
open Classical

/-- A finite simple undirected tree, with its actual finite vertex type. -/
structure Host where
  Vertex : Type
  fintype : Fintype Vertex
  graph : SimpleGraph Vertex
  tree : graph.IsTree

attribute [instance] Host.fintype

/-- New vertices are indexed by root, root occurrence, and distance minus one. -/
abbrev ExtensionVertex {V : Type} (m : V → ℕ) (l : ℕ) :=
  V ⊕ (Σ v : V, Fin (m v) × Fin l)

/-- The ordinary extension has exactly `m v` arms of `l` edges at each `v`. -/
def extensionGraph {V : Type} (H : SimpleGraph V) (m : V → ℕ) (l : ℕ) :
    SimpleGraph (ExtensionVertex m l) where
  Adj x y := match x, y with
    | .inl v, .inl w => H.Adj v w
    | .inl v, .inr a => v = a.1 ∧ a.2.2.val = 0
    | .inr a, .inl v => v = a.1 ∧ a.2.2.val = 0
    | .inr a, .inr b =>
        a.1 = b.1 ∧ a.2.1.val = b.2.1.val ∧
          (a.2.2.val + 1 = b.2.2.val ∨ b.2.2.val + 1 = a.2.2.val)
  symm.symm := by
    intro x y h
    cases x <;> cases y
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  loopless.irrefl := by
    intro x
    cases x with
    | inl v => exact H.irrefl
    | inr a => simp only [and_self, not_and, not_or]; omega

/-- An extension of this particular copy, with all arms present simultaneously. -/
def HasExtension {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    (m : V → ℕ) (l : ℕ) (c : Copy H G) : Prop :=
  ∃ e : Copy (extensionGraph H m l) G, ∀ v, e (.inl v) = c v

/-- Containment coincides with the original host, including adjacency. -/
def Coincides {G S : Host} (i : Copy G.graph S.graph) : Prop :=
  Function.Surjective i ∧ ∀ x y, S.graph.Adj (i x) (i y) → G.graph.Adj x y

/-- A growth minimizes the total edge count among all finite containing trees
realizing the extension of the specified copy. -/
def MinimumGrowth {V : Type} {H : SimpleGraph V} (m : V → ℕ) (l : ℕ)
    {G : Host} (c : Copy H G.graph) {S : Host} (i : Copy G.graph S.graph) : Prop :=
  HasExtension m l (i.comp c) ∧
    ∀ (R : Host) (j : Copy G.graph R.graph), HasExtension m l (j.comp c) →
      Nat.card S.graph.edgeSet ≤ Nat.card R.graph.edgeSet

/-- Deadness quantifies over every minimum growth, with its containing map. -/
def Dead {V : Type} {H : SimpleGraph V} (m : V → ℕ) (l : ℕ)
    {G : Host} (c : Copy H G.graph) : Prop :=
  ∀ (S : Host) (i : Copy G.graph S.graph), MinimumGrowth m l c i → Coincides i

/-- A confining host admits a copy and kills all copies and multiplicity placements. -/
def Confining {V : Type} (H : SimpleGraph V) (m : V → ℕ) (l : ℕ) (S : Host) : Prop :=
  Nonempty (Copy H S.graph) ∧ ∀ c : Copy H S.graph, Dead m l c

/-- Total confinement preserves each arbitrary initial finite tree by a copy. -/
def TotallyConfined {V : Type} (H : SimpleGraph V) (m : V → ℕ) (l : ℕ) : Prop :=
  ∀ (T : Host), Nonempty (Copy H T.graph) →
    ∃ S : Host, Nonempty (Copy T.graph S.graph) ∧ Confining H m l S

/-- The full ordinary-amoeba Conjecture 1, including zero length and multiplicities. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] (H : SimpleGraph V) (_hH : H.IsTree) (m : V → ℕ) (l : ℕ),
    (∑ v, m v) + 2 < H.maxDegree → TotallyConfined H m l

private theorem coincides_of_edge_count {G S : Host} (i : Copy G.graph S.graph)
    (hcard : Nat.card S.graph.edgeSet ≤ Nat.card G.graph.edgeSet) : Coincides i := by
  letI : Fintype G.graph.edgeSet := Fintype.ofFinite _
  letI : Fintype S.graph.edgeSet := Fintype.ofFinite _
  have hG := (isTree_iff_connected_and_card.mp G.tree).2
  have hS := (isTree_iff_connected_and_card.mp S.tree).2
  have hvertices : Fintype.card S.Vertex ≤ Fintype.card G.Vertex := by
    simp only [Nat.card_eq_fintype_card] at hG hS hcard
    omega
  have hsurj : Function.Surjective i := by
    by_contra h
    have := Fintype.card_lt_of_injective_not_surjective i i.injective h
    omega
  have hesurj : Function.Surjective i.mapEdgeSet := by
    by_contra h
    have := Fintype.card_lt_of_injective_not_surjective
      i.mapEdgeSet i.mapEdgeSet.injective h
    simp only [Nat.card_eq_fintype_card] at hcard
    omega
  refine ⟨hsurj, ?_⟩
  intro x y hxy
  obtain ⟨e, he⟩ := hesurj ⟨s(i x, i y), hxy⟩
  have he' : e.val.map i = (s(x, y)).map i := congrArg Subtype.val he
  have heq : e.val = s(x, y) := Sym2.map.injective i.injective he'
  have he_mem : s(x, y) ∈ G.graph.edgeSet := heq ▸ e.property
  exact he_mem

/-- A simultaneous extension already in a finite tree makes every minimum-total-edge
growth coincide with that tree. -/
theorem dead_of_hasExtension {V : Type} {H : SimpleGraph V} (m : V → ℕ) (l : ℕ)
    {G : Host} (c : Copy H G.graph) (h : HasExtension m l c) : Dead m l c := by
  intro S i hi
  apply coincides_of_edge_count i
  apply hi.2 G (Copy.id G.graph)
  exact h

/-- At most the total multiplicity many integer degrees are forbidden. A degree
between two and `k+2` escapes every half-open degree-demand interval. -/
theorem exists_safe_degree {V : Type} [Fintype V] (d m : V → ℕ) :
    ∃ q : ℕ, 2 ≤ q ∧ q ≤ (∑ v, m v) + 2 ∧
      ∀ v, d v ≤ q → d v + m v ≤ q := by
  let bad : Finset ℕ := Finset.univ.biUnion (fun v => Finset.Ico (d v) (d v + m v))
  have hb : bad.card ≤ ∑ v, m v := by
    calc
      bad.card ≤ ∑ v, (Finset.Ico (d v) (d v + m v)).card := Finset.card_biUnion_le
      _ = ∑ v, m v := by simp
  have hc : bad.card < (Finset.Icc 2 ((∑ v, m v) + 2)).card := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨q, hq, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  refine ⟨q, (Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2, ?_⟩
  intro v hv
  by_contra h
  apply hnot
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, Finset.mem_Ico.mpr ⟨hv, by omega⟩⟩

end
end D5.S3.Combinatorics.Graph.Walks.AmoebaConfinement

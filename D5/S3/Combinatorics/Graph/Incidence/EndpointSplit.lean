/- GID: D5/S3/Combinatorics/Graph/Incidence/EndpointSplit
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Incidence/EndpointSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint partitions split a simple graph into tagged blocks. -/

import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Incidence.EndpointSplit

open SimpleGraph
open scoped Sym2 BigOperators

section

variable {V : Type*} {F : SimpleGraph V}

/-- The original edges incident to a given endpoint. -/
abbrev Incident (F : SimpleGraph V) (v : V) := {e : F.edgeSet // v ∈ e.val}

/-- An equivalence relation on the incident edges at each endpoint encodes a partition
into its nonempty equivalence classes. -/
def EndpointPartition (F : SimpleGraph V) := (v : V) → Setoid (Incident F v)

namespace EndpointPartition

variable (P : EndpointPartition F)

/-- Blocks at the same endpoint are the classes of its partition. -/
abbrev BlockAt (v : V) := Quotient (P v)

/-- A block retains its original endpoint as a tag. -/
abbrev Block := Σ v : V, P.BlockAt v

/-- The block of an original edge at one of its endpoints. -/
def blockOf (v : V) (e : Incident F v) : P.Block :=
  ⟨v, Quotient.mk (P v) e⟩

/-- The incident labels contained in a tagged block. -/
abbrev Members (b : P.Block) := {e : Incident F b.1 // Quotient.mk (P b.1) e = b.2}

theorem members_nonempty (b : P.Block) : Nonempty (P.Members b) := by
  rcases b with ⟨v, c⟩
  obtain ⟨e, rfl⟩ := Quotient.exists_rep c
  exact ⟨⟨e, rfl⟩⟩

/-- Send an original edge to the unordered pair of its two tagged blocks. -/
def splitPair (e : F.edgeSet) : Sym2 P.Block :=
  e.val.pmap (fun v hv => P.blockOf v ⟨e, hv⟩) (fun _ hv => hv)

theorem mem_splitPair_iff (b : P.Block) (e : F.edgeSet) :
    b ∈ P.splitPair e ↔ ∃ h : b.1 ∈ e.val, Quotient.mk (P b.1) ⟨e, h⟩ = b.2 := by
  rw [splitPair, Sym2.mem_pmap_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, rfl⟩
  · rcases b with ⟨v, c⟩
    rintro ⟨h, hc⟩
    exact ⟨v, h, congrArg (Sigma.mk v) hc.symm⟩

private theorem splitPair_map_root (e : F.edgeSet) :
    (P.splitPair e).map Sigma.fst = e.val := by
  rcases e with ⟨⟨u, v⟩, h⟩
  rfl

private theorem splitPair_injective : Function.Injective P.splitPair := by
  intro e f h
  apply Subtype.ext
  simpa only [P.splitPair_map_root] using congrArg (Sym2.map Sigma.fst) h

private theorem splitPair_not_isDiag (e : F.edgeSet) : ¬ (P.splitPair e).IsDiag := by
  rcases e with ⟨⟨u, v⟩, h⟩
  change F.Adj u v at h
  intro hd
  exact h.ne (congrArg Sigma.fst (Sym2.mk_isDiag_iff.mp hd))

/-- The finite simple graph obtained by joining the endpoint blocks of every edge. -/
def splitGraph : SimpleGraph P.Block :=
  SimpleGraph.fromEdgeSet (Set.range P.splitPair)

private theorem splitGraph_edgeSet : P.splitGraph.edgeSet = Set.range P.splitPair := by
  rw [splitGraph, SimpleGraph.edgeSet_fromEdgeSet]
  ext p
  simp only [Set.mem_sdiff, Set.mem_range, Sym2.mem_diagSet]
  exact ⟨And.left, fun ⟨e, he⟩ => ⟨⟨e, he⟩, he ▸ P.splitPair_not_isDiag e⟩⟩

/-- In a simple input graph every original edge gives a distinct edge of the split graph. -/
noncomputable def edgeEquiv : F.edgeSet ≃ P.splitGraph.edgeSet :=
  Equiv.ofBijective (fun e => ⟨P.splitPair e, P.splitGraph_edgeSet.symm ▸ ⟨e, rfl⟩⟩)
    ⟨fun _ _ h => P.splitPair_injective (congrArg Subtype.val h), fun e => by
      have he : e.val ∈ Set.range P.splitPair := by
        rw [← P.splitGraph_edgeSet]
        exact e.property
      obtain ⟨f, hf⟩ := he
      exact ⟨f, Subtype.ext hf⟩⟩

theorem card_edgeSet : Nat.card P.splitGraph.edgeSet = Nat.card F.edgeSet :=
  Nat.card_congr P.edgeEquiv.symm

instance [Finite V] : Finite P.Block := by
  classical
  let := Fintype.ofFinite V
  let (v : V) := Fintype.ofFinite (Quotient (P v))
  exact Finite.of_fintype _

private theorem not_isEmpty_block_of_edge (e : F.edgeSet) : Nonempty P.Block := by
  rcases e with ⟨⟨u, v⟩, he⟩
  exact ⟨P.blockOf u ⟨⟨s(u, v), he⟩, Sym2.mem_mk_left u v⟩⟩

private theorem blockOf_eq_iff (b : P.Block) {e : F.edgeSet} (h : b.1 ∈ e.val) :
    P.blockOf b.1 (⟨e, h⟩ : Incident F b.1) = b ↔
      Quotient.mk (P b.1) ⟨e, h⟩ = b.2 := by
  rcases b with ⟨v, c⟩
  simp [blockOf]

private theorem splitGraph_adj_iff {b c : P.Block} :
    P.splitGraph.Adj b c ↔ ∃ e : F.edgeSet, P.splitPair e = s(b, c) := by
  change s(b, c) ∈ P.splitGraph.edgeSet ↔ _
  rw [P.splitGraph_edgeSet]
  rfl

private theorem split_reachable_of_mem {b c : P.Block} {e : F.edgeSet}
    (hb : b ∈ P.splitPair e) (hc : c ∈ P.splitPair e) :
    P.splitGraph.Reachable b c := by
  by_cases h : b = c
  · exact h ▸ Reachable.rfl
  · exact ((P.splitGraph_adj_iff).mpr ⟨e, (Sym2.mem_and_mem_iff h).mp ⟨hb, hc⟩⟩).reachable

/-- A block member labels its incident split edge, or equivalently its split neighbor. -/
noncomputable def membersEquivNeighbor (b : P.Block) :
    P.Members b ≃ P.splitGraph.neighborSet b := by
  let f (e : P.Members b) : P.splitGraph.neighborSet b :=
    let hb := (P.mem_splitPair_iff b e.val.val).mpr ⟨e.val.property, e.property⟩
    ⟨Sym2.Mem.other hb, P.splitGraph_adj_iff.mpr ⟨e.val.val, (Sym2.other_spec hb).symm⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e e' h
    apply Subtype.ext
    apply Subtype.ext
    apply P.splitPair_injective
    have pair (a : P.Members b) : s(b, (f a).val) = P.splitPair a.val.val :=
      Sym2.other_spec _
    exact (pair e).symm.trans ((congrArg (fun c : P.splitGraph.neighborSet b => s(b, c.val)) h).trans (pair e'))
  · intro c
    obtain ⟨e, he⟩ := P.splitGraph_adj_iff.mp c.property
    have hb : b ∈ P.splitPair e := he.symm ▸ Sym2.mem_mk_left b c.val
    obtain ⟨hm, hc⟩ := (P.mem_splitPair_iff _ _).mp hb
    refine ⟨⟨⟨e, hm⟩, hc⟩, Subtype.ext ?_⟩
    change Sym2.Mem.other hb = c.val
    exact Sym2.congr_right.mp ((Sym2.other_spec hb).trans he)

theorem splitGraph_connected_of_steps {H : SimpleGraph F.edgeSet} (hH : H.Connected)
    (hstep : ∀ ⦃e f⦄, H.Adj e f → ∃ b : P.Block, b ∈ P.splitPair e ∧ b ∈ P.splitPair f) :
    P.splitGraph.Connected := by
  have hn := P.not_isEmpty_block_of_edge (Classical.choice hH.nonempty)
  refine (connected_iff _).mpr ⟨fun b c => ?_, hn⟩
  obtain ⟨e⟩ := P.members_nonempty b
  obtain ⟨f⟩ := P.members_nonempty c
  have hb := (P.mem_splitPair_iff b e.val.val).mpr ⟨e.val.property, e.property⟩
  have hc := (P.mem_splitPair_iff c f.val.val).mpr ⟨f.val.property, f.property⟩
  obtain ⟨p⟩ := hH.preconnected e.val.val f.val.val
  have lift {a z : F.edgeSet} (w : H.Walk a z) :
      ∀ {x y}, x ∈ P.splitPair a → y ∈ P.splitPair z → P.splitGraph.Reachable x y := by
    induction w with
    | nil => exact P.split_reachable_of_mem
    | cons h _ ih =>
      obtain ⟨d, hd, hd'⟩ := hstep h
      exact fun hx hy => (P.split_reachable_of_mem hx hd).trans (ih hd' hy)
  exact lift p hb hc

/-- Reachability inside each block transfers connectivity back to the original edge labels. -/
theorem connected_of_splitGraph_connected {H : SimpleGraph F.edgeSet}
    (hP : P.splitGraph.Connected)
    (hlocal : ∀ b : P.Block, ∀ ⦃e f : F.edgeSet⦄,
      b ∈ P.splitPair e → b ∈ P.splitPair f → H.Reachable e f) :
    H.Connected := by
  obtain ⟨b⟩ := hP.nonempty
  obtain ⟨a⟩ := P.members_nonempty b
  refine (connected_iff _).mpr ⟨?_, ⟨a.val.val⟩⟩
  have lift {b c : P.Block} (w : P.splitGraph.Walk b c) :
      ∀ ⦃e f : F.edgeSet⦄, b ∈ P.splitPair e → c ∈ P.splitPair f → H.Reachable e f := by
    induction w with
    | nil => exact hlocal _
    | cons h _ ih =>
      obtain ⟨g, hg⟩ := P.splitGraph_adj_iff.mp h
      have hu := hg.symm ▸ Sym2.mem_mk_left _ _
      have hv := hg.symm ▸ Sym2.mem_mk_right _ _
      exact fun {_ _} he hf => (hlocal _ he hu).trans (ih hv hf)
  intro e f
  have member (g : F.edgeSet) : ∃ b : P.Block, b ∈ P.splitPair g := by
    rcases g with ⟨⟨u, v⟩, h⟩
    let a : Incident F u := ⟨⟨s(u, v), h⟩, Sym2.mem_mk_left u v⟩
    exact ⟨P.blockOf u a, (P.mem_splitPair_iff _ _).mpr ⟨a.property, rfl⟩⟩
  obtain ⟨b, hb⟩ := member e
  obtain ⟨c, hc⟩ := member f
  obtain ⟨p⟩ := hP.preconnected b c
  exact lift p hb hc

end EndpointPartition

variable (P : EndpointPartition F)

/-- A member of a tagged block is the same data as an original edge with one marked endpoint. -/
private def membersEquivIncidence :
    (Σ b : P.Block, P.Members b) ≃ (Σ e : F.edgeSet, {v : V // v ∈ e.val}) where
  toFun p := ⟨p.2.val.val, ⟨p.1.1, p.2.val.property⟩⟩
  invFun p :=
    let e : Incident F p.2.val := ⟨p.1, p.2.property⟩
    ⟨P.blockOf p.2.val e, ⟨e, rfl⟩⟩
  left_inv := by
    intro p
    have hp : P.blockOf p.1.1 p.2.val = p.1 :=
      (P.blockOf_eq_iff p.1 p.2.val.property).mpr p.2.property
    apply Sigma.ext hp
    have het (b c : P.Block) (h : b = c) (x : P.Members b) (y : P.Members c)
        (he : x.val.val = y.val.val) : HEq x y := by
      subst c
      exact heq_of_eq (Subtype.ext (Subtype.ext he))
    exact het _ _ hp _ _ rfl
  right_inv := by rintro ⟨_, _⟩; rfl

private theorem card_edge_endpoints [Finite V] (e : F.edgeSet) :
    Nat.card {v : V // v ∈ e.val} = 2 := by
  classical
  let := Fintype.ofFinite V
  let s : Set V := e.val
  change Nat.card s = 2
  have he : ¬ e.val.IsDiag := F.not_isDiag_of_mem_edgeSet e.property
  have hs : s.toFinset = e.val.toFinset := by
    ext v
    simp [s, Sym2.mem_toFinset]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', hs, Sym2.card_toFinset_of_not_isDiag _ he]

theorem card_total_members [Finite V] :
    Nat.card (Σ b : P.Block, P.Members b) = 2 * Nat.card F.edgeSet := by
  classical
  let := Fintype.ofFinite F.edgeSet
  rw [Nat.card_congr (membersEquivIncidence P), Nat.card_sigma]
  simp [card_edge_endpoints, Nat.card_eq_fintype_card, Nat.mul_comm]

end

end D5.S3.Combinatorics.Graph.Incidence.EndpointSplit

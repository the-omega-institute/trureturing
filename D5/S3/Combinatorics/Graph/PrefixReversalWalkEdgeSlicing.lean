/- GID: D5/S3/Combinatorics/Graph/PrefixReversalWalkEdgeSlicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversalWalkEdgeSlicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph]
   utility: none
   digest: Cutting actual paths and Hamilton cycles preserves full supports, uncut edges, and piece counts. -/
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversalWalkEdgeSlicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- A path piece retains its actual graph and both actual endpoints. -/
structure Piece (G : SimpleGraph V) where
  start : V
  finish : V
  walk : G.Walk start finish

/-- The first piece keeps the starting endpoint in its type. -/
private structure Slicing (G : SimpleGraph V) (start : V) where
  finish : V
  first : G.Walk start finish
  later : List (Piece G)

private def Slicing.pieces {start : V} (s : Slicing G start) : List (Piece G) :=
  ⟨start, s.finish, s.first⟩ :: s.later

/-- Split when the actual next edge is selected. Adjacent selected edges
    intentionally create an actual nil walk, preserving its lone vertex. -/
private def cutWalk (E : Finset (Sym2 V)) :
    {start finish : V} → G.Walk start finish → Slicing G start
  | _, _, .nil' start => ⟨start, .nil, []⟩
  | _, _, .cons' start next _ h p =>
      let parts := cutWalk E p
      if s(start, next) ∈ E then
        ⟨start, .nil, ⟨next, parts.finish, parts.first⟩ :: parts.later⟩
      else
        ⟨parts.finish, parts.first.cons h, parts.later⟩

private theorem cutWalk_support (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) :
    ((cutWalk E p).pieces.flatMap fun z => z.walk.support) = p.support := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    by_cases he : s(a, b) ∈ E
    · rw [cutWalk, if_pos he]
      simpa [Slicing.pieces, List.cons_append] using congrArg (a :: ·) ih
    · rw [cutWalk, if_neg he]
      simpa [Slicing.pieces, List.cons_append] using congrArg (a :: ·) ih

private theorem cutWalk_edges (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) :
    ((cutWalk E p).pieces.flatMap fun z => z.walk.edges) =
      p.edges.filter (fun e => decide (e ∉ E)) := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    by_cases he : s(a, b) ∈ E
    · rw [cutWalk, if_pos he]
      simpa [he, Slicing.pieces] using ih
    · rw [cutWalk, if_neg he]
      simpa [he, Slicing.pieces, List.cons_append] using
        congrArg (s(a, b) :: ·) ih

private theorem cutWalk_length (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) :
    (cutWalk E p).pieces.length =
      (p.edges.filter (fun e => decide (e ∈ E))).length + 1 := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    by_cases he : s(a, b) ∈ E
    · simp [cutWalk, he, Slicing.pieces] at ih ⊢
      omega
    · simpa [cutWalk, he, Slicing.pieces] using ih

private theorem cutWalk_paths (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) (hp : p.IsPath) :
    (cutWalk E p).first.IsPath ∧
      ∀ z ∈ (cutWalk E p).later, z.walk.IsPath := by
  revert hp
  induction p with
  | nil =>
    intro _
    exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [cutWalk]⟩
  | @cons a b c h p ih =>
    intro hp
    obtain ⟨hp', ha⟩ := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
    obtain ⟨hfirst, hlater⟩ := ih hp'
    by_cases he : s(a, b) ∈ E
    · rw [cutWalk, if_pos he]
      refine ⟨SimpleGraph.Walk.IsPath.nil, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hfirst
      · exact hlater z hz
    · rw [cutWalk, if_neg he]
      refine ⟨hfirst.cons ?_, hlater⟩
      intro hamem
      apply ha
      rw [← cutWalk_support E p]
      simp only [Slicing.pieces, List.flatMap_cons, List.mem_append]
      exact Or.inl hamem

/-- All selected edges are genuinely deleted, all vertices occur in the
    literal original order, and the actual pieces are paths. -/
theorem exists_path_edge_slicing (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) (hp : p.IsPath) :
    ∃ pieces : List (Piece G),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      pieces.flatMap (fun z => z.walk.support) = p.support ∧
      pieces.flatMap (fun z => z.walk.edges) =
        p.edges.filter (fun e => decide (e ∉ E)) ∧
      pieces.length = (p.edges.filter (fun e => decide (e ∈ E))).length + 1 := by
  refine ⟨(cutWalk E p).pieces, ?_, cutWalk_support E p,
    cutWalk_edges E p, cutWalk_length E p⟩
  obtain ⟨hfirst, hlater⟩ := cutWalk_paths E p hp
  intro z hz
  simp only [Slicing.pieces, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact hfirst
  · exact hlater z hz

private theorem exists_open_cycle_at_edge [Fintype V] {a x y : V}
    (p : G.Walk a a) (hp : p.IsHamiltonianCycle) (he : s(x, y) ∈ p.edgeSet) :
    ∃ q : G.Walk y x, q.IsHamiltonian ∧
      ∀ e, e ∈ q.edges ↔ e ∈ p.edges ∧ e ≠ s(x, y) := by
  let r := p.rotate x (hp.mem_support x)
  have hr : r.IsHamiltonianCycle := hp.rotate (hp.mem_support x)
  have hrEdge : r.edgeSet = p.edgeSet := by
    rw [← SimpleGraph.Walk.edgeSet_toSubgraph, SimpleGraph.Walk.toSubgraph_rotate,
      SimpleGraph.Walk.edgeSet_toSubgraph]
  have hxy : r.toSubgraph.Adj x y := by
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    change s(x, y) ∈ r.edgeSet
    rw [hrEdge]
    exact he
  have hneighbors : y = r.snd ∨ y = r.penultimate := by
    have hm : y ∈ r.toSubgraph.neighborSet x := hxy
    rw [hr.isCycle.neighborSet_toSubgraph_endpoint] at hm
    exact hm
  have hex : ∃ t : G.Walk x x,
      t.IsHamiltonianCycle ∧ t.snd = y ∧ t.edgeSet = p.edgeSet := by
    rcases hneighbors with hs | hs
    · exact ⟨r, hr, hs.symm, hrEdge⟩
    · refine ⟨r.reverse, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
        exact ⟨hr.isCycle.reverse, by simpa using hr.length_eq⟩
      · rw [SimpleGraph.Walk.snd_reverse, hs]
      · rw [SimpleGraph.Walk.edgeSet_reverse, hrEdge]
  obtain ⟨t, ht, hsnd, htEdge⟩ := hex
  cases t with
  | nil => exact (ht.ne_nil rfl).elim
  | @cons _ z _ h q =>
    have hz : z = y := by simpa using hsnd
    subst z
    have hq : q.IsHamiltonian := by
      simpa [SimpleGraph.Walk.IsHamiltonian] using ht.isHamiltonian_tail
    have hcut : s(x, y) ∉ q.edges :=
      ((SimpleGraph.Walk.cons_isCycle_iff q h).mp ht.isCycle).2
    refine ⟨q, hq, ?_⟩
    intro e
    have hmem : (e = s(x, y) ∨ e ∈ q.edges) ↔ e ∈ p.edges := by
      simpa only [SimpleGraph.Walk.mem_edgeSet, SimpleGraph.Walk.edges_cons,
        List.mem_cons] using Set.ext_iff.mp htEdge e
    constructor
    · intro heq
      refine ⟨hmem.mp (Or.inr heq), ?_⟩
      intro hee
      exact hcut (hee ▸ heq)
    · rintro ⟨hep, hne⟩
      exact (hmem.mpr hep).resolve_left hne

/-- Removing a nonempty set of genuine cycle edges produces exactly as
    many actual paths as cuts. Their full supports partition every vertex
    exactly once; their edges are exactly the uncut actual cycle edges.
    The chosen first cut is obtained from E, then the genuine cycle is
    rotated and, when needed, reversed to open precisely that edge. -/
theorem exists_cycle_edge_slicing [Fintype V] (E : Finset (Sym2 V)) {a : V}
    (p : G.Walk a a) (hp : p.IsHamiltonianCycle) (hE : E.Nonempty)
    (hcuts : ∀ e ∈ E, e ∈ p.edgeSet) :
    ∃ pieces : List (Piece G),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔
        e ∈ p.edgeSet ∧ e ∉ E) ∧
      pieces.length = E.card := by
  classical
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e₀
  obtain ⟨q, hq, hqEdges⟩ := exists_open_cycle_at_edge p hp (hcuts _ he₀)
  obtain ⟨pieces, hpaths, hsupport, hedges, hlength⟩ :=
    exists_path_edge_slicing E q hq.isPath
  have hselected :
      (q.edges.filter (fun e => decide (e ∈ E))).toFinset = E.erase s(x, y) := by
    ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_erase]
    constructor
    · rintro ⟨hqmem, hEmem⟩
      exact ⟨(hqEdges e).mp hqmem |>.2, hEmem⟩
    · rintro ⟨hne, hEmem⟩
      exact ⟨(hqEdges e).mpr ⟨hcuts e hEmem, hne⟩, hEmem⟩
  have hselectedNodup := hq.isPath.isTrail.edges_nodup.filter (fun e => decide (e ∈ E))
  have hcount : (q.edges.filter (fun e => decide (e ∈ E))).length + 1 = E.card := by
    rw [← List.toFinset_card_of_nodup hselectedNodup, hselected]
    exact Finset.card_erase_add_one he₀
  refine ⟨pieces, hpaths, ?_, ?_, hlength.trans hcount⟩
  · intro v
    rw [hsupport]
    exact hq v
  · intro e
    rw [hedges]
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨heq, hnot⟩
      exact ⟨(hqEdges e).mp heq |>.1, hnot⟩
    · rintro ⟨hep, hnot⟩
      refine ⟨(hqEdges e).mpr ⟨hep, ?_⟩, hnot⟩
      intro hee
      exact hnot (hee.symm ▸ he₀)

#print axioms exists_path_edge_slicing
#print axioms exists_cycle_edge_slicing

end D5.S3.Combinatorics.Graph.PrefixReversalWalkEdgeSlicing

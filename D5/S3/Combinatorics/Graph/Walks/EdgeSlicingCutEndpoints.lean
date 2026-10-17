/- GID: D5/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hamiltonian]
   utility: none
   digest: Actual Hamilton cycle slices retain actual cut-edge endpoints. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.EdgeSlicingCutEndpoints

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open private Slicing Slicing.finish Slicing.first Slicing.later Slicing.pieces
  cutWalk cutWalk.eq_1 cutWalk.eq_2 cutWalk_paths
  cutWalk_support cutWalk_edges cutWalk_length
  from D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

private def CutVertex {V : Type u} (E : Finset (Sym2 V)) (v : V) : Prop :=
  ∃ e ∈ E, v ∈ e

private theorem cutWalk_boundaries (E : Finset (Sym2 V)) {start finish : V}
    (p : G.Walk start finish) :
    (Slicing.finish (cutWalk E p) = finish ∨ CutVertex E (Slicing.finish (cutWalk E p))) ∧
      ∀ z ∈ Slicing.later (cutWalk E p),
        CutVertex E z.start ∧ (z.finish = finish ∨ CutVertex E z.finish) := by
  induction p with
  | nil =>
    refine ⟨Or.inl rfl, ?_⟩
    simp only [cutWalk.eq_1, List.not_mem_nil, false_implies, implies_true]
  | @cons a b c h p ih =>
    by_cases he : s(a, b) ∈ E
    · rw [cutWalk.eq_2, if_pos he]
      refine ⟨Or.inr ⟨s(a, b), he, Sym2.mem_mk_left _ _⟩, ?_⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨⟨s(a, b), he, Sym2.mem_mk_right _ _⟩, ih.1⟩
      · exact ih.2 z hz
    · rw [cutWalk.eq_2, if_neg he]
      exact ih

/-- Every actual sliced path starts and ends at actual cut-edge vertices.
The exact vertex partition and retained-edge inventory are preserved too.
This is the endpoint information needed to identify residual components. -/
theorem exists_cycle_edge_slicing_with_cut_endpoints [Fintype V]
    (E : Finset (Sym2 V)) {a : V} (p : G.Walk a a) (hp : p.IsHamiltonianCycle)
    (hE : E.Nonempty) (hcuts : ∀ e ∈ E, e ∈ p.edgeSet) :
    ∃ pieces : List (Piece G),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (∀ v, (pieces.flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔
        e ∈ p.edgeSet ∧ e ∉ E) ∧
      pieces.length = E.card ∧
      ∀ z ∈ pieces,
        (∃ e ∈ E, z.start ∈ e) ∧ (∃ e ∈ E, z.finish ∈ e) := by
  classical
  obtain ⟨e₀, he₀⟩ := hE
  obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e₀
  obtain ⟨q, hq, hqEdges⟩ := exists_open_cycle_at_edge p hp (hcuts _ he₀)
  let pieces := Slicing.pieces (cutWalk E q)
  have hpaths : ∀ z ∈ pieces, z.walk.IsPath := by
    obtain ⟨hfirst, hlater⟩ := cutWalk_paths E q hq.isPath
    intro z hz
    simp only [pieces, Slicing.pieces, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hfirst
    · exact hlater z hz
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
  refine ⟨pieces, hpaths, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [show (pieces.flatMap fun z => z.walk.support) = q.support from cutWalk_support E q]
    exact hq v
  · intro e
    rw [show (pieces.flatMap fun z => z.walk.edges) = _ from cutWalk_edges E q]
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨heq, hnot⟩
      exact ⟨(hqEdges e).mp heq |>.1, hnot⟩
    · rintro ⟨hep, hnot⟩
      refine ⟨(hqEdges e).mpr ⟨hep, ?_⟩, hnot⟩
      intro hee
      exact hnot (hee.symm ▸ he₀)
  · exact (cutWalk_length E q).trans hcount
  · have hb := cutWalk_boundaries E q
    have hx : CutVertex E x := ⟨s(x, y), he₀, Sym2.mem_mk_left _ _⟩
    have hy : CutVertex E y := ⟨s(x, y), he₀, Sym2.mem_mk_right _ _⟩
    have hfinish (v : V) (hv : v = x ∨ CutVertex E v) : CutVertex E v := by
      rcases hv with rfl | hv
      · exact hx
      · exact hv
    intro z hz
    simp only [pieces, Slicing.pieces, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨hy, hfinish _ hb.1⟩
    · exact ⟨(hb.2 z hz).1, hfinish _ (hb.2 z hz).2⟩

#print axioms exists_cycle_edge_slicing_with_cut_endpoints

end D5.S3.Combinatorics.Graph.Walks.EdgeSlicingCutEndpoints

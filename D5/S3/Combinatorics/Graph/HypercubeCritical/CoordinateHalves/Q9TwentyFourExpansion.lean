/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyFourExpansion
   generality: G
   mirror-B: none(waiver:covered-by-q9-twenty-four-half-embedding-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Expand compressed walks through subdivision vertices and recover the girth constraint. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression

/-! Expand an edge of the compressed graph back to its one- or two-edge
walk in the induced coordinate half. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion

open Finset SimpleGraph
open private suppress from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open GirthSliceCounting (degreeThree)

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {L R : Finset V}

private abbrev High (G : SimpleGraph V) (L R : Finset V) := SideHigh G L ⊕ SideHigh G R

private def vertex : High G L R → V := Sum.elim Subtype.val Subtype.val

private def side : High G L R → Bool := Sum.elim (fun _ => false) (fun _ => true)

private theorem vertex_degree (x : High G L R) : G.degree (vertex x) = 3 := by
  cases x with
  | inl x => exact (mem_filter.mp x.property).2
  | inr x => exact (mem_filter.mp x.property).2

private theorem vertex_injective (hdisjoint : Disjoint L R) :
    Function.Injective (vertex : High G L R → V) := by
  rintro (x | x) (y | y) he
  · exact congrArg Sum.inl (Subtype.ext he)
  · change x.val = y.val at he
    exact (Finset.disjoint_left.mp hdisjoint (mem_filter.mp x.property).1
      (he.symm ▸ (mem_filter.mp y.property).1)).elim
  · change x.val = y.val at he
    exact (Finset.disjoint_left.mp hdisjoint (mem_filter.mp y.property).1
      (he ▸ (mem_filter.mp x.property).1)).elim
  · exact congrArg Sum.inr (Subtype.ext he)

private def expandEdge {x y : High G L R} (h : (suppress G L R).Adj x y) :
    G.Walk (vertex x) (vertex y) :=
  match x, y, h with
  | .inl _, .inl _, h => .cons h.2.choose_spec.2.1 (.cons h.2.choose_spec.2.2.symm .nil)
  | .inl x, .inr y, h => (show G.Adj x.val y.val from h).toWalk
  | .inr x, .inl y, h => (show G.Adj x.val y.val from h).toWalk
  | .inr _, .inr _, h => .cons h.2.choose_spec.2.1 (.cons h.2.choose_spec.2.2.symm .nil)

private theorem expandEdge_cases {x y : High G L R} (h : (suppress G L R).Adj x y) :
    (side x ≠ side y ∧ ∃ e : G.Adj (vertex x) (vertex y), expandEdge h = e.toWalk) ∨
      (side x = side y ∧ ∃ m, G.degree m = 2 ∧
        ∃ a : G.Adj (vertex x) m, ∃ b : G.Adj m (vertex y),
          expandEdge h = .cons a (.cons b .nil)) := by
  cases x <;> cases y
  · exact Or.inr ⟨rfl, _, h.2.choose_spec.1, _, _, rfl⟩
  · exact Or.inl ⟨by simp [side], h, rfl⟩
  · exact Or.inl ⟨by simp [side], h, rfl⟩
  · exact Or.inr ⟨rfl, _, h.2.choose_spec.1, _, _, rfl⟩

private def expandWalk {x y : High G L R} :
    (suppress G L R).Walk x y → G.Walk (vertex x) (vertex y)
  | .nil => .nil
  | .cons h rest => (expandEdge h).append (expandWalk rest)

private def directCount {x y : High G L R} (w : (suppress G L R).Walk x y) : Nat :=
  w.darts.countP (fun d => side d.fst != side d.snd)

private theorem length_expandWalk {x y : High G L R} (w : (suppress G L R).Walk x y) :
    (expandWalk w).length + directCount w = 2 * w.length := by
  induction w with
  | nil => rfl
  | @cons x y z h rest ih =>
    rw [expandWalk, Walk.length_append]
    rcases expandEdge_cases h with ⟨hd, ⟨e, he⟩⟩ | ⟨hs, m, hm, a, b, he⟩
    · rw [he, Adj.length_toWalk]
      have hc : directCount (.cons h rest) = 1 + directCount rest := by
        simp [directCount, hd, Nat.add_comm]
      rw [hc, Walk.length_cons]
      omega
    · rw [he]
      have hc : directCount (.cons h rest) = directCount rest := by
        simp [directCount, hs]
      rw [hc, Walk.length_cons, Walk.length_cons, Walk.length_cons]
      simp only [Walk.length_nil]
      omega

private theorem neighbor_pair {m a b : V} (hm : G.degree m = 2)
    (ha : G.Adj m a) (hb : G.Adj m b) (hne : a ≠ b) :
    G.neighborFinset m = {a, b} := by
  classical
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr ha
    · exact (G.mem_neighborFinset _ _).mpr hb
  · simp [G.card_neighborFinset_eq_degree, hm, hne]

private theorem expanded_edge_list {x y : High G L R} (h : (suppress G L R).Adj x y) :
    (expandEdge h).edges = [s(vertex x, vertex y)] ∨
      ∃ m, G.degree m = 2 ∧ G.Adj m (vertex x) ∧ G.Adj m (vertex y) ∧
        (expandEdge h).edges = [s(vertex x, m), s(m, vertex y)] := by
  rcases expandEdge_cases h with ⟨_, ⟨e, he⟩⟩ | ⟨_, m, hm, a, b, hw⟩
  · exact Or.inl (he ▸ Adj.edges_toWalk e)
  · exact Or.inr ⟨m, hm, a.symm, b, by rw [hw]; rfl⟩

private theorem source_of_middle {x y a b : High G L R} (hinj : Function.Injective
      (vertex : High G L R → V))
    (hxy : x ≠ y) (hab : a ≠ b) {m : V} (hm : G.degree m = 2)
    (hx : G.Adj m (vertex x)) (hy : G.Adj m (vertex y))
    (ha : G.Adj m (vertex a)) (hb : G.Adj m (vertex b)) : s(x, y) = s(a, b) := by
  classical
  have hn := neighbor_pair hm hx hy (fun he => hxy (hinj he))
  have A := (G.mem_neighborFinset _ _).mpr ha
  have B := (G.mem_neighborFinset _ _).mpr hb
  rw [hn, mem_insert, mem_singleton] at A B
  rcases A with A | A <;> rcases B with B | B
  · exact (hab (hinj (A.trans B.symm))).elim
  · exact Sym2.eq_iff.mpr (Or.inl ⟨hinj A.symm, hinj B.symm⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨hinj B.symm, hinj A.symm⟩)
  · exact (hab (hinj (A.trans B.symm))).elim

private theorem source_of_common_edge {x y a b : High G L R}
    (hinj : Function.Injective (vertex : High G L R → V))
    (h : (suppress G L R).Adj x y) (h' : (suppress G L R).Adj a b)
    {e : Sym2 V} (he : e ∈ (expandEdge h).edges) (he' : e ∈ (expandEdge h').edges) :
    s(x, y) = s(a, b) := by
  rcases expanded_edge_list h with H | ⟨m, hm, hx, hy, H⟩ <;>
    rcases expanded_edge_list h' with H' | ⟨n, hn, ha, hb, H'⟩
  · rw [H, List.mem_singleton] at he
    rw [H', List.mem_singleton] at he'
    rcases Sym2.eq_iff.mp (he.symm.trans he') with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hinj hx, hinj hy⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hinj hx, hinj hy⟩)
  · rw [H, List.mem_singleton] at he
    rw [H', List.mem_cons, List.mem_singleton, he] at he'
    have hx3 := vertex_degree x
    have hy3 := vertex_degree y
    rcases he' with he' | he' <;>
      rcases Sym2.eq_iff.mp he' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
  · rw [H', List.mem_singleton] at he'
    rw [H, List.mem_cons, List.mem_singleton, he'] at he
    have ha3 := vertex_degree a
    have hb3 := vertex_degree b
    rcases he with he | he <;>
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
  · rw [H, List.mem_cons, List.mem_singleton] at he
    rw [H', List.mem_cons, List.mem_singleton] at he'
    have hx3 := vertex_degree x
    have hy3 := vertex_degree y
    have ha3 := vertex_degree a
    have hb3 := vertex_degree b
    have hmn : m = n := by
      rcases he with he | he <;> rcases he' with he' | he' <;>
        rcases Sym2.eq_iff.mp (he.symm.trans he') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
    subst n
    exact source_of_middle hinj h.ne h'.ne hm hx hy ha hb

private theorem expandEdge_trail {x y : High G L R}
    (hinj : Function.Injective (vertex : High G L R → V))
    (h : (suppress G L R).Adj x y) : (expandEdge h).IsTrail := by
  rw [Walk.isTrail_def]
  rcases expanded_edge_list h with H | ⟨m, hm, hx, hy, H⟩
  · simp [H]
  · rw [H]
    have hx3 := vertex_degree x
    have hy3 := vertex_degree y
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, and_true]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [h1, hm] at hx3
      omega
    · exact h.ne (hinj h1)

private theorem mem_expandWalk {x y : High G L R} (w : (suppress G L R).Walk x y)
    {e : Sym2 V} (he : e ∈ (expandWalk w).edges) :
    ∃ a b, ∃ h : (suppress G L R).Adj a b,
      s(a, b) ∈ w.edges ∧ e ∈ (expandEdge h).edges := by
  induction w with
  | nil => simp [expandWalk] at he
  | @cons a b c h w ih =>
    rw [expandWalk, Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · exact ⟨a, b, h, by simp, he⟩
    · obtain ⟨u, v, hv, hw, he⟩ := ih he
      exact ⟨u, v, hv, List.mem_cons_of_mem _ hw, he⟩

private theorem expandWalk_trail (hdisjoint : Disjoint L R) {x y : High G L R}
    {w : (suppress G L R).Walk x y} (hw : w.IsTrail) : (expandWalk w).IsTrail := by
  have hinj := vertex_injective (G := G) hdisjoint
  induction w with
  | nil => simp [expandWalk]
  | @cons a b c h w ih =>
    obtain ⟨ht, hn⟩ := Walk.isTrail_cons h w |>.mp hw
    rw [expandWalk, Walk.isTrail_def, Walk.edges_append]
    refine (expandEdge_trail hinj h).edges_nodup.append (ih ht).edges_nodup ?_
    intro e he he'
    obtain ⟨u, v, hv, hu, hshare⟩ := mem_expandWalk w he'
    exact hn ((source_of_common_edge hinj h hv he hshare).symm ▸ hu)

/-- An actual cycle in the compressed graph has expanded length at least
the girth of the induced half. -/
private theorem girth_le_expanded_length (hdisjoint : Disjoint L R) {x : High G L R}
    {w : (suppress G L R).Walk x x} (hw : w.IsCycle) :
    G.egirth ≤ (2 * w.length - directCount w : Nat) := by
  have hlen := length_expandWalk w
  have hp : (expandWalk w).IsCircuit := by
    refine ⟨expandWalk_trail hdisjoint ((Walk.isCycle_def w).mp hw).1, ?_⟩
    intro he
    have hn : 0 < (expandWalk w).length := by
      cases w with
      | nil => exact (hw.ne_nil rfl).elim
      | cons h rest =>
        rw [expandWalk, Walk.length_append]
        rcases expandEdge_cases h with ⟨_, e, he'⟩ | ⟨_, _, _, _, _, he'⟩ <;>
          rw [he'] <;> simp
    simp [he] at hn
  have hbound := hp.egirth_le_length
  rwa [show 2 * w.length - directCount w = (expandWalk w).length by omega]

private theorem walk_darts_zip {W : Type*} {J : SimpleGraph W} {a b : W} (w : J.Walk a b) :
    w.darts.map (fun d => (d.fst, d.snd)) = w.support.dropLast.zip w.support.tail := by
  induction w with
  | nil => rfl
  | @cons a b c h p ih =>
    have hp : p.support ≠ [] := p.support_ne_nil
    cases hs : p.support with
    | nil => exact (hp hs).elim
    | cons x xs =>
      have hx : x = b := by simpa [hs] using p.head_support
      subst x
      simp only [Walk.darts_cons, List.map_cons, Walk.support_cons, hs, List.dropLast_cons_cons,
        List.tail_cons, List.zip_cons_cons, List.cons.injEq, true_and]
      simpa only [hs, List.tail_cons] using ih

private theorem chain_of_adjacent_pairs {W : Type*} {J : SimpleGraph W} (xs : List W)
    (h : ∀ p ∈ xs.zip xs.tail, J.Adj p.1 p.2) : xs.IsChain J.Adj := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.isChain_cons_cons]
      exact ⟨h (x, y) (by simp), ih (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

private theorem circuit_of_vertex_list {W : Type*} {J : SimpleGraph W} (a : W) (xs : List W)
    (hn : (a :: xs).Nodup) (hsize : 3 ≤ (a :: xs).length)
    (hadj : ∀ p ∈ (a :: xs).zip (xs ++ [a]), J.Adj p.1 p.2) :
    ∃ w : J.Walk a a, w.IsCycle ∧ w.length = (a :: xs).length ∧
      w.darts.map (fun d => (d.fst, d.snd)) = (a :: xs).zip (xs ++ [a]) := by
  let l := (a :: xs) ++ [a]
  have hne : l ≠ [] := by simp [l]
  have htail : l.tail = xs ++ [a] := rfl
  have hdrop : l.dropLast = a :: xs := List.dropLast_concat
  have hzip : l.zip l.tail = (a :: xs).zip (xs ++ [a]) := by
    have hz (p q : List W) (h : p.length = q.length) :
        (p ++ [a]).zip q = p.zip q := by
      induction p generalizing q with
      | nil => have : q = [] := by simpa using h.symm
               simp [this]
      | cons y ys ih =>
        cases q with
        | nil => simp at h
        | cons z zs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at h
          simp [ih zs h]
    rw [htail]
    apply hz
    simp
  have hc : l.IsChain J.Adj := chain_of_adjacent_pairs l (by
    rw [hzip]
    exact hadj)
  let p := Walk.ofSupport l hne hc
  have hs : l.head hne = a := by simp [l]
  have he : l.getLast hne = a := by simp [l]
  let w : J.Walk a a := p.copy hs he
  have hsupport : w.support = l := by
    exact (Walk.support_copy p hs he).trans (Walk.support_ofSupport hne hc)
  have hlen : w.length = (a :: xs).length := by
    have hl := w.length_support
    rw [hsupport] at hl
    simpa [l] using hl.symm
  have hpos : 0 < w.length := by omega
  have hw : ¬w.Nil := fun h => by
    rw [Walk.length_eq_zero_iff.mpr h] at hpos
    omega
  have hpath : w.dropLast.IsPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_dropLast hw, hsupport, hdrop]
    exact hn
  refine ⟨w, Walk.isCycle_iff_isPath_dropLast_and_le_length.mpr ⟨hpath, by omega⟩, hlen, ?_⟩
  rw [walk_darts_zip, hsupport, hdrop, htail]

#print axioms length_expandWalk
#print axioms girth_le_expanded_length
#print axioms circuit_of_vertex_list

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion

/- GID: D5/S3/Combinatorics/Graph/Brooks/ColoringExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Brooks/ColoringExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Odd-cycle extraction, degree reduction and color-preserving extension tools for Brooks surgery. -/

import D5.S3.Combinatorics.Graph.Brooks.Coloring
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Operations

/-
Copyright (c) 2026 Brian Rabern. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/brooks-suppliers/BrooksLean-LICENSE.txt`.
Authors: Brian Rabern and Opus 5

Source: https://github.com/brianrabern/BrooksLean/tree/1d990050d881327fc79dd51e82ba4449b4e2467d
Units: BrooksLean/OddCycle.lean, BrooksLean/VertexLemmas.lean, BrooksLean/Brooks.lean.
Modified from the retained General source by capacity partition on 2026-10-19.
Module framing, imports and consumed helper visibility are adapted here.
The greedy bound reuses the existing frozen Coloring owner; its redundant
greedy-step and finite-insertion proof helpers are omitted.
The low-degree deletion extension is imported from its existing native owner.
The mathematical argument is Landon Rabern, Yet another proof of Brooks' theorem,
Discrete Mathematics 346 (2023), 113261, DOI 10.1016/j.disc.2022.113261.
Retire each transplanted statement when this repository's pinned Mathlib contains
an equivalent statement, replacing its consumers by direct applications.
-/

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- `G` contains a cycle of odd length. -/
def HasOddCycle (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length

/-- Induction for `hasOddCycle_of_odd_length`, on an upper bound for the length of the walk. -/
private theorem hasOddCycle_aux :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length ≤ n → Odd w.length → G.HasOddCycle := by
  intro n
  induction n with
  | zero =>
    intro u w hlen hodd
    rw [Nat.le_zero.1 hlen] at hodd
    simp at hodd
  | succ k ih =>
    intro u w hlen hodd
    classical
    cases w with
    | nil => simp at hodd
    | @cons _ v _ h p =>
      rw [Walk.length_cons] at hlen hodd
      by_cases hp : p.IsPath
      · by_cases he : s(u, v) ∈ p.edges
        · -- `p` is a path from `v` to `u` using the edge `uv`, so `p` *is* that edge and the closed
          -- walk has length `2`, contradicting oddness.
          exact absurd (hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he) ▸ hodd) (by simp)
        · -- `p` is a path avoiding `uv`, so `cons h p` is already an odd cycle.
          exact ⟨u, Walk.cons h p, (Walk.cons_isCycle_iff p h).2 ⟨hp, he⟩, by
            rwa [Walk.length_cons]⟩
      · -- `p` is not a path, so some vertex `x` occurs twice in `p.support`. Writing
        -- `p = A ++ (cons hb (C ++ D))` where `A : Walk v x`, `C : Walk _ x` and `D : Walk x u`,
        -- the two closed walks `cons hb C : Walk x x` and `cons h (A ++ D) : Walk u u` have lengths
        -- `C.length + 1` and `A.length + D.length + 1`, summing to `w.length`. Both are nonzero, so
        -- both are strictly shorter than `w`, and one of them is odd.
        rw [Walk.isPath_def] at hp
        obtain ⟨x, hdup⟩ := List.exists_duplicate_iff_not_nodup.2 hp
        have hx : x ∈ p.support := hdup.mem
        -- Split `p` at the first occurrence of `x`.
        have hspec := p.take_spec hx
        have hA1 : (p.takeUntil x hx).support.count x = 1 := p.count_support_takeUntil_eq_one hx
        -- `x` occurs again after the split, so the second piece is not `nil`.
        have hBt : 1 ≤ (p.dropUntil x hx).support.tail.count x := by
          have hsupp : p.support
              = (p.takeUntil x hx).support ++ (p.dropUntil x hx).support.tail :=
            (congrArg Walk.support hspec.symm).trans (Walk.support_append _ _)
          have hsplit : p.support.count x
              = (p.takeUntil x hx).support.count x + (p.dropUntil x hx).support.tail.count x := by
            rw [hsupp, List.count_append]
          have := List.duplicate_iff_two_le_count.1 hdup
          lia
        have hBnil : ¬(p.dropUntil x hx).Nil := by
          intro hnil
          rw [Walk.nil_iff_support_eq.1 hnil] at hBt
          simp at hBt
        obtain ⟨y, hb, Bt, hBeq⟩ := Walk.not_nil_iff.1 hBnil
        have hx2 : x ∈ Bt.support := by
          have hsupp : (p.dropUntil x hx).support.tail = Bt.support := by rw [hBeq]; simp
          rw [hsupp] at hBt
          exact List.count_pos_iff.1 (by lia)
        -- Split the second piece again at the next occurrence of `x`.
        have hspec2 := Bt.take_spec hx2
        -- Length bookkeeping: the two loops partition the length of `w`.
        have hlenp : p.length
            = (p.takeUntil x hx).length + (p.dropUntil x hx).length :=
          (congrArg Walk.length hspec.symm).trans (Walk.length_append _ _)
        have hlenB : (p.dropUntil x hx).length = Bt.length + 1 := by rw [hBeq]; simp
        have hlenBt : (Bt.takeUntil x hx2).length + (Bt.dropUntil x hx2).length = Bt.length :=
          ((Walk.length_append _ _).symm.trans (congrArg Walk.length hspec2))
        rcases Nat.even_or_odd (Walk.cons hb (Bt.takeUntil x hx2)).length with hev | hod
        · -- The loop through `x` is even, so the loop through `u` is odd.
          refine ih (Walk.cons h ((p.takeUntil x hx).append (Bt.dropUntil x hx2))) ?_ ?_
          · simp only [Walk.length_cons, Walk.length_append]
            lia
          · simp only [Walk.length_cons, Walk.length_append] at *
            rw [Nat.odd_iff] at hodd ⊢
            rw [Nat.even_iff] at hev
            omega
        · -- The loop through `x` is itself odd.
          refine ih (Walk.cons hb (Bt.takeUntil x hx2)) ?_ hod
          simp only [Walk.length_cons]
          lia

/-- A closed walk of odd length yields a cycle of odd length. -/
private theorem hasOddCycle_of_odd_length {u : V} (w : G.Walk u u) (hodd : Odd w.length) :
    G.HasOddCycle :=
  hasOddCycle_aux _ w le_rfl hodd

/-- **A graph is `2`-colorable iff it contains no odd cycle.** -/
private theorem colorable_two_iff_not_hasOddCycle : G.Colorable 2 ↔ ¬G.HasOddCycle := by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · rintro h ⟨v, c, _, hodd⟩
    exact (Nat.not_odd_iff_even.2 (h v c)) hodd
  · intro h u w
    rw [← Nat.not_odd_iff_even]
    exact fun hodd => h (hasOddCycle_of_odd_length w hodd)


end SimpleGraph
end

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-! ### Greedy coloring from the existing frozen owner -/

variable (G) in
/-- **Greedy coloring bound**: a finite graph is `(G.maxDegree + 1)`-colorable, since when a vertex
is colored it has at most `G.maxDegree` neighbors, so some color is still available for it. -/
theorem colorable_maxDegree_succ [Fintype V] [DecidableRel G.Adj] :
    G.Colorable (G.maxDegree + 1) := by
  classical
  let rank : V → ℕ := fun v => ((Fintype.equivFin V) v : ℕ)
  refine BrooksSubcubic.colorable_of_lower_neighbors_lt G (G.maxDegree + 1) rank ?_ ?_
  · intro a b h
    exact (Fintype.equivFin V).injective (Fin.ext h)
  · intro v
    calc ((G.neighborFinset v).filter fun w => rank w < rank v).card
        ≤ (G.neighborFinset v).card := Finset.card_filter_le _ _
      _ = G.degree v := G.card_neighborFinset_eq_degree v
      _ < G.maxDegree + 1 := Nat.lt_succ_of_le (G.degree_le_maxDegree v)

end SimpleGraph

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

/-! ### Ingredient lemmas -/

/-- STEP 1: the case `Δ(G) ≤ 2`. -/
theorem colorable_maxDegree_of_maxDegree_le_two [Fintype V] [DecidableRel G.Adj]
    (_h2 : G.maxDegree ≤ 2) (hcf : G.CliqueFree (G.maxDegree + 1))
    (hodd : G.maxDegree = 2 → ¬G.HasOddCycle) :
    G.Colorable G.maxDegree := by
  match hΔ : G.maxDegree with
  | 0 =>
    rw [hΔ] at hcf
    refine colorable_zero_iff.2 ?_
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨v⟩ := hne
    exact hcf {v} ⟨by simp [isClique_iff], by simp⟩
  | 1 =>
    rw [hΔ, cliqueFree_two] at hcf
    exact colorable_one_iff.2 hcf
  | 2 =>
    exact colorable_two_iff_not_hasOddCycle.2 (hodd hΔ)
  | k + 3 =>
    lia

/-- STEP 3a: every finite graph has a maximal independent set. -/
theorem exists_maximal_isIndepSet (G : SimpleGraph V) [Finite V] :
    ∃ I : Set V, Maximal G.IsIndepSet I := by
  obtain ⟨s, hs⟩ := G.maximumIndepSet_exists
  exact ⟨↑s, hs.isMaximalIndepSet s⟩

/-- STEP 3b: a maximal independent set is dominating. -/
private theorem Maximal.exists_adj_of_notMem {I : Set V} (hI : Maximal G.IsIndepSet I) {v : V}
    (hv : v ∉ I) : ∃ w ∈ I, G.Adj v w := by
  by_contra hcon
  push Not at hcon
  have hindep : G.IsIndepSet (insert v I) := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact hcon y hy
    · rcases hy with rfl | hy
      · exact fun hadj => hcon x hx hadj.symm
      · exact hI.1 hx hy hxy
  exact hv (hI.2 hindep (Set.subset_insert v I) (Set.mem_insert v I))

/-- STEP 3c: deleting a maximal independent set drops the maximum degree. -/
theorem maxDegree_induce_compl_lt_of_maximal [Fintype V] [DecidableRel G.Adj]
    {I : Set V} [DecidablePred (· ∈ I)] [Nonempty ↥(Iᶜ : Set V)]
    (hI : Maximal G.IsIndepSet I) :
    (G.induce (Iᶜ : Set V)).maxDegree < G.maxDegree := by
  classical
  obtain ⟨⟨v0, hv0⟩⟩ := ‹Nonempty ↥(Iᶜ : Set V)›
  obtain ⟨w0, _, hw0⟩ := Maximal.exists_adj_of_notMem hI (v := v0)
    (Set.notMem_of_mem_compl hv0)
  have hdeg0 : 0 < G.degree v0 := by
    rw [← card_neighborFinset_eq_degree, Finset.card_pos]
    exact ⟨w0, (G.mem_neighborFinset v0 w0).2 hw0⟩
  have hpos : 0 < G.maxDegree := lt_of_lt_of_le hdeg0 (G.degree_le_maxDegree v0)
  refine (maxDegree_le_of_forall_degree_le (G.induce (Iᶜ : Set V)) (G.maxDegree - 1)
    fun v => ?_).trans_lt (Nat.sub_lt hpos Nat.zero_lt_one)
  obtain ⟨w, hwI, hwadj⟩ := Maximal.exists_adj_of_notMem hI (v := ↑v)
    (Set.notMem_of_mem_compl v.property)
  have hsubset :
      ((G.induce (Iᶜ : Set V)).neighborFinset v).map (.subtype (· ∈ (Iᶜ : Set V))) ⊆
        (G.neighborFinset ↑v).erase w := by
    intro x hx
    rcases Finset.mem_map.1 hx with ⟨a, ha, rfl⟩
    have ha' : G.Adj ↑v ↑a := by simpa [mem_neighborFinset, comap_adj] using ha
    have hne : ↑a ≠ w := fun h =>
      Set.notMem_of_mem_compl (h ▸ a.property : w ∈ Iᶜ) hwI
    exact Finset.mem_erase.2 ⟨hne, (G.mem_neighborFinset _ _).2 ha'⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map, card_neighborFinset_eq_degree] at hcard
  have herase :
      ((G.neighborFinset ↑v).erase w).card + 1 = G.degree ↑v := by
    rw [Finset.card_erase_add_one ((G.mem_neighborFinset _ _).2 hwadj),
      card_neighborFinset_eq_degree]
  have := G.degree_le_maxDegree (↑v)
  omega

/-- STEP 4: deleting an independent set costs at most one color. -/
theorem Colorable.of_induce_compl_isIndepSet {I : Set V} (hI : G.IsIndepSet I)
    (h : (G.induce (Iᶜ : Set V)).Colorable n) :
    G.Colorable (n + 1) := by
  obtain ⟨C⟩ := h
  classical
  let color : V → Fin (n + 1) := fun v =>
    if hv : v ∈ I then Fin.last n
    else Fin.castSucc (C ⟨v, Set.mem_compl hv⟩)
  refine ⟨Coloring.mk color fun {x y} hxy => ?_⟩
  dsimp [color]
  by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
  · exact absurd hxy (hI hx hy hxy.ne)
  · simp [hx, hy, Fin.ne_of_gt (Fin.castSucc_lt_last _)]
  · simp [hx, hy, Fin.ne_of_lt (Fin.castSucc_lt_last _)]
  · have hxy' : (G.induce (Iᶜ : Set V)).Adj ⟨x, Set.mem_compl hx⟩ ⟨y, Set.mem_compl hy⟩ := hxy
    simp only [hx, hy, ↓reduceDIte]
    exact Fin.castSucc_inj.ne.mpr (C.valid hxy')

/-- STEP 5: if no vertex has degree below `Δ`, the graph is `Δ`-regular. -/
theorem isRegularOfDegree_maxDegree_of_forall_le [Fintype V] [DecidableRel G.Adj]
    (h : ∀ v, G.maxDegree ≤ G.degree v) :
    G.IsRegularOfDegree G.maxDegree :=
  fun v => le_antisymm (G.degree_le_maxDegree v) (h v)

/-- STEP 6: in a `k`-regular `G` with `1 ≤ k`, a vertex of a `(k-1)`-regular induced subgraph
`Q ⊆ Iᶜ` has exactly one neighbor in `I`. -/
theorem existsUnique_adj_mem_of_isRegular [Fintype V] [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (hG : G.IsRegularOfDegree k) {I Q : Set V} (hI : Maximal G.IsIndepSet I)
    (hQI : Q ⊆ Iᶜ) [DecidablePred (· ∈ Q)] [DecidablePred (· ∈ I)]
    (hQ : (G.induce Q).IsRegularOfDegree (k - 1)) (v : V) (hv : v ∈ Q) :
    ∃! w, w ∈ I ∧ G.Adj v w := by
  classical
  have hdegQ : (G.induce Q).degree ⟨v, hv⟩ = k - 1 := hQ _
  have hinter : (G.neighborFinset v ∩ Q.toFinset).card = k - 1 := by
    have hmap := congrArg Finset.card (G.map_neighborFinset_induce (s := Q) ⟨v, hv⟩)
    simpa [card_neighborFinset_eq_degree, hdegQ] using hmap.symm
  have hsum :
      (G.neighborFinset v ∩ Q.toFinset).card + (G.neighborFinset v \ Q.toFinset).card =
        G.degree v := by
    rw [← card_neighborFinset_eq_degree, add_comm, Finset.card_sdiff_add_card_inter]
  have hout : (G.neighborFinset v \ Q.toFinset).card = 1 := by
    have hdeg := hG v
    omega
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hout
  have hwmem : w ∈ G.neighborFinset v \ Q.toFinset := by simp [hw]
  have hwAdj : G.Adj v w := (G.mem_neighborFinset _ _).1 (Finset.mem_sdiff.1 hwmem).1
  have hwI : w ∈ I := by
    obtain ⟨w', hw'I, hw'Adj⟩ := Maximal.exists_adj_of_notMem hI (v := v)
      (Set.notMem_of_mem_compl (hQI hv))
    have hw'out : w' ∈ G.neighborFinset v \ Q.toFinset := by
      refine Finset.mem_sdiff.2 ⟨(G.mem_neighborFinset _ _).2 hw'Adj, ?_⟩
      simp only [Set.mem_toFinset]
      exact fun hq => absurd hw'I (Set.notMem_of_mem_compl (hQI hq))
    have : w' = w := by rw [hw] at hw'out; simpa using hw'out
    rwa [← this]
  refine ⟨w, ⟨hwI, hwAdj⟩, ?_⟩
  intro w' ⟨hw'I, hw'Adj⟩
  have hw'out : w' ∈ G.neighborFinset v \ Q.toFinset := by
    refine Finset.mem_sdiff.2 ⟨(G.mem_neighborFinset _ _).2 hw'Adj, ?_⟩
    simp only [Set.mem_toFinset]
    exact fun hq => absurd hw'I (Set.notMem_of_mem_compl (hQI hq))
  rw [hw] at hw'out
  simpa using hw'out

/-- STEP 7: on a connected graph, a non-constant labelling has an edge with distinct labels. -/
theorem Connected.exists_adj_ne_of_ne {β : Type*} (hG : G.Connected) (f : V → β) {a b : V}
    (hab : f a ≠ f b) :
    ∃ u v, G.Adj u v ∧ f u ≠ f v := by
  obtain ⟨p⟩ := hG a b
  induction p with
  | nil => exact (hab rfl).elim
  | @cons u v w h q ih =>
    by_cases hf : f u = f v
    · exact ih (hf ▸ hab)
    · exact ⟨u, v, h, hf⟩

theorem exists_isHamiltonian_walk_of_isCycle_snd [DecidableEq V] {y : V} {c : G.Walk y y}
    (hc : c.IsCycle) (hspan : ∀ t, t ∈ c.support) :
    ∃ p : G.Walk y c.snd, p.IsHamiltonian := by
  have hnil : ¬c.Nil := hc.not_nil
  have hadj := c.adj_snd hnil
  have hsupp : c.support = y :: c.tail.support := by
    conv_lhs => rw [← c.cons_tail_eq hnil]
    simp [Walk.support_cons]
  have hc' : (Walk.cons hadj c.tail).IsCycle := by rwa [c.cons_tail_eq hnil]
  obtain ⟨hp, _⟩ := (Walk.cons_isCycle_iff c.tail hadj).1 hc'
  refine ⟨c.tail.reverse, Walk.IsPath.isHamiltonian_of_mem
    ((Walk.isPath_reverse_iff _).2 hp) fun t => ?_⟩
  have ht := hspan t
  rw [hsupp, List.mem_cons] at ht
  simp only [Walk.support_reverse, List.mem_reverse]
  exact ht.elim (fun h => h ▸ c.tail.end_mem_support) id

/-- STEP 9: adding one edge raises the maximum degree by at most one. -/
theorem degree_sup_edge_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u w v : V) :
    (G ⊔ edge u w).degree v ≤ G.degree v + 1 := by
  classical
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_sup]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  have ha' : (edge u w).Adj v a := (mem_neighborFinset _ _ _).1 ha
  have hb' : (edge u w).Adj v b := (mem_neighborFinset _ _ _).1 hb
  simp only [edge_adj] at ha' hb'
  aesop


/-- Same as `of_induce_insert_color`, but returns the colouring and records that old colours on
`s` are preserved and the new vertex gets colour `a`. Assumes `v ∉ s`. -/
private theorem exists_coloring_induce_insert_color [DecidableEq V] {s : Finset V} {v : V} {a : Fin n}
    (hv : v ∉ s)
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (ha : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a) :
    ∃ C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n),
      C' ⟨v, Finset.mem_insert_self v s⟩ = a ∧
        ∀ (u : V) (hu : u ∈ s),
          C' ⟨u, Finset.mem_insert_of_mem hu⟩ = C ⟨u, hu⟩ := by
  classical
  let f : V → Fin n := fun u => if hu : u ∈ s then C ⟨u, hu⟩ else a
  have hf : ∀ (u : V) (hu : u ∈ s), f u = C ⟨u, hu⟩ := fun _ hu => dif_pos hu
  have hfree : ∀ w, G.Adj v w → w ∈ s → f w ≠ a := fun w hw hws hc =>
    ha w hws hw (hf w hws ▸ hc)
  let C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n) :=
    Coloring.mk (fun u => if u.1 = v then a else f u.1) <| by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx hy
      have hadj : G.Adj x y := hxy
      rcases eq_or_ne x v with hxv | hxv
      · rcases eq_or_ne y v with hyv | hyv
        · exact absurd (hxv.trans hyv.symm) hadj.ne
        · rw [if_pos hxv, if_neg hyv]
          exact (hfree y (hxv ▸ hadj) (hy.resolve_left hyv)).symm
      · rcases eq_or_ne y v with hyv | hyv
        · rw [if_neg hxv, if_pos hyv]
          exact hfree x (hyv ▸ hadj.symm) (hx.resolve_left hxv)
        · rw [if_neg hxv, if_neg hyv, hf x (hx.resolve_left hxv), hf y (hy.resolve_left hyv)]
          exact C.valid hadj
  refine ⟨C', ?_, fun u hu => ?_⟩
  · change (if (v : V) = v then a else f v) = a
    simp
  · have hne : u ≠ v := fun h => hv (h ▸ hu)
    change (if (u : V) = v then a else f u) = C ⟨u, hu⟩
    rw [if_neg hne, hf u hu]

/-- Greedy step with a prescribed free colour (needed when two neighbours share a colour). -/
private theorem Colorable.of_induce_insert_color [DecidableEq V] {s : Finset V} {v : V} {a : Fin n}
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (ha : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a) :
    (G.induce (↑(insert v s) : Set V)).Colorable n := by
  classical
  by_cases hv : v ∈ s
  · rw [Finset.insert_eq_of_mem hv]
    exact ⟨C⟩
  · obtain ⟨C', _, _⟩ := exists_coloring_induce_insert_color hv C ha
    exact ⟨C'⟩

/-- Same as `of_induce_insert`, returning the colouring with old colours preserved. Assumes `v ∉ s`. -/
theorem exists_coloring_induce_insert [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s : Finset V} {v : V} [NeZero n]
    (hv : v ∉ s)
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (hlt : (G.neighborFinset v ∩ s).card < n) :
    ∃ C' : (G.induce (↑(insert v s) : Set V)).Coloring (Fin n),
      ∀ (u : V) (hu : u ∈ s),
        C' ⟨u, Finset.mem_insert_of_mem hu⟩ = C ⟨u, hu⟩ := by
  classical
  let f : V → Fin n := fun u => if hu : u ∈ s then C ⟨u, hu⟩ else 0
  obtain ⟨a, ha⟩ : ∃ a, a ∉ (G.neighborFinset v ∩ s).image f := by
    have hcard : ((G.neighborFinset v ∩ s).image f).card < n :=
      lt_of_le_of_lt Finset.card_image_le hlt
    obtain ⟨a, ha⟩ : (((G.neighborFinset v ∩ s).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  have hfree : ∀ (w : V) (hw : w ∈ s), G.Adj v w → C ⟨w, hw⟩ ≠ a := fun w hw hadj hEq => by
    have hf : f w = C ⟨w, hw⟩ := dif_pos hw
    have him : f w ∈ (G.neighborFinset v ∩ s).image f :=
      Finset.mem_image_of_mem f (Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, hw⟩)
    exact ha (by rwa [hf, hEq] at him)
  obtain ⟨C', _, hpres⟩ := exists_coloring_induce_insert_color hv C hfree
  exact ⟨C', hpres⟩

/-- Greedy step when the already-coloured neighbours use fewer than `n` colours. -/
theorem Colorable.of_induce_insert_image [Fintype V] [DecidableRel G.Adj]
    [DecidableEq V] {s : Finset V} {v : V} [NeZero n]
    (C : (G.induce (↑s : Set V)).Coloring (Fin n))
    (hlt : (((G.neighborFinset v ∩ s).image fun w =>
        if hw : w ∈ s then (C ⟨w, hw⟩ : Fin n) else 0) : Finset (Fin n)).card < n) :
    (G.induce (↑(insert v s) : Set V)).Colorable n := by
  classical
  let f : V → Fin n := fun w => if hw : w ∈ s then C ⟨w, hw⟩ else 0
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a ∉ (G.neighborFinset v ∩ s).image f := by
    have hcard : ((G.neighborFinset v ∩ s).image f).card < n := by simpa [f] using hlt
    obtain ⟨a, ha⟩ : (((G.neighborFinset v ∩ s).image f)ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]; lia
    exact ⟨a, Finset.mem_compl.1 ha⟩
  exact Colorable.of_induce_insert_color (C := C) (a := a) fun w hw hadj hEq => by
    have hf : f w = C ⟨w, hw⟩ := dif_pos hw
    have : f w ∈ (G.neighborFinset v ∩ s).image f :=
      Finset.mem_image_of_mem f (Finset.mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 hadj, hw⟩)
    exact ha (by rwa [hf, hEq] at this)

/-- Image of a `K_Δ` copy in `G.induce Iᶜ`. -/
theorem exists_clique_set_of_copy {Δ : ℕ} {I : Set V}
    (ψ : Copy (⊤ : SimpleGraph (Fin Δ)) (G.induce (Iᶜ : Set V))) :
    ∃ Q : Set V, Q ⊆ (Iᶜ : Set V) ∧ Q.ncard = Δ ∧ G.IsClique Q := by
  let ι : Fin Δ → V := fun i => (ψ i : V)
  have hinj : Function.Injective ι := fun _ _ h => ψ.injective (Subtype.ext h)
  refine ⟨Set.range ι, fun _ ⟨i, hi⟩ => hi ▸ (ψ i).property, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  · intro a ha b hb hne
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact ψ.toHom.map_adj ((top_adj i j).2 fun h => hne (congrArg ι h))

/-- From the inductive hypothesis on graphs of size `≤ k`, every such graph is `n`-colorable
when `3 ≤ n`, `Δ ≤ n`, and there is no `K_{n+1}`. -/
theorem colorable_of_card_le_of_maxDegree_le
    {k n : ℕ}
    (ih : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      Fintype.card V ≤ k → G.CliqueFree (G.maxDegree + 1) →
        (G.maxDegree = 2 → ¬G.HasOddCycle) → G.Colorable G.maxDegree)
    {V : Type u} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ k) (hn : 3 ≤ n) (hΔ : G.maxDegree ≤ n)
    (hcf : G.CliqueFree (n + 1)) : G.Colorable n := by
  by_cases hc : G.Colorable G.maxDegree
  · exact Colorable.mono hΔ hc
  · by_cases hcf' : G.CliqueFree (G.maxDegree + 1)
    · by_cases hodd : G.maxDegree = 2 → ¬G.HasOddCycle
      · exact absurd (ih G hcard hcf' hodd) hc
      · -- `Δ = 2` and an odd cycle: greedy gives a 3-colouring.
        exact Colorable.mono (by lia) G.colorable_maxDegree_succ
    · -- Has a `K_{Δ+1}`. If `Δ = n` this contradicts `hcf`; otherwise greedy
      -- gives a `(Δ+1)`-colouring with `Δ+1 ≤ n`.
      by_cases hEq : G.maxDegree = n
      · rw [hEq] at hcf'
        exact absurd hcf hcf'
      · exact Colorable.mono (by lia) G.colorable_maxDegree_succ

/-- The vertex set of a cycle has cardinality equal to its length. -/
theorem Walk.IsCycle.support_toFinset_card [DecidableEq V] {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) : c.support.toFinset.card = c.length := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hne : c.support ≠ [] := c.support_ne_nil
  have hlen : c.support.tail.length = c.length := by
    have hsup := Walk.length_support c
    match hlist : c.support with
    | [] => exact (hne hlist).elim
    | _ :: t =>
      simp only [hlist, List.tail_cons, List.length_cons] at hsup ⊢
      omega
  have heq : c.support.toFinset = c.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      have hx' : x = c.support.head hne ∨ x ∈ c.support.tail :=
        List.mem_cons.1 ((List.cons_head_tail hne).symm ▸ hx)
      rcases hx' with rfl | hx'
      · -- `head = start = end ∈ tail`
        have hhead : c.support.head hne = v := by
          match c with
          | .nil => simp
          | .cons _ _ => simp [Walk.support_cons]
        rw [hhead]
        exact c.end_mem_tail_support hc.not_nil
      · exact hx'
    · exact List.mem_of_mem_tail
  rw [heq, List.toFinset_card_of_nodup hnodup, hlen]


end SimpleGraph

end

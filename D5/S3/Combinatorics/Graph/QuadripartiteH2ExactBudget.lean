/- GID: D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Trails]
   utility: none
   digest: Exact support partitions and pairing budgets for triangular cochains on the four-cube. -/

import D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.InformationTheory.Hamming

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.QuadripartiteH2ExactBudget

open D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
open D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
open SimpleGraph

def cubeGraph : SimpleGraph Cube where
  Adj x y := hamming4 x y = 1
  symm := ⟨by
    have h : ∀ x y : Cube, hamming4 x y = hamming4 y x := by decide
    intro x y hxy
    rw [h]
    exact hxy⟩
  loopless := ⟨by
    intro x
    simp [hamming4]⟩

def oddTerminals (E : Finset (Sym2 Cube)) : Finset Cube :=
  Finset.univ.filter fun x => Odd ((E.filter (fun a => x ∈ a)).card)


structure PathPiece where
  start : Cube
  finish : Cube
  walk : cubeGraph.Walk start finish
  simple : walk.IsPath
  distinct : start ≠ finish

structure CyclePiece where
  base : Cube
  walk : cubeGraph.Walk base base
  simple : walk.IsCycle
  even : Even walk.length

def supportCertificate (E : Finset (Sym2 Cube))
    (ps : List PathPiece) (cs : List CyclePiece) : Prop :=
  ((ps.flatMap fun p => p.walk.edges) ++ (cs.flatMap fun c => c.walk.edges)).Perm E.toList ∧
  (ps.flatMap fun p => [p.start, p.finish]).Perm (oddTerminals E).toList ∧
  (ps.map fun p => p.walk.length).sum + (cs.map fun c => c.walk.length).sum = E.card ∧
  (ps.map fun p => hamming4 p.start p.finish).sum ≤ (ps.map fun p => p.walk.length).sum


def insertOne (i : Fin 4) (t : Bits) : Cube :=
  if i = 0 then (true, t.1, t.2.1, t.2.2) else
  if i = 1 then (t.1, true, t.2.1, t.2.2) else
  if i = 2 then (t.1, t.2.1, true, t.2.2) else
    (t.1, t.2.1, t.2.2, true)

def dualEdge (f : Face) : Sym2 Cube := s(insertZero f.1 f.2, insertOne f.1 f.2)

def supportEdges (F : Cochain) : Finset (Sym2 Cube) :=
  (Finset.univ.filter (fun f => F f ≠ 0)).image dualEdge

def syndrome (F : Cochain) : Finset Cube :=
  Finset.univ.filter (fun b => d2 F b ≠ 0)

def pairCost : Sym2 Cube → ℕ :=
  Sym2.lift ⟨hamming4, by decide⟩

def pairingCost (P : List (Sym2 Cube)) : ℕ := (P.map pairCost).sum

/-- A list of unordered two-element subsets, with each vertex of S occurring exactly once. -/
def IsPairing (S : Finset Cube) (P : List (Sym2 Cube)) : Prop :=
  (∀ a ∈ P, ¬a.IsDiag) ∧
    (P.flatMap fun a => a.toFinset.toList).Perm S.toList

/-- Every dual support has an exact path/cycle partition, and the repair budget is exactly
the cost of an unordered pairing of the tetrahedral defects. -/
theorem fourcube_exact_budget :
    Function.Injective dualEdge ∧
    (∀ f : Face, dualEdge f ∈ cubeGraph.edgeSet) ∧
    (∀ E : Finset (Sym2 Cube), (E : Set (Sym2 Cube)) ⊆ cubeGraph.edgeSet →
      ∃ (ps : List PathPiece) (cs : List CyclePiece), supportCertificate E ps cs) ∧
    (∀ F : Cochain, (supportEdges F).card = weight F ∧
      oddTerminals (supportEdges F) = syndrome F) ∧
    (∀ (F : Cochain) (k : ℕ),
      (∃ e : EdgeCochain, weight (F + d1 e) ≤ k) ↔
      ∃ P : List (Sym2 Cube), IsPairing (syndrome F) P ∧ pairingCost P ≤ k) ∧
    (∀ e : EdgeCochain, 4 ≤ weight (path + d1 e)) := by
  classical
  have decomposition : ∀ E : Finset (Sym2 Cube), (E : Set (Sym2 Cube)) ⊆ cubeGraph.edgeSet →
    ∃ (ps : List PathPiece) (cs : List CyclePiece), supportCertificate E ps cs := by
    classical
    have longest (E : Finset (Sym2 Cube)) (hE : (E : Set (Sym2 Cube)) ⊆ cubeGraph.edgeSet)
      (hne : E.Nonempty) :
      ∃ (u v : Cube) (p : (SimpleGraph.fromEdgeSet (E : Set (Sym2 Cube))).Walk u v),
        p.IsTrail ∧ 0 < p.length ∧
        (∀ (x y : Cube) (q : (SimpleGraph.fromEdgeSet (E : Set (Sym2 Cube))).Walk x y),
          q.IsTrail → q.length ≤ p.length) ∧
        (∀ a ∈ E, u ∈ a → a ∈ p.edges) ∧
        (∀ a ∈ E, v ∈ a → a ∈ p.edges) ∧
        (u ≠ v → u ∈ oddTerminals E ∧ v ∈ oddTerminals E) := by
      classical
      let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 Cube))
      have edges_in {u v : Cube} (p : G.Walk u v) : ∀ a ∈ p.edges, a ∈ E := by
        intro a ha
        have := p.edges_subset_edgeSet ha
        rw [SimpleGraph.edgeSet_fromEdgeSet] at this
        exact this.1
      obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length G
      have maximal {x y : Cube} (q : G.Walk x y) (hq : q.IsTrail) : q.length ≤ p.length :=
        hmax x y q hq
      have positive : 0 < p.length := by
        obtain ⟨a, ha⟩ := hne
        induction a using Sym2.ind with
        | _ x y =>
          have hxy : cubeGraph.Adj x y := hE ha
          have hxyn : x ≠ y := cubeGraph.ne_of_adj hxy
          have hG : G.Adj x y := ⟨ha, hxyn⟩
          have hq : (SimpleGraph.Walk.cons hG .nil).IsTrail := by simp
          have := maximal _ hq
          simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at this
          omega
      have saturated {x y : Cube} (q : G.Walk x y) (hq : q.IsTrail)
          (hm : ∀ {z w : Cube} (r : G.Walk z w), r.IsTrail → r.length ≤ q.length) :
          ∀ a ∈ E, x ∈ a → a ∈ q.edges := by
        intro a ha hx
        induction a using Sym2.ind with
        | _ z w =>
          rcases Sym2.mem_iff.mp hx with rfl | rfl
          · by_contra hed
            have hadj : G.Adj w x := ⟨by simpa [Sym2.eq_swap] using ha,
              (cubeGraph.ne_of_adj (hE ha)).symm⟩
            have hq' : (q.cons hadj).IsTrail := by
              rw [SimpleGraph.Walk.isTrail_cons]
              exact ⟨hq, by simpa [Sym2.eq_swap] using hed⟩
            have := hm _ hq'
            simp only [SimpleGraph.Walk.length_cons] at this
            omega
          · by_contra hed
            have hadj : G.Adj z x := ⟨ha, cubeGraph.ne_of_adj (hE ha)⟩
            have hq' : (q.cons hadj).IsTrail := by
              rw [SimpleGraph.Walk.isTrail_cons]
              exact ⟨hq, hed⟩
            have := hm _ hq'
            simp only [SimpleGraph.Walk.length_cons] at this
            omega
      have hu := saturated p hp (fun r hr => maximal r hr)
      have hv := saturated p.reverse hp.reverse (by
        intro z w r hr
        simpa using maximal r hr)
      simp only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at hv
      refine ⟨u, v, p, hp, positive, fun x y q hq => maximal q hq, hu, hv, ?_⟩
      intro huv
      have parity (x : Cube) (hs : ∀ a ∈ E, x ∈ a → a ∈ p.edges) :
          Even ((E.filter (fun a => x ∈ a)).card) ↔ x ≠ u ∧ x ≠ v := by
        have hf : E.filter (fun a => x ∈ a) = p.edges.toFinset.filter (fun a => x ∈ a) := by
          ext a
          simp only [Finset.mem_filter, List.mem_toFinset]
          exact ⟨fun h => ⟨hs a h.1 h.2, h.2⟩, fun h => ⟨edges_in p a h.1, h.2⟩⟩
        have hc := List.toFinset_card_of_nodup (hp.edges_nodup.filter (fun a => decide (x ∈ a)))
        simp only [List.toFinset_filter, decide_eq_true_eq] at hc
        rw [hf, hc, ← List.countP_eq_length_filter]
        simpa [huv] using hp.even_countP_edges_iff x
      constructor
      · simp only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Nat.not_even_iff_odd, parity u hu]
        simp
      · simp only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← Nat.not_even_iff_odd, parity v hv]
        simp
    have metric (u v : Cube) (q : cubeGraph.Walk u v) : hamming4 u v ≤ q.length := by
      have eqh : ∀ x y : Cube, hamming4 x y = hammingDist (bit x) (bit y) := by decide
      induction q with
      | nil => simp [hamming4]
      | @cons x y z h q ih =>
        have ht := hammingDist_triangle (bit x) (bit y) (bit z)
        rw [← eqh, ← eqh, ← eqh] at ht
        have hh : hamming4 x y = 1 := h
        simp only [SimpleGraph.Walk.length_cons]
        omega
    let color : cubeGraph.Coloring Bool := SimpleGraph.Coloring.mk
      (fun b => xor (xor b.1 b.2.1) (xor b.2.2.1 b.2.2.2)) (by
        have h : ∀ x y : Cube, hamming4 x y = 1 →
          xor (xor x.1 x.2.1) (xor x.2.2.1 x.2.2.2) ≠
            xor (xor y.1 y.2.1) (xor y.2.2.1 y.2.2.2) := by decide
        intro x y hxy
        exact h x y hxy)
    have deletion (E : Finset (Sym2 Cube)) {u v : Cube} (q : cubeGraph.Walk u v)
        (hq : q.IsTrail) (hsub : q.edges.toFinset ⊆ E)
        (hterm : u ≠ v → u ∈ oddTerminals E ∧ v ∈ oddTerminals E) :
        oddTerminals (E \ q.edges.toFinset) =
          if u = v then oddTerminals E else oddTerminals E \ {u, v} := by
      let D := q.edges.toFinset
      have counts (x : Cube) :
          ((E \ D).filter (fun a => x ∈ a)).card + (D.filter (fun a => x ∈ a)).card =
            (E.filter (fun a => x ∈ a)).card := by
        have hf : (E \ D).filter (fun a => x ∈ a) =
            (E.filter (fun a => x ∈ a)) \ (D.filter (fun a => x ∈ a)) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨he, hd⟩, hx⟩
            exact ⟨⟨he, hx⟩, fun h => hd h.1⟩
          · rintro ⟨⟨he, hx⟩, hd⟩
            exact ⟨⟨he, fun h => hd ⟨h, hx⟩⟩, hx⟩
        rw [hf]
        exact Finset.card_sdiff_add_card_eq_card (fun a ha =>
          Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩)
      have parity (x : Cube) :
          Even ((D.filter (fun a => x ∈ a)).card) ↔ u ≠ v → x ≠ u ∧ x ≠ v := by
        have hc := List.toFinset_card_of_nodup (hq.edges_nodup.filter (fun a => decide (x ∈ a)))
        simp only [List.toFinset_filter, decide_eq_true_eq] at hc
        change Even ((q.edges.toFinset.filter (fun a => x ∈ a)).card) ↔ _
        rw [hc, ← List.countP_eq_length_filter]
        exact hq.even_countP_edges_iff x
      dsimp only [D] at counts parity
      by_cases huv : u = v
      · simp only [huv, ↓reduceIte]
        ext x
        simp only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and, Nat.odd_iff]
        have hp := parity x
        simp only [huv, ne_eq, not_true_eq_false, false_implies, iff_true, Nat.even_iff] at hp
        have hc := counts x
        omega
      · simp only [huv, ↓reduceIte]
        ext x
        simp only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Nat.odd_iff]
        have hp : ((q.edges.toFinset.filter (fun a => x ∈ a)).card % 2 = 0) ↔
            x ≠ u ∧ x ≠ v := by
          rw [← Nat.even_iff]
          exact (parity x).trans (by simp [huv])
        have hc := counts x
        have hm := congrArg (fun n : ℕ => n % 2) hc
        rw [Nat.add_mod] at hm
        have hu : (E.filter (fun a => u ∈ a)).card % 2 = 1 := by
          simpa only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and, Nat.odd_iff]
            using (hterm huv).1
        have hv : (E.filter (fun a => v ∈ a)).card % 2 = 1 := by
          simpa only [oddTerminals, Finset.mem_filter, Finset.mem_univ, true_and, Nat.odd_iff]
            using (hterm huv).2
        by_cases hxu : x = u
        · subst x
          simp only [ne_eq, not_true_eq_false, false_and, iff_false] at hp
          simp only [true_or, not_true_eq_false, and_false, iff_false]
          omega
        · by_cases hxv : x = v
          · subst x
            simp only [ne_eq, not_true_eq_false, and_false, iff_false] at hp
            simp only [or_true, not_true_eq_false, and_false, iff_false]
            omega
          · have hd := hp.mpr ⟨hxu, hxv⟩
            simp only [hxu, hxv, false_or, not_false_eq_true, and_true]
            constructor <;> intro h <;> omega
    have join_edges (E : Finset (Sym2 Cube)) (l : List (Sym2 Cube))
        (hn : l.Nodup) (hs : l.toFinset ⊆ E) :
        (l ++ (E \ l.toFinset).toList).Perm E.toList := by
      apply (List.perm_ext_iff_of_nodup ?_ E.nodup_toList).2
      · intro a
        simp only [List.mem_append, Finset.mem_toList, Finset.mem_sdiff, List.mem_toFinset]
        exact ⟨fun h => h.elim (fun h => hs (List.mem_toFinset.mpr h)) And.left,
          fun h => by
            by_cases ha : a ∈ l
            · exact Or.inl ha
            · exact Or.inr ⟨h, ha⟩⟩
      · apply List.nodup_append.mpr
        refine ⟨hn, (E \ l.toFinset).nodup_toList, ?_⟩
        intro a ha b hb hab
        subst b
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (List.mem_toFinset.mpr ha)
    intro E
    refine E.strongInductionOn ?_
    intro E ih hE
    by_cases hempty : E = ∅
    · subst E
      exact ⟨[], [], by simp [supportCertificate, oddTerminals]⟩
    obtain ⟨u, v, p, hp, hpos, hmax, hsat0, hsat1, hterm⟩ :=
      longest E hE (Finset.nonempty_iff_ne_empty.mpr hempty)
    let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 Cube))
    have hle : G ≤ cubeGraph :=
      (SimpleGraph.fromEdgeSet_le (G := cubeGraph)).mpr (fun a ha => hE ha.1)
    have supported {x y : Cube} (q : G.Walk x y) : q.edges.toFinset ⊆ E := by
      intro a ha
      have he := q.edges_subset_edgeSet (List.mem_toFinset.mp ha)
      rw [SimpleGraph.edgeSet_fromEdgeSet] at he
      exact he.1
    by_cases huv : u = v
    · subst v
      let c := p.cycleBypass
      have hc : c.IsCycle := hp.isCycle_cycleBypass (by
        intro hn
        have := congrArg SimpleGraph.Walk.length hn
        simp only [SimpleGraph.Walk.length_nil] at this
        omega)
      let cQ := c.mapLe hle
      have hcQ : cQ.IsCycle := hc.mapLe hle
      have hsub : cQ.edges.toFinset ⊆ E := by
        simpa only [cQ, SimpleGraph.Walk.edges_mapLe_eq_edges] using supported c
      have hnon : cQ.edges.toFinset.Nonempty := by
        have hcp : 0 < cQ.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hcQ.not_nil
        have hcard := List.toFinset_card_of_nodup hcQ.isTrail.edges_nodup
        rw [cQ.length_edges] at hcard
        exact Finset.card_pos.mp (by omega)
      have hlt : E \ cQ.edges.toFinset ⊂ E := Finset.sdiff_ssubset hsub hnon
      obtain ⟨ps, cs, hedges, hend, hlen, hcost⟩ := ih _ hlt
        (fun a ha => hE (Finset.mem_sdiff.mp ha).1)
      have hodd := deletion E cQ hcQ.isTrail hsub (by simp)
      simp only [↓reduceIte] at hodd
      let cp : CyclePiece := ⟨u, cQ, hcQ, (color.even_length_iff_congr cQ).mpr Iff.rfl⟩
      refine ⟨ps, cp :: cs, ?_, ?_, ?_, ?_⟩
      · change ((ps.flatMap fun p => p.walk.edges) ++
          (cQ.edges ++ cs.flatMap fun c => c.walk.edges)).Perm E.toList
        have hj := join_edges E cQ.edges hcQ.isTrail.edges_nodup hsub
        have hr := hedges.append_left cQ.edges
        have hswap : ((ps.flatMap fun p => p.walk.edges) ++
            (cQ.edges ++ cs.flatMap fun c => c.walk.edges)).Perm
            (cQ.edges ++ ((ps.flatMap fun p => p.walk.edges) ++
              cs.flatMap fun c => c.walk.edges)) := by
          simpa only [List.append_assoc] using
            (List.perm_append_comm (l₁ := ps.flatMap fun p => p.walk.edges)
              (l₂ := cQ.edges)).append_right (cs.flatMap fun c => c.walk.edges)
        exact hswap.trans (hr.trans hj)
      · simpa only [hodd] using hend
      · have hd := Finset.card_sdiff_add_card_eq_card hsub
        have hc := List.toFinset_card_of_nodup hcQ.isTrail.edges_nodup
        rw [cQ.length_edges] at hc
        simp only [List.map_cons, List.sum_cons]
        change (ps.map fun p => p.walk.length).sum +
          (cQ.length + (cs.map fun c => c.walk.length).sum) = E.card
        omega
      · exact hcost
    · let q := p.toPath.val
      have hq : q.IsPath := p.toPath.property
      let qQ := q.mapLe hle
      have hqQ : qQ.IsPath := hq.mapLe hle
      have hsub : qQ.edges.toFinset ⊆ E := by
        simpa only [qQ, SimpleGraph.Walk.edges_mapLe_eq_edges] using supported q
      have hnon : qQ.edges.toFinset.Nonempty := by
        have hpos : 0 < qQ.length := by
          by_contra hz
          exact huv (SimpleGraph.Walk.eq_of_length_eq_zero (by omega : qQ.length = 0))
        have hcard := List.toFinset_card_of_nodup hqQ.isTrail.edges_nodup
        rw [qQ.length_edges] at hcard
        exact Finset.card_pos.mp (by omega)
      have hlt : E \ qQ.edges.toFinset ⊂ E := Finset.sdiff_ssubset hsub hnon
      obtain ⟨ps, cs, hedges, hend, hlen, hcost⟩ := ih _ hlt
        (fun a ha => hE (Finset.mem_sdiff.mp ha).1)
      have hodd := deletion E qQ hqQ.isTrail hsub hterm
      simp only [huv, ↓reduceIte] at hodd
      let pp : PathPiece := ⟨u, v, qQ, hqQ, huv⟩
      refine ⟨pp :: ps, cs, ?_, ?_, ?_, ?_⟩
      · change (qQ.edges ++ (ps.flatMap fun p => p.walk.edges) ++
          (cs.flatMap fun c => c.walk.edges)).Perm E.toList
        have hr := hedges.append_left qQ.edges
        have hj := join_edges E qQ.edges hqQ.isTrail.edges_nodup hsub
        simpa only [List.append_assoc] using hr.trans hj
      · change ([u, v] ++ ps.flatMap fun p => [p.start, p.finish]).Perm (oddTerminals E).toList
        have hs : ([u, v] : List Cube).toFinset ⊆ oddTerminals E := by
          intro x hx
          simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
            Finset.notMem_empty, or_false] at hx
          rcases hx with rfl | rfl
          · exact (hterm huv).1
          · exact (hterm huv).2
        have hn : ([u, v] : List Cube).Nodup := by simp [huv]
        have hperm : ([u, v] ++ (oddTerminals E \ {u, v}).toList).Perm (oddTerminals E).toList := by
          apply (List.perm_ext_iff_of_nodup ?_ (oddTerminals E).nodup_toList).2
          · intro x
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
              Finset.mem_toList,
              Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro hx
              rcases hx with (rfl | rfl) | hx
              · exact (hterm huv).1
              · exact (hterm huv).2
              · exact hx.1
            · intro hx
              by_cases hxu : x = u
              · exact Or.inl (Or.inl hxu)
              · by_cases hxv : x = v
                · exact Or.inl (Or.inr hxv)
                · exact Or.inr ⟨hx, by simp [hxu, hxv]⟩
          · apply List.nodup_append.mpr
            refine ⟨hn, (oddTerminals E \ {u, v}).nodup_toList, ?_⟩
            intro x hx y hy hxy
            subst y
            exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hy)).2 (by simpa using hx)
        have hr := hend.append_left [u, v]
        rw [hodd] at hr
        exact hr.trans hperm
      · have hd := Finset.card_sdiff_add_card_eq_card hsub
        have hc := List.toFinset_card_of_nodup hqQ.isTrail.edges_nodup
        rw [qQ.length_edges] at hc
        simp only [List.map_cons, List.sum_cons]
        change (qQ.length + (ps.map fun p => p.walk.length).sum) +
          (cs.map fun c => c.walk.length).sum = E.card
        omega
      · change hamming4 u v + _ ≤ qQ.length + _
        exact Nat.add_le_add (metric u v qQ) hcost
  have inj : Function.Injective dualEdge := by decide
  have adj : ∀ f : Face, dualEdge f ∈ cubeGraph.edgeSet := by
    have h : ∀ f : Face, hamming4 (insertZero f.1 f.2) (insertOne f.1 f.2) = 1 := by decide
    exact h
  have incidence : ∀ (b : Cube) (f : Face), b ∈ dualEdge f ↔ drop f.1 b = f.2 := by decide
  have bit_value : ∀ z : ZMod 2, (if z ≠ 0 then 1 else 0) = z := by decide
  have support_data (F : Cochain) : (supportEdges F).card = weight F ∧
      oddTerminals (supportEdges F) = syndrome F := by
    have count : (supportEdges F).card = weight F := by
      rw [supportEdges, Finset.card_image_of_injective _ inj]
      simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]
    have boundary (b : Cube) :
        (((supportEdges F).filter (fun a => b ∈ a)).card : ZMod 2) = d2 F b := by
      calc
        (((supportEdges F).filter (fun a => b ∈ a)).card : ZMod 2) =
            ∑ f : Face, if b ∈ dualEdge f then F f else 0 := by
          rw [supportEdges, Finset.filter_image, Finset.card_image_of_injective _ inj,
            Finset.card_eq_sum_ones, Nat.cast_sum]
          simp only [Finset.sum_filter, Nat.cast_one]
          apply Finset.sum_congr rfl
          intro f hf
          by_cases hi : b ∈ dualEdge f <;> simp only [hi, ↓reduceIte, bit_value, ite_self]
        _ = d2 F b := by
          rw [Fintype.sum_prod_type]
          simp only [incidence, d2]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    refine ⟨count, ?_⟩
    ext b
    simp only [oddTerminals, syndrome, Finset.mem_filter, Finset.mem_univ, true_and,
      ← ZMod.natCast_ne_zero_iff_odd, boundary]
  have pair_from_paths (E : Finset (Sym2 Cube)) (ps : List PathPiece) (cs : List CyclePiece)
      (hcert : supportCertificate E ps cs) :
      ∃ P : List (Sym2 Cube), IsPairing (oddTerminals E) P ∧ pairingCost P ≤ E.card := by
    let P := ps.map (fun p => s(p.start, p.finish))
    have hp (p : PathPiece) : s(p.start, p.finish).toFinset.toList.Perm [p.start, p.finish] := by
      apply (List.perm_ext_iff_of_nodup (s(p.start, p.finish).toFinset.nodup_toList)
        (by simp [p.distinct])).2
      intro x
      simp [Sym2.toFinset_mk_eq]
    have hconvert :
        (P.flatMap fun a => a.toFinset.toList).Perm (ps.flatMap fun p => [p.start, p.finish]) := by
      dsimp only [P]
      clear hcert
      induction ps with
      | nil => simp
      | cons p ps ih =>
        simp only [List.map_cons, List.flatMap_cons]
        exact (hp p).append ih
    have hcost : pairingCost P = (ps.map fun p => hamming4 p.start p.finish).sum := by
      simp only [pairingCost, P, List.map_map, Function.comp_def, pairCost, Sym2.lift_mk]
    refine ⟨P, ⟨?_, hconvert.trans hcert.2.1⟩, ?_⟩
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      simpa only [Sym2.mk_isDiag_iff] using p.distinct
    · rw [hcost]
      have := hcert.2.2.1
      have := hcert.2.2.2
      omega
  have subadd (H K : Cochain) : weight (H + K) ≤ weight H + weight K := by
    simp only [weight, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro f hf
    by_cases hH : H f = 0 <;> by_cases hK : K f = 0 <;> simp [hH, hK]
    split <;> omega
  have geo_cost (a : Sym2 Cube) : weight (geodesic a.out.1 a.out.2) = pairCost a := by
    rw [geodesic_weight]
    have hout : s(a.out.1, a.out.2) = a := a.out_eq
    conv_rhs => rw [← hout, pairCost, Sym2.lift_mk]
  have route (S : Finset Cube) (P : List (Sym2 Cube)) (hP : IsPairing S P) :
      ∃ H : Cochain, (∀ b : Cube, d2 H b = if b ∈ S then 1 else 0) ∧
        weight H ≤ pairingCost P := by
    let H : Cochain := (P.map fun a => geodesic a.out.1 a.out.2).sum
    have endpoint (a : Sym2 Cube) (ha : ¬a.IsDiag) (b : Cube) :
        d2 (geodesic a.out.1 a.out.2) b = (a.toFinset.toList.count b : ZMod 2) := by
      have hout : s(a.out.1, a.out.2) = a := a.out_eq
      have hne : a.out.1 ≠ a.out.2 := by
        intro he
        exact ha (by rw [← hout, Sym2.mk_isDiag_iff]; exact he)
      have hm : b ∈ a ↔ b = a.out.1 ∨ b = a.out.2 := by
        conv_lhs => rw [← hout, Sym2.mem_iff]
      have hc : a.toFinset.toList.count b = if b ∈ a then 1 else 0 := by
        by_cases hb : b ∈ a
        · simp only [hb, ↓reduceIte]
          exact List.count_eq_one_of_mem a.toFinset.nodup_toList
            (Finset.mem_toList.mpr (Sym2.mem_toFinset.mpr hb))
        · simp only [hb, ↓reduceIte]
          exact List.count_eq_zero_of_not_mem (by
            simpa only [Finset.mem_toList, Sym2.mem_toFinset] using hb)
      rw [geodesic_boundary, hc]
      by_cases hb0 : b = a.out.1 <;> by_cases hb1 : b = a.out.2
      · exact (hne (hb0.symm.trans hb1)).elim
      · rw [if_pos hb0, if_neg hb1, if_pos (hm.mpr (Or.inl hb0))]
        simp
      · rw [if_neg hb0, if_pos hb1, if_pos (hm.mpr (Or.inr hb1))]
        simp
      · have hb : b ∉ a := fun h => (hm.mp h).elim hb0 hb1
        rw [if_neg hb0, if_neg hb1, if_neg hb]
        simp
    have bd (Q : List (Sym2 Cube)) (hQ : ∀ a ∈ Q, ¬a.IsDiag) (b : Cube) :
        d2 ((Q.map fun a => geodesic a.out.1 a.out.2).sum) b =
          ((Q.flatMap fun a => a.toFinset.toList).count b : ZMod 2) := by
      induction Q with
      | nil => simp [d2]
      | cons a Q ih =>
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.count_append, Nat.cast_add]
        rw [show d2 (geodesic a.out.1 a.out.2 +
          (Q.map fun a => geodesic a.out.1 a.out.2).sum) b =
          d2 (geodesic a.out.1 a.out.2) b +
          d2 ((Q.map fun a => geodesic a.out.1 a.out.2).sum) b by
            simp only [d2, Pi.add_apply, Finset.sum_add_distrib]]
        rw [endpoint a (hQ a (by simp)) b, ih (fun a ha => hQ a (by simp [ha]))]
    have cost (Q : List (Sym2 Cube)) :
        weight ((Q.map fun a => geodesic a.out.1 a.out.2).sum) ≤ pairingCost Q := by
      induction Q with
      | nil => simp [weight, pairingCost]
      | cons a Q ih =>
        simp only [List.map_cons, List.sum_cons, pairingCost] at ih ⊢
        exact le_trans (subadd _ _) (Nat.add_le_add (geo_cost a).le ih)
    refine ⟨H, ?_, cost P⟩
    intro b
    rw [bd P hP.1 b, hP.2.count_eq]
    by_cases hb : b ∈ S
    · simp only [hb, ↓reduceIte]
      congr 1
      exact List.count_eq_one_of_mem S.nodup_toList (Finset.mem_toList.mpr hb)
    · simp only [hb, ↓reduceIte]
      rw [List.count_eq_zero_of_not_mem (by simpa only [Finset.mem_toList] using hb)]
      rfl
  have chain (e : EdgeCochain) (b : Cube) : d2 (d1 e) b = 0 := by
    rcases b with ⟨a, c, d, f⟩
    cases a <;> cases c <;> cases d <;> cases f <;>
      simp [d2, d1, triA, triB, triC, drop, Fin.sum_univ_succ] <;>
      ring_nf <;> simp [show (2 : ZMod 2) = 0 by decide]
  refine ⟨inj, adj, decomposition, support_data, ?_,
    (antipodal_repair_sharpness).2.2.2.2.2.2.2.2⟩
  intro F k
  constructor
  · rintro ⟨e, he⟩
    let H := F + d1 e
    have hE : (supportEdges H : Set (Sym2 Cube)) ⊆ cubeGraph.edgeSet := by
      intro a ha
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ha
      exact adj f
    obtain ⟨ps, cs, hcert⟩ := decomposition (supportEdges H) hE
    obtain ⟨P, hP, hcost⟩ := pair_from_paths (supportEdges H) ps cs hcert
    have hsame : syndrome H = syndrome F := by
      ext b
      simp only [syndrome, Finset.mem_filter, Finset.mem_univ, true_and]
      have hb : d2 H b = d2 F b := by
        change d2 (F + d1 e) b = d2 F b
        rw [show d2 (F + d1 e) b = d2 F b + d2 (d1 e) b by
          simp only [d2, Pi.add_apply, Finset.sum_add_distrib]]
        rw [chain, add_zero]
      rw [hb]
    refine ⟨P, ?_, ?_⟩
    · rw [← hsame, ← (support_data H).2]
      exact hP
    · rw [(support_data H).1] at hcost
      exact hcost.trans he
  · rintro ⟨P, hP, hcost⟩
    obtain ⟨H, hH, hweight⟩ := route (syndrome F) P hP
    have hzero (b : Cube) : d2 (F + H) b = 0 := by
      rw [show d2 (F + H) b = d2 F b + d2 H b by
        simp only [d2, Pi.add_apply, Finset.sum_add_distrib]]
      rw [hH]
      have hi : (if b ∈ syndrome F then (1 : ZMod 2) else 0) = d2 F b := by
        simpa only [syndrome, Finset.mem_filter, Finset.mem_univ, true_and] using bit_value (d2 F b)
      rw [hi]
      exact CharTwo.add_self_eq_zero _
    have hdef : defects (F + H) = 0 := by
      simp only [defects, hzero, ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero]
    obtain ⟨e, he⟩ := ((D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.universal_repair 2 1).mpr
      (by decide)) (F + H)
    rw [hdef] at he
    have hz : weight ((F + H) + d1 e) = 0 := by omega
    have hzfun : (F + H) + d1 e = 0 := by
      funext f
      have hs : (∑ g : Face, if ((F + H) + d1 e) g ≠ 0 then (1 : ℕ) else 0) = 0 := hz
      have hp := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => Nat.zero_le _)).mp
        hs f (Finset.mem_univ f)
      change ((F + H) + d1 e) f = 0
      by_contra hf
      rw [if_pos hf] at hp
      exact Nat.one_ne_zero hp
    have heq : F + d1 e = H := by
      funext f
      have hf := congrFun hzfun f
      simp only [Pi.add_apply, Pi.zero_apply] at hf
      calc
        F f + d1 e f = (F f + H f + d1 e f) + H f := by
          ring_nf
          simp [show (2 : ZMod 2) = 0 by decide]
        _ = H f := by rw [hf, zero_add]
    refine ⟨e, ?_⟩
    rw [heq]
    exact hweight.trans hcost

#print axioms fourcube_exact_budget

end D5.S3.Combinatorics.Graph.QuadripartiteH2ExactBudget

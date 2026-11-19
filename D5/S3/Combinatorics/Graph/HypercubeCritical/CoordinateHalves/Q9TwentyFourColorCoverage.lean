import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding

/-! Transport the finite coloring certificates to graphs labeled by the
twelve high vertices of a coordinate half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyFourCompression (half_suppression)
open GirthSliceCounting (degreeThree)
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private suppress from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourCompression
open private SideHigh from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private Graph adjacent decode labels representatives from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphSearch
open private representative_of_graph witnessPerm eraseDups_spec from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourGraphEncoding
open private High vertex side directCount girth_le_expanded_length circuit_of_vertex_list from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourExpansion
open private models coloredCases graphEdges admissible validCycle relabelsColor checkCase
  checked cycleEdges crosses vertices ColorCase.cycles ColorCase.witnesses from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColors

attribute [local instance] Classical.propDecidable

private theorem representative_of_half {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 24) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let J := suppress G (paritySide S false) (paritySide S true)
    ∃ (index : Fin 22) (label : Fin 12 ≃ _), ∀ i j,
      adjacent (decode representatives[index.val]!) i.val j.val = true ↔
        J.Adj (label i) (label j) := by
  obtain ⟨hc, hd, ht, hconn⟩ := half_suppression hC hr hb b hs
  exact representative_of_graph _ hc hconn hd ht (Classical.choice hconn.nonempty)

set_option maxRecDepth 4096 in
private theorem coloring_certificate (index : Fin 22) (group : Nat) (hgroup : group < 4096)
    (hvalid : admissible (graphEdges (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ word, relabelsColor (decode representatives[index.val]!) group word = true := by
  let graph := decode representatives[index.val]!
  let cert := coloredCases[index.val]!
  have hc := checked index
  unfold checkCase at hc
  change ((ColorCase.cycles cert).all (validCycle graph) &&
    (List.range 4096).all fun group =>
      !admissible (graphEdges graph) (ColorCase.cycles cert) group ||
        match List.lookup group (ColorCase.witnesses cert) with
        | none => false
        | some witness => relabelsColor graph group witness) = true at hc
  have hw := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 group
    (List.mem_range.mpr hgroup)
  change admissible (graphEdges graph) (ColorCase.cycles cert) group = true at hvalid
  simp only [hvalid, Bool.not_true, Bool.false_or] at hw
  split at hw
  · cases hw
  · rename_i word _
    exact ⟨word, hw⟩

/-- A certified coloring yields both an adjacency-preserving permutation and
agreement of the parity classes up to a global exchange. -/
private theorem colored_representative (index : Fin 22) (group : Nat) (hgroup : group < 4096)
    (hvalid : admissible (graphEdges (decode representatives[index.val]!))
      (ColorCase.cycles coloredCases[index.val]!) group = true) :
    ∃ (model : Fin 53) (p : Equiv.Perm (Fin 12)) (reverse : Bool),
      (∀ i j : Fin 12, adjacent (decode representatives[index.val]!) i.val j.val =
        adjacent (decode models[model.val]!.1) (p i).val (p j).val) ∧
      (∀ i : Fin 12, group.testBit i.val =
        (models[model.val]!.2.testBit (p i).val ^^ reverse)) := by
  obtain ⟨word, hw⟩ := coloring_certificate index group hgroup hvalid
  let modelIndex := word >>> 48
  let model := models[modelIndex]!
  let reverse := group.testBit 0 != model.2.testBit (labels word 0)
  change (decide (modelIndex < models.size) &&
    (List.range 12).all (fun i => decide (labels word i < 12)) &&
    (((List.range 12).map (labels word)).eraseDups.length == 12) &&
    (List.range 12).all (fun i => (List.range 12).all fun j =>
      adjacent (decode representatives[index.val]!) i j ==
        adjacent (decode model.1) (labels word i) (labels word j)) &&
    (List.range 12).all (fun i => group.testBit i == (model.2.testBit (labels word i) ^^ reverse)))
      = true at hw
  obtain ⟨⟨⟨⟨hindex, hbound⟩, hnodup⟩, hgraph⟩, hcolor⟩ := by
    simpa only [Bool.and_eq_true_iff] using hw
  let p := witnessPerm word (fun i hi =>
    of_decide_eq_true (List.all_eq_true.mp hbound _ (List.mem_range.mpr hi)))
    (beq_iff_eq.mp hnodup)
  have hsize : models.size = 53 := rfl
  refine ⟨⟨modelIndex, hsize ▸ of_decide_eq_true hindex⟩, p, reverse, ?_, ?_⟩
  · intro i j
    exact beq_iff_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hgraph _ (List.mem_range.mpr i.isLt)) _
      (List.mem_range.mpr j.isLt))
  · intro i
    exact beq_iff_eq.mp (List.all_eq_true.mp hcolor _ (List.mem_range.mpr i.isLt))

private theorem cycle_respects_girth {V : Type*} [Fintype V] {G : SimpleGraph V}
    {L R : Finset V} (hdisj : Disjoint L R) (hg : (8 : ℕ∞) ≤ G.egirth)
    (index : Fin 22) (label : Fin 12 ≃ High G L R)
    (hlabel : ∀ i j : Fin 12, adjacent (decode representatives[index.val]!) i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j))
    (group : Nat) (reverse : Bool)
    (hcolor : ∀ i : Fin 12, group.testBit i.val = (side (label i) ^^ reverse))
    (cycle : List Nat) (hc : validCycle (decode representatives[index.val]!) cycle = true) :
    8 ≤ 2 * cycle.length - (cycleEdges cycle).countP (fun (u, v) => crosses group u v) := by
  obtain ⟨⟨⟨⟨hlen, _⟩, hnd⟩, hb⟩, he⟩ := by
    simpa only [validCycle, Bool.and_eq_true_iff] using hc
  cases cycle with
  | nil => simp at hlen
  | cons a xs =>
    let cast (i : Nat) := label (Fin.ofNat 12 i)
    have hbound (i : Nat) (hi : i ∈ a :: xs) : i < 12 :=
      of_decide_eq_true (List.all_eq_true.mp hb i hi)
    have hval (i : Nat) (hi : i ∈ a :: xs) : (Fin.ofNat 12 i).val = i :=
      Nat.mod_eq_of_lt (hbound i hi)
    have hnodup : ((a :: xs).map cast).Nodup := by
      have hs := eraseDups_spec (a :: xs)
      have hn := (hs.1.length_eq.mp (beq_iff_eq.mp hnd)) ▸ hs.2
      apply (List.nodup_map_iff_inj_on hn).mpr
      intro i hi j hj h
      exact (hval i hi).symm.trans ((congrArg Fin.val (label.injective h)).trans (hval j hj))
    have hstep {q : Nat × Nat} (hq : q ∈ cycleEdges (a :: xs)) :
        q.1 ∈ a :: xs ∧ q.2 ∈ a :: xs := by
      obtain ⟨hq₁, hq₂⟩ := List.of_mem_zip hq
      change q.2 ∈ xs ++ [a] at hq₂
      exact ⟨hq₁, by simpa [or_comm] using hq₂⟩
    have hmap : (cast a :: xs.map cast).zip (xs.map cast ++ [cast a]) =
        (cycleEdges (a :: xs)).map (Prod.map cast cast) := by
      change ((a :: xs).map cast).zip _ = _
      rw [show xs.map cast ++ [cast a] = (xs ++ [a]).map cast by simp, List.zip_map]
      rfl
    have hadj : ∀ q ∈ (cast a :: xs.map cast).zip (xs.map cast ++ [cast a]),
        (suppress G L R).Adj q.1 q.2 := by
      intro q hq
      rw [hmap] at hq
      obtain ⟨⟨i, j⟩, hm, rfl⟩ := List.mem_map.mp hq
      obtain ⟨hi, hj⟩ := hstep hm
      have ha := List.all_eq_true.mp he (i, j) hm
      change adjacent (decode representatives[index.val]!) i j = true at ha
      apply (hlabel (Fin.ofNat 12 i) (Fin.ofNat 12 j)).mp
      rw [hval i hi, hval j hj]
      exact ha
    have hl : 3 ≤ (cast a :: xs.map cast).length := by
      simp only [List.length_cons, List.length_map]
      exact (by decide : 3 ≤ 4).trans (of_decide_eq_true hlen)
    obtain ⟨w, hw, hlength, hzip⟩ :=
      circuit_of_vertex_list (cast a) (xs.map cast) hnodup hl hadj
    have hlength' : w.length = (a :: xs).length := by simpa using hlength
    have hcount : directCount w =
        (cycleEdges (a :: xs)).countP (fun (u, v) => crosses group u v) := by
      let f : High G L R × High G L R → Bool := fun (x, y) => side x != side y
      change w.darts.countP (fun d => f (d.fst, d.snd)) = _
      have hm : w.darts.countP (fun d => f (d.fst, d.snd)) =
          (w.darts.map (fun d => (d.fst, d.snd))).countP f :=
        (List.countP_map (p := f) (f := fun d : (suppress G L R).Dart => (d.fst, d.snd))).symm
      rw [hm, hzip, hmap, List.countP_map]
      apply List.countP_congr
      intro q hq
      obtain ⟨ha, hb⟩ := hstep hq
      have hca := hcolor (Fin.ofNat 12 q.1)
      have hcb := hcolor (Fin.ofNat 12 q.2)
      rw [hval q.1 ha] at hca
      rw [hval q.2 hb] at hcb
      change (side (cast q.1) != side (cast q.2)) = true ↔
        (group.testBit q.1 != group.testBit q.2) = true
      rw [hca, hcb]
      cases side (cast q.1) <;> cases side (cast q.2) <;> cases reverse <;> decide
    have h := hg.trans (girth_le_expanded_length hdisj hw)
    rw [hlength', hcount] at h
    exact_mod_cast h

private theorem mem_graphEdges (graph : Graph) (i j : Nat) :
    (i, j) ∈ graphEdges graph ↔ i < 12 ∧ j < 12 ∧ i < j ∧ adjacent graph i j = true := by
  simp [graphEdges, vertices, List.mem_flatMap, List.mem_filter, List.mem_map, and_assoc]

private theorem graphEdges_nodup (graph : Graph) : (graphEdges graph).Nodup := by
  unfold graphEdges
  apply List.nodup_flatMap.mpr
  constructor
  · intro u hu
    exact ((List.nodup_range).filter _).map (fun _ _ h => congrArg Prod.snd h)
  · apply (List.nodup_range).imp
    intro u v hne e hu hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
    obtain ⟨b, _, he⟩ := List.mem_map.mp hv
    exact hne (congrArg Prod.fst he.symm)

private theorem count_cross_eq_card (graph : Graph) (group : Nat) :
    (graphEdges graph).countP (fun (i, j) => crosses group i j) =
      ((graphEdges graph).toFinset.filter (fun p => crosses group p.1 p.2 = true)).card := by
  let good (p : Nat × Nat) := crosses group p.1 p.2
  let edges := graphEdges graph
  have hcount := List.toFinset_card_of_nodup ((graphEdges_nodup graph).filter good)
  change edges.countP good = _
  rw [List.countP_eq_length_filter, ← hcount, List.toFinset_filter]

private theorem cross_of_side {V : Type*} [Fintype V] {G : SimpleGraph V}
    {L R : Finset V} (label : Fin 12 ≃ High G L R) (group : Nat) (reverse : Bool)
    (hcolor : ∀ i : Fin 12, group.testBit i.val = (side (label i) ^^ reverse))
    (i j : Fin 12) :
    crosses group i.val j.val = true ↔ side (label i) ≠ side (label j) := by
  unfold crosses
  rw [hcolor i, hcolor j]
  cases side (label i) <;> cases side (label j) <;> cases reverse <;> simp

private theorem count_direct_edges {V : Type*} [Fintype V] {G : SimpleGraph V}
    {L R : Finset V} (hbip : G.IsBipartiteWith (L : Set V) (R : Set V)) (graph : Graph)
    (label : Fin 12 ≃ High G L R)
    (hlabel : ∀ i j : Fin 12, adjacent graph i.val j.val = true ↔
      (suppress G L R).Adj (label i) (label j))
    (group : Nat) (reverse : Bool)
    (hcolor : ∀ i : Fin 12, group.testBit i.val = (side (label i) ^^ reverse)) :
    (graphEdges graph).countP (fun (i, j) => crosses group i j) =
      ∑ v ∈ degreeThree G R, (degreeThree G (G.neighborFinset v)).card := by
  classical
  let cross := (graphEdges graph).toFinset.filter (fun p => crosses group p.1 p.2 = true)
  let directed := (degreeThree G R).sigma (fun y => degreeThree G (G.neighborFinset y))
  rw [count_cross_eq_card, ← Finset.card_sigma]
  change cross.card = directed.card
  symm
  let order (i j : Fin 12) : Nat × Nat :=
    if i.val < j.val then (i.val, j.val) else (j.val, i.val)
  have horder (i j : Fin 12) (hn : i ≠ j) :
      order i j = (i.val, j.val) ∧ i.val < j.val ∨
        order i j = (j.val, i.val) ∧ j.val < i.val := by
    by_cases h : i.val < j.val
    · exact Or.inl ⟨ite_eq_left h, h⟩
    · exact Or.inr ⟨ite_eq_right h, by
        have := fun he : i.val = j.val => hn (Fin.ext he)
        omega⟩
  let leftLabel (v : V) (hv : v ∈ L) (hd : G.degree v = 3) : Fin 12 :=
    label.symm (Sum.inl ⟨v, mem_filter.mpr ⟨hv, hd⟩⟩)
  let rightLabel (v : V) (hv : v ∈ degreeThree G R) : Fin 12 :=
    label.symm (Sum.inr ⟨v, hv⟩)
  have left_side (v : V) (hv : v ∈ L) (hd : G.degree v = 3) :
      side (label (leftLabel v hv hd)) = false := by simp [leftLabel, side]
  have right_side (v : V) (hv : v ∈ degreeThree G R) :
      side (label (rightLabel v hv)) = true := by simp [rightLabel, side]
  have left_mem (q : Sigma fun _ : V => V) (hq : q ∈ directed) : q.2 ∈ L :=
    hbip.mem_of_mem_adj' (mem_filter.mp (mem_sigma.mp hq).1).1
      ((G.mem_neighborFinset _ _).mp (mem_filter.mp (mem_sigma.mp hq).2).1).symm
  let il (q : Sigma fun _ : V => V) (hq : q ∈ directed) :=
    leftLabel q.2 (left_mem q hq) (mem_filter.mp (mem_sigma.mp hq).2).2
  let ir (q : Sigma fun _ : V => V) (hq : q ∈ directed) :=
    rightLabel q.1 (mem_sigma.mp hq).1
  have hleft (q : Sigma fun _ : V => V) (hq : q ∈ directed) :
      side (label (il q hq)) = false :=
    left_side q.2 (left_mem q hq) (mem_filter.mp (mem_sigma.mp hq).2).2
  have hright (q : Sigma fun _ : V => V) (hq : q ∈ directed) :
      side (label (ir q hq)) = true := right_side q.1 (mem_sigma.mp hq).1
  have hd (q : Sigma fun _ : V => V) (hq : q ∈ directed) : il q hq ≠ ir q hq := by
    intro he
    have h := hleft q hq
    rw [he, hright q hq] at h
    cases h
  have hdirect (q : Sigma fun _ : V => V) (hq : q ∈ directed) :
      (suppress G L R).Adj (label (ir q hq)) (label (il q hq)) := by
    simp only [ir, il, rightLabel, leftLabel, Equiv.apply_symm_apply]
    exact (G.mem_neighborFinset _ _).mp (mem_filter.mp (mem_sigma.mp hq).2).1
  have in_cross (i j : Fin 12) (hij : i.val < j.val)
      (ha : (suppress G L R).Adj (label i) (label j))
      (hne : side (label i) ≠ side (label j)) : (i.val, j.val) ∈ cross :=
    mem_filter.mpr ⟨List.mem_toFinset.mpr
      ((mem_graphEdges graph _ _).mpr ⟨i.isLt, j.isLt, hij, (hlabel i j).mpr ha⟩),
      (cross_of_side label group reverse hcolor i j).mpr hne⟩
  refine Finset.card_bij (fun q hq => order (il q hq) (ir q hq)) ?_ ?_ ?_
  · intro q hq
    rcases horder (il q hq) (ir q hq) (hd q hq) with ⟨he, hlt⟩ | ⟨he, hlt⟩
    · rw [he]
      exact in_cross _ _ hlt (hdirect q hq).symm (by rw [hleft q hq, hright q hq]; decide)
    · rw [he]
      exact in_cross _ _ hlt (hdirect q hq) (by rw [hleft q hq, hright q hq]; decide)
  · intro a ha b hb he
    have from_left (h : il a ha = il b hb) : a.2 = b.2 := by
      have h := congrArg (fun i => vertex (label i)) h
      simpa only [il, leftLabel, Equiv.apply_symm_apply,
        vertex, Sum.elim_inl] using h
    have from_right (h : ir a ha = ir b hb) : a.1 = b.1 := by
      have h := congrArg (fun i => vertex (label i)) h
      simpa only [ir, rightLabel, Equiv.apply_symm_apply,
        vertex, Sum.elim_inr] using h
    have swap_impossible : il a ha ≠ ir b hb := by
      intro hh
      have h := hleft a ha
      rw [hh, hright b hb] at h
      cases h
    rcases horder (il a ha) (ir a ha) (hd a ha) with ⟨hA, _⟩ | ⟨hA, _⟩ <;>
      rcases horder (il b hb) (ir b hb) (hd b hb) with ⟨hB, _⟩ | ⟨hB, _⟩
    · rw [hA, hB, Prod.mk.injEq] at he
      exact Sigma.ext (from_right (Fin.ext he.2)) (heq_of_eq (from_left (Fin.ext he.1)))
    · rw [hA, hB, Prod.mk.injEq] at he
      exact (swap_impossible (Fin.ext he.1)).elim
    · rw [hA, hB, Prod.mk.injEq] at he
      exact (swap_impossible (Fin.ext he.2)).elim
    · rw [hA, hB, Prod.mk.injEq] at he
      exact Sigma.ext (from_right (Fin.ext he.1)) (heq_of_eq (from_left (Fin.ext he.2)))
  · rintro ⟨i, j⟩ hp
    obtain ⟨hedge, hcross⟩ := mem_filter.mp hp
    obtain ⟨hi, hj, hij, hadj⟩ := (mem_graphEdges graph i j).mp (List.mem_toFinset.mp hedge)
    let a : Fin 12 := ⟨i, hi⟩
    let b : Fin 12 := ⟨j, hj⟩
    have hJ := (hlabel a b).mp hadj
    have hs := (cross_of_side label group reverse hcolor a b).mp hcross
    cases ha : label a with
    | inl x =>
      cases hb : label b with
      | inl y => exact (hs (by rw [ha, hb]; rfl)).elim
      | inr y =>
        rw [ha, hb] at hJ
        let q : Sigma fun _ : V => V := ⟨y.val, x.val⟩
        have hq : q ∈ directed := mem_sigma.mpr ⟨y.property,
          mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hJ.symm, (mem_filter.mp x.property).2⟩⟩
        have hl : il q hq = a := label.symm_apply_eq.mpr ha.symm
        have hr : ir q hq = b := label.symm_apply_eq.mpr hb.symm
        exact ⟨q, hq, by rw [hl, hr]; exact ite_eq_left hij⟩
    | inr x =>
      cases hb : label b with
      | inr y => exact (hs (by rw [ha, hb]; rfl)).elim
      | inl y =>
        rw [ha, hb] at hJ
        let q : Sigma fun _ : V => V := ⟨x.val, y.val⟩
        have hq : q ∈ directed := mem_sigma.mpr ⟨x.property,
          mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hJ, (mem_filter.mp y.property).2⟩⟩
        have hl : il q hq = b := label.symm_apply_eq.mpr hb.symm
        have hr : ir q hq = a := label.symm_apply_eq.mpr ha.symm
        exact ⟨q, hq, by rw [hl, hr]; exact ite_eq_right (Nat.not_lt_of_ge hij.le)⟩

#print axioms representative_of_half
#print axioms colored_representative
#print axioms cycle_respects_girth
#print axioms count_direct_edges

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyFourColorCoverage

/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoPairedExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Excludes a 22-vertex coordinate half of an order-72 Huang-balanced cubic support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedAxes
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExtension
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedMatching

/-! Exclude the paired compression on a realized 22-point half. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExclusion

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyTwoPairedAxes (normalize_paired_paths)
open Q9TwentyTwoPairedCoverage (normalized_placement_excess_degree)
open Q9TwentyTwoPairedExtension (no_extension_of_excess_degree)
open Q9TwentyTwoSingletonLabels (select_subdivision_vertices_of_paths)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open Q9TwentyTwoPairedMatching (paired_model_labels)
open Q9TwentyTwoSingletonExclusion (paired_compression)
open private coordinate_slice_low_independent coordinate_slice_degree_cases balanced_subset
  paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open HuangBalancedSymmetry (cube_action_regular_balanced)
open private adjacent adjacent_iff hasTwoSetBits moves toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SeventyTwoEmbeddingSearch
open private labels middleOptions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
open private separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage
open private adjacency_to_toggle two_step from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonExclusion
open private solidEdges hollowEdges valid seed searchOrder stepOptions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements

local notation "flip" => BalancedCriticalSpectrum.flip
private abbrev Vertex := BitVec 9

private theorem edge_order : ∀ e : Fin 10 × Fin 10, e ∈ hollowEdges → e.1 < e.2 := by
  decide

private theorem edge_sizes : hollowEdges.Nodup ∧ hollowEdges.length = 12 := by decide

private theorem search_edge : ∀ s : Fin 10 × Fin 10 × Bool, s ∈ searchOrder →
    if s.2.2 then (s.2.1, s.1) ∈ solidEdges
    else (s.2.1, s.1) ∈ hollowEdges ∨ (s.1, s.2.1) ∈ hollowEdges := by
  decide

attribute [local instance] Classical.propDecidable

/-- Neither paired placement can occur in an actual 22-vertex half. -/
theorem no_paired_model {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22)
    (p : Fin 10 ↪ (coordinateSlice C b : Set (Q 9)))
    (hhigh : ∀ i, ((hypercube 9).induce (coordinateSlice C b : Set (Q 9))).degree (p i) = 3)
    (hsolid : ∀ i j, i < j →
      (((hypercube 9).induce (coordinateSlice C b : Set (Q 9))).Adj (p i) (p j) ↔
        (i, j) ∈ solidEdges))
    (hmid : ∀ e ∈ hollowEdges,
      ∃ m, let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
      G.degree m = 2 ∧ G.Adj (p e.1) m ∧ G.Adj (p e.2) m) : False := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hside (x : (S : Set (Q 9))) : x.val 0 = b := (Finset.mem_filter.mp x.property).2
  obtain ⟨f, hf, hfinj⟩ := select_subdivision_vertices_of_paths G p hollowEdges edge_order hmid
  let m := f (0, 1)
  let n := f (0, 2)
  have hm : G.neighborFinset m = {p 0, p 1} := (hf (0, 1) (by decide)).2
  have hn : G.neighborFinset n = {p 0, p 2} := (hf (0, 2) (by decide)).2
  have hm0 : G.Adj (p 0) m := ((G.mem_neighborFinset m (p 0)).mp (by rw [hm]; simp)).symm
  have hn0 : G.Adj (p 0) n := ((G.mem_neighborFinset n (p 0)).mp (by rw [hn]; simp)).symm
  have hm1 : G.Adj m (p 1) := (G.mem_neighborFinset _ _).mp (by rw [hm]; simp)
  have hn2 : G.Adj n (p 2) := (G.mem_neighborFinset _ _).mp (by rw [hn]; simp)
  have hmn : m.val ≠ n.val := by
    intro he
    have hh := hfinj (by decide : (0, 1) ∈ hollowEdges) (by decide : (0, 2) ∈ hollowEdges)
      (Subtype.ext he)
    exact (by decide : ((0, 1) : Fin 10 × Fin 10) ≠ (0, 2)) hh
  have low_ne_high (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges) (i : Fin 10) :
      (f edge).val ≠ (p i).val := by
    intro heq
    have h := (hf edge he).1
    have h3 : G.degree (p i) = 3 := hhigh i
    rw [← SimpleGraph.ncard_neighborSet] at h h3
    rw [show f edge = p i from Subtype.ext heq] at h
    omega
  have hu_n : ¬ G.Adj (p 1) n := by
    intro h
    have ht := (G.mem_neighborFinset _ _).mpr h.symm
    rw [hn] at ht
    simpa [p.injective.eq_iff] using ht
  have hv_m : ¬ G.Adj (p 2) m := by
    intro h
    have ht := (G.mem_neighborFinset _ _).mpr h.symm
    rw [hm] at ht
    simpa [p.injective.eq_iff] using ht
  have plane (x : (S : Set (Q 9))) : x.val 0 = (p 0).val 0 :=
    (hside x).trans (hside (p 0)).symm
  obtain ⟨g, σ, sameAxis, hg, hplane0, hg0, hg1, hg2, hg7⟩ :=
    normalize_paired_paths (plane m) (plane n) (plane (p 1)) (plane (p 2)) (plane (p 7))
      hm0 hn0 ((hsolid 0 7 (by decide)).mpr (by decide)) hm1 hn2 hmn
      (low_ne_high (0, 1) (by decide) 7) (low_ne_high (0, 2) (by decide) 7)
      (fun h => p.injective.ne (by decide : (1 : Fin 10) ≠ 0) (Subtype.ext h))
      (fun h => p.injective.ne (by decide : (2 : Fin 10) ≠ 0) (Subtype.ext h))
      hu_n (fun h => (by decide : (1, 7) ∉ solidEdges) ((hsolid 1 7 (by decide)).mp h))
      hv_m (fun h => (by decide : (2, 7) ∉ solidEdges) ((hsolid 2 7 (by decide)).mp h))
  let e := cubeBitVec 9
  let norm (x : Q 9) : Vertex := e.symm (g x)
  have hnorm : Function.Injective norm := e.symm.injective.comp g.injective
  have hplane (x : (S : Set (Q 9))) : (norm x.val).getLsbD 0 = false := by
    change e (norm x.val) 0 = false
    rw [show e (norm x.val) = g x.val from e.apply_symm_apply _]
    exact (hplane0 x.val).mpr ((hside x).trans (hside (p 0)).symm)
  have hAdj (x y : (S : Set (Q 9))) :
      adjacent (norm x.val) (norm y.val) = true ↔ G.Adj x y := by
    rw [adjacent_iff]
    change (hypercube 9).Adj (e (e.symm (g x.val))) (e (e.symm (g y.val))) ↔
      (hypercube 9).Adj x.val y.val
    simp only [Equiv.apply_symm_apply]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := adjacent_exists_flip h
      have h' : y.val = flip x.val (σ.symm i) := g.injective (by
        rw [hi, hg, σ.apply_symm_apply])
      rw [h']
      exact flip_adj _ _
    · intro h
      obtain ⟨i, hi⟩ := adjacent_exists_flip h
      rw [hi, hg]
      exact flip_adj _ _
  let P (i : Fin 10) : Vertex := norm (p i).val
  let M (edge : Fin 10 × Fin 10) : Vertex := norm (f edge).val
  have hpinj : Function.Injective P := fun _ _ he => p.injective (Subtype.ext (hnorm he))
  have hAdjM (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges) (i : Fin 10) :
      adjacent (M edge) (P i) = true ↔ i = edge.1 ∨ i = edge.2 := by
    have heq := (hf edge he).2
    refine (hAdj (f edge) (p i)).trans ?_
    have hset := congrArg
      (fun t : Finset (S : Set (Q 9)) => (↑t : Set (S : Set (Q 9)))) heq
    simp only [SimpleGraph.coe_neighborFinset, Finset.coe_insert, Finset.coe_singleton] at hset
    change p i ∈ G.neighborSet (f edge) ↔ _
    rw [hset]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, p.injective.eq_iff]
  have hstep (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges) :
      P edge.2 ∈ moves (P edge.1) ∧ hasTwoSetBits (P edge.1 ^^^ P edge.2) = true := by
    have hx : adjacent (P edge.1) (M edge) = true := (hAdj _ _).mpr
      ((hAdj _ _).mp ((hAdjM edge he edge.1).mpr (Or.inl rfl))).symm
    exact two_step hx ((hAdjM edge he edge.2).mpr (Or.inr rfl))
      (hpinj.ne (edge_order edge he).ne)
  have hoptions (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges) :
      M edge ∈ middleOptions labels P edge.1 edge.2 := by
    have hxy : adjacent (P edge.1) (M edge) = true := (hAdj _ _).mpr
      ((hAdj _ _).mp ((hAdjM edge he edge.1).mpr (Or.inl rfl))).symm
    obtain ⟨d, hd⟩ := adjacency_to_toggle hxy
    have hd0 : d ≠ 0 := by
      intro hh
      subst d
      have hh := congrArg (fun w => cubeBitVec 9 w 0) hd
      have hp0 : e (P edge.1) 0 = false := hplane (p edge.1)
      have hm0 : e (M edge) 0 = false := hplane (f edge)
      change e (M edge) 0 = e (toggle (P edge.1) 0) 0 at hh
      rw [show e (toggle (P edge.1) 0) = flip (e (P edge.1)) 0
        from cubeBitVec_xor_single _ _, BalancedCriticalSpectrum.flip_apply_same, hp0, hm0] at hh
      contradiction
    obtain ⟨j, hj⟩ : ∃ j : Fin 8, d = j.succ := by
      refine Fin.cases ?_ (fun j _ => ⟨j, rfl⟩) d hd0
      exact fun h => (h rfl).elim
    unfold middleOptions
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr ⟨j, List.mem_finRange _, by rw [hd, hj]⟩, ?_⟩
    apply List.all_eq_true.mpr
    intro i _
    apply beq_iff_eq.mpr
    by_cases hh : i = edge.1 ∨ i = edge.2
    · rw [(hAdjM edge he i).mpr hh]
      rcases hh with rfl | rfl <;> simp
    · rw [Bool.eq_false_iff.mpr (fun h => hh ((hAdjM edge he i).mp h))]
      simp [(not_or.mp hh).1, (not_or.mp hh).2]
  have hvalid : valid labels P = true := by
    unfold valid
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    by_cases hij : i < j
    · have hadj : adjacent (P i) (P j) = solidEdges.contains (i, j) :=
        Bool.eq_iff_iff.mpr ((hAdj (p i) (p j)).trans
          ((hsolid i j hij).trans List.contains_iff_mem.symm))
      have hne := beq_eq_false_iff_ne.mpr (hpinj.ne hij.ne)
      simp only [hij, ite_true, bne, hne, Bool.not_false, hadj, beq_self_eq_true, Bool.true_and]
      by_cases hh : (i, j) ∈ hollowEdges
      · have ho := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨M (i, j), hoptions _ hh⟩
        simp [List.contains_iff_mem.mpr hh, (hstep _ hh).2, ho]
      · simp [hh]
    · simp [hij]
  have hroot : ∀ i ∈ ([0, 1, 2, 7] : List (Fin 10)), seed sameAxis i = P i := by
    have h0 : P 0 = 0 := e.injective ((e.apply_symm_apply _).trans hg0)
    have h1 : P 1 = 18 := e.injective ((e.apply_symm_apply _).trans hg1)
    have h2 : P 2 = (if sameAxis then 20 else 36) := e.injective ((e.apply_symm_apply _).trans hg2)
    have h7 : P 7 = 8 := e.injective ((e.apply_symm_apply _).trans hg7)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h7.symm
  have hstepOptions (s : Fin 10 × Fin 10 × Bool) (hs : s ∈ searchOrder) :
      P s.1 ∈ stepOptions (P s.2.1) s.2.2 := by
    have ht := search_edge s hs
    cases hsolid' : s.2.2
    · simp only [hsolid', Bool.false_eq_true, ite_false, stepOptions] at ht ⊢
      rcases ht with h | h
      · exact (hstep _ h).1
      · have ha : adjacent (P s.2.1) (M (s.1, s.2.1)) = true := (hAdj _ _).mpr
          ((hAdj _ _).mp ((hAdjM _ h s.2.1).mpr (Or.inr rfl))).symm
        exact (two_step ha ((hAdjM _ h s.1).mpr (Or.inl rfl))
          (hpinj.ne (edge_order _ h).ne.symm)).1
    · simp only [hsolid', ite_true, stepOptions] at ht ⊢
      have hord : ∀ k : Fin 10 × Fin 10, k ∈ solidEdges → k.1 < k.2 := by decide
      have ha := (hAdj _ _).mpr ((hsolid _ _ (hord _ ht)).mpr ht)
      obtain ⟨d, hd⟩ := adjacency_to_toggle ha
      have hd0 : d ≠ 0 := by
        intro h
        subst d
        have hh := congrArg (fun w => cubeBitVec 9 w 0) hd
        change e (P s.1) 0 = e (toggle (P s.2.1) 0) 0 at hh
        rw [show e (toggle (P s.2.1) 0) = flip (e (P s.2.1)) 0 from
          cubeBitVec_xor_single _ _, BalancedCriticalSpectrum.flip_apply_same] at hh
        have hu : e (P s.1) 0 = false := hplane (p s.1)
        have hv : e (P s.2.1) 0 = false := hplane (p s.2.1)
        rw [hu, hv] at hh
        contradiction
      obtain ⟨j, rfl⟩ : ∃ j : Fin 8, d = j.succ := by
        refine Fin.cases ?_ (fun j _ => ⟨j, rfl⟩) d hd0
        exact fun h => (h rfl).elim
      exact List.mem_map.mpr ⟨j, List.mem_finRange _, hd.symm⟩
  let es := hollowEdges
  have hpairs : (es.map M).Pairwise separated := by
    apply List.pairwise_map.mpr
    apply edge_sizes.1.imp_of_mem
    intro x y hx hy hxy
    constructor
    · intro he
      exact hxy (hfinj hx hy (Subtype.ext (hnorm he)))
    · apply Bool.eq_false_iff.mpr
      exact fun h => coordinate_slice_low_independent hr hb ((hAdj _ _).mp h)
        (hf x hx).1 (hf y hy).1
  let half := (es.map M).reverse ++ labels.map P
  have bad := normalized_placement_excess_degree sameAxis P hroot hvalid
    (fun i => hplane (p i)) (fun _ ht => hstepOptions _ ht) M hoptions hpairs
  have hn : half.Nodup := by
    have hmN : (es.map M).Nodup := hpairs.imp (fun h => h.1)
    apply List.nodup_append'.mpr
    refine ⟨List.nodup_reverse.mpr hmN, (List.nodup_finRange 10).map hpinj, ?_⟩
    intro x hx hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    obtain ⟨i, _, he⟩ := List.mem_map.mp hy
    have hv : p i = f t := Subtype.ext (hnorm he)
    have h : G.degree (p i) = 3 := hhigh i
    have hh := (hf t ht).1
    rw [← SimpleGraph.ncard_neighborSet] at h hh
    rw [hv] at h
    omega
  let T := C.image g
  have hS : coordinateSlice T false = S.image g := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hx0⟩ := Finset.mem_filter.mp hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨hy, ((hplane0 y).mp hx0).trans (hside (p 0))⟩, rfl⟩
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hy0⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩,
        (hplane0 y).mpr (hy0.trans (hside (p 0)).symm)⟩
  have hsT : (coordinateSlice T false).card = 22 := by
    rw [hS, Finset.card_image_of_injective _ g.injective]
    exact hs
  have hhalf : half.toFinset.map e.toEmbedding = coordinateSlice T false := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      rw [hS]
      have h : y ∈ half := List.mem_toFinset.mp hy
      rcases List.mem_append.mp h with h | h
      · obtain ⟨t, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
        exact Finset.mem_image.mpr ⟨(f t).val, (f t).property, e.apply_symm_apply _ |>.symm⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
        exact Finset.mem_image.mpr ⟨(p i).val, (p i).property, e.apply_symm_apply _ |>.symm⟩
    · rw [hsT, Finset.card_map, List.toFinset_card_of_nodup hn]
      simp [half, labels, es, edge_sizes.2]
  have hmap (x : Vertex) : x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice T false := by
    rw [← hhalf, Finset.mem_map]
    constructor
    · intro hx
      exact ⟨x, List.mem_toFinset.mpr hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have e' : y = x := e.injective he
      exact e' ▸ List.mem_toFinset.mp hy
  obtain ⟨hrT, hbT⟩ := cube_action_regular_balanced g σ hg hr hb
  exact no_extension_of_excess_degree hrT hbT half hn hmap bad

#print axioms no_paired_model

private abbrev SideLabel := Fin 2 ⊕ Fin 3
private abbrev HighLabel := SideLabel ⊕ SideLabel

private def pairedLabel : Fin 10 → HighLabel :=
  ![.inl (.inr 0), .inl (.inl 0), .inl (.inl 1), .inl (.inr 1), .inl (.inr 2),
    .inr (.inl 0), .inr (.inl 1), .inr (.inr 0), .inr (.inr 1), .inr (.inr 2)]

private def matched : HighLabel → HighLabel → Prop
  | .inl (.inr i), .inr (.inr j) => i = j
  | .inr (.inr j), .inl (.inr i) => i = j
  | _, _ => False

private def joined : SideLabel → SideLabel → Prop
  | .inl _, .inr _ | .inr _, .inl _ => True
  | _, _ => False

private def subdivided : HighLabel → HighLabel → Prop
  | .inl i, .inl j | .inr i, .inr j => joined i j
  | _, _ => False

private instance (a b : HighLabel) : Decidable (matched a b) := by
  cases a <;> cases b <;> rename_i a b <;> cases a <;> cases b <;>
    unfold matched <;> infer_instance

private instance (a b : SideLabel) : Decidable (joined a b) := by
  cases a <;> cases b <;> unfold joined <;> infer_instance

private instance (a b : HighLabel) : Decidable (subdivided a b) := by
  cases a <;> cases b <;> unfold subdivided <;> infer_instance

private theorem side_label_injective {V : Type*} [Fintype V] {G : SimpleGraph V} {L : Finset V}
    (u : Fin 2 ↪ SideHigh G L) (x : Fin 3 ↪ SideHigh G L)
    (hu : ∀ i, (compressed G L).degree (u i) = 3)
    (hx : ∀ j, (compressed G L).degree (x j) = 2) :
    Function.Injective (Sum.elim u x : SideLabel → SideHigh G L) := by
  rintro (i | i) (j | j) h
  · exact congrArg Sum.inl (u.injective h)
  · have he := congrArg (fun z : SideHigh G L => (compressed G L).degree z) h
    change (compressed G L).degree (u i) = (compressed G L).degree (x j) at he
    rw [hu, hx] at he
    contradiction
  · have he := congrArg (fun z : SideHigh G L => (compressed G L).degree z) h
    change (compressed G L).degree (x i) = (compressed G L).degree (u j) at he
    rw [hx, hu] at he
    contradiction
  · exact congrArg Sum.inr (x.injective h)

/-- A balanced cubic support of order 72 has no 22-vertex coordinate half. -/
theorem no_twenty_two_half {C : Finset (Q 9)} (hc : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22) : False := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  obtain ⟨side, ⟨left⟩, ⟨right⟩, _, _⟩ := paired_compression hc hr hb b hs
  let L := paritySide S side
  let R := paritySide S (!side)
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := by
    cases side
    · exact parity_bipartite S
    · exact (parity_bipartite S).symm
  have hg := BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
  obtain ⟨u, v, x, y, hu, hv, hx, hy, hl, hr', hm, hleft, hright⟩ :=
    paired_model_labels hp (fun z => coordinate_slice_degree_cases z.property hr)
      (fun ha h₂ h₂' => coordinate_slice_low_independent hr hb ha h₂ h₂') hg left right
  let l : SideLabel → SideHigh G L := Sum.elim u x
  let r : SideLabel → SideHigh G R := Sum.elim v y
  let vertex : HighLabel → (S : Set (Q 9)) :=
    Sum.elim (fun i => (l i).val) (fun i => (r i).val)
  have inL (i : SideLabel) : (l i).val ∈ (L : Set _) := (mem_filter.mp (l i).property).1
  have inR (i : SideLabel) : (r i).val ∈ (R : Set _) := (mem_filter.mp (r i).property).1
  have injective : Function.Injective vertex := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (side_label_injective u x hu hx (Subtype.ext h))
    · change (l i).val = (r j).val at h
      exact (Set.disjoint_left.mp hp.disjoint (inL i) (h.symm ▸ inR j)).elim
    · change (r i).val = (l j).val at h
      exact (Set.disjoint_left.mp hp.disjoint (inL j) (h ▸ inR i)).elim
    · exact congrArg Sum.inr (side_label_injective v y hv hy (Subtype.ext h))
  have high (a : HighLabel) : G.degree (vertex a) = 3 := by
    cases a with
    | inl i => exact (mem_filter.mp (l i).property).2
    | inr i => exact (mem_filter.mp (r i).property).2
  have cross (i j : SideLabel) : G.Adj (l i).val (r j).val ↔ matched (.inl i) (.inr j) := by
    cases i with
    | inl i => exact iff_false_intro (hleft i (r j))
    | inr i =>
      cases j with
      | inl j => exact iff_false_intro (hright j (l (.inr i)))
      | inr j => exact hm i j
  have solid (a b : HighLabel) : G.Adj (vertex a) (vertex b) ↔ matched a b := by
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        have noAdj : ¬ G.Adj (l i).val (l j).val := fun h =>
          Set.disjoint_left.mp hp.disjoint (inL j) (hp.mem_of_mem_adj (inL i) h)
        have noMatch : ¬ matched (.inl i) (.inl j) := by cases i <;> cases j <;> exact id
        exact iff_of_false noAdj noMatch
      | inr j => exact cross i j
    | inr i =>
      cases b with
      | inl j =>
        have h := cross j i
        cases i <;> cases j <;> exact ⟨fun ha => h.mp ha.symm, fun hm => (h.mpr hm).symm⟩
      | inr j =>
        have noAdj : ¬ G.Adj (r i).val (r j).val := fun h =>
          Set.disjoint_left.mp hp.disjoint (hp.symm.mem_of_mem_adj (inR i) h) (inR j)
        have noMatch : ¬ matched (.inr i) (.inr j) := by cases i <;> cases j <;> exact id
        exact iff_of_false noAdj noMatch
  have joined_edge {A : Finset (S : Set (Q 9))}
      (w : SideLabel → SideHigh G A)
      (hadj : ∀ i j, (compressed G A).Adj (w (.inl i)) (w (.inr j)))
      (i j : SideLabel) (h : joined i j) : (compressed G A).Adj (w i) (w j) := by
    cases i <;> cases j
    · exact h.elim
    · exact hadj _ _
    · exact (hadj _ _).symm
    · exact h.elim
  have middle (a b : HighLabel) (h : subdivided a b) :
      ∃ m, G.degree m = 2 ∧ G.Adj (vertex a) m ∧ G.Adj (vertex b) m := by
    cases a <;> cases b
    · exact (joined_edge l hl _ _ h).2
    · exact h.elim
    · exact h.elim
    · exact (joined_edge r hr' _ _ h).2
  have injectiveLabel : Function.Injective pairedLabel := by
    change ∀ i j : Fin 10, pairedLabel i = pairedLabel j → i = j
    decide
  let p : Fin 10 ↪ (S : Set (Q 9)) := ⟨vertex ∘ pairedLabel, injective.comp injectiveLabel⟩
  have solidTable : ∀ i j : Fin 10, i < j →
      (matched (pairedLabel i) (pairedLabel j) ↔ (i, j) ∈ solidEdges) := by decide
  have middleTable : ∀ e : Fin 10 × Fin 10, e ∈ hollowEdges →
      subdivided (pairedLabel e.1) (pairedLabel e.2) := by decide
  exact no_paired_model hr hb b hs p (fun i => high (pairedLabel i))
    (fun i j hij => (solid _ _).trans (solidTable i j hij))
    (fun e he => middle _ _ (middleTable e he))

#print axioms no_twenty_two_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExclusion

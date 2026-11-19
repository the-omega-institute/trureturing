/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoSingletonExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TwentyTwoSingletonExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Exclude both singleton compressions by the size of the reconstructed slice. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoAxes
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry

/-! Exclude the singleton-parity case by normalizing its actual cubical
embedding and using unsigned opposite-half reconstruction. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonExclusion

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyTwoSingletonCoverage (high_candidate_of_normalized candidate_of_normalized)
open Q9TwentyTwoSingletonLabels (select_subdivision_vertices singleton_model)
open Q9TwentyTwoAxes (normalize_root_and_first_point)
open Q9TwentyTwoReconstruction (no_listed_singleton_half)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open Q9TwentyTwoCompression (half_compression)
open private coordinate_slice_low_independent coordinate_slice_degree_cases balanced_subset
  paritySide parity_bipartite from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open HuangBalancedSymmetry (cube_action_regular_balanced)
open private adjacent adjacent_iff hasTwoSetBits hasTwoSetBits_of_two_toggles
  moves toggle two_toggles_mem_moves from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
open private attachment solid hollow labels hollowEdges middleOptions valid root firstPointAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonPlacements
open private cycleIndex separated from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonCoverage
open private mem_hollowEdges rootIndex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonLabels
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

local notation "flip" => BalancedCriticalSpectrum.flip
private abbrev Vertex := BitVec 9

private theorem middle_edge (opposite : Bool) (i : Fin 6) :
    (attachment opposite i, cycleIndex i) ∈ hollowEdges opposite := by
  revert opposite i
  decide

private theorem edge_sizes (opposite : Bool) :
    (hollowEdges opposite).Nodup ∧ (hollowEdges opposite).length = 12 := by
  cases opposite <;> decide

private theorem adjacency_to_toggle {x y : Vertex}
    (h : adjacent x y = true) : ∃ d : Fin 9, y = toggle x d := by
  obtain ⟨d, hd⟩ := adjacent_exists_flip ((adjacent_iff x y).mp h)
  exact ⟨d, (cubeBitVec 9).injective (hd.trans (cubeBitVec_xor_single x d).symm)⟩

private theorem two_step {x y m : Vertex}
    (hx : adjacent x m = true) (hy : adjacent m y = true) (hne : x ≠ y) :
    y ∈ moves x ∧ hasTwoSetBits (x ^^^ y) = true := by
  obtain ⟨a, ha⟩ := adjacency_to_toggle hx
  obtain ⟨b, hb⟩ := adjacency_to_toggle hy
  have hy' : y = toggle (toggle x a) b := hb.trans (congrArg (fun z => toggle z b) ha)
  have hab : a ≠ b := by
    intro h
    subst b
    exact hne (by simpa [toggle, BitVec.xor_assoc] using hy'.symm)
  constructor
  · rw [hy']
    exact two_toggles_mem_moves _ _ _ hab
  · rw [hy', show x ^^^ toggle (toggle x a) b = toggle (toggle 0 a) b by
        simp [toggle, ← BitVec.xor_assoc]]
    exact hasTwoSetBits_of_two_toggles _ _ hab

attribute [local instance] Classical.propDecidable

/-- Neither singleton-parity model can occur in a 22-point half of an
order-72 Huang-balanced cubic support. -/
theorem no_singleton_model {C : Finset (Q 9)} (hc : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22)
    (opposite : Bool) (p : Fin 10 ↪ (coordinateSlice C b : Set (Q 9)))
    (hhigh : ∀ i, ((hypercube 9).induce (coordinateSlice C b : Set (Q 9))).degree (p i) = 3)
    (hsolid : ∀ i j,
      ((hypercube 9).induce (coordinateSlice C b : Set (Q 9))).Adj (p i) (p j) ↔ solid i j = true)
    (hmid : ∀ i j, hollow opposite i j = true →
      ∃ m, let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
      G.degree m = 2 ∧ G.Adj (p i) m ∧ G.Adj (p j) m) : False := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let o := (p 0).val
  have hside (x : (S : Set (Q 9))) : x.val 0 = b := (Finset.mem_filter.mp x.property).2
  have hstar (j : Fin 3) : (hypercube 9).Adj o (p (rootIndex j)).val :=
    (hsolid 0 (rootIndex j)).mpr ((show ∀ i : Fin 3, solid 0 (rootIndex i) = true by decide) j)
  choose first hfirst using fun j => adjacent_exists_flip (hstar j)
  have hfirstInj : Function.Injective first := by
    intro j k he
    have hh : p (rootIndex j) = p (rootIndex k) :=
      Subtype.ext ((hfirst j).trans (he ▸ hfirst k).symm)
    have h := congrArg Fin.val (p.injective hh)
    change j.val + 1 = k.val + 1 at h
    exact Fin.ext (by omega)
  have hfirst0 (i : Fin 3) : first i ≠ 0 := by
    intro h
    have he := congrFun (hfirst i) 0
    rw [h, BalancedCriticalSpectrum.flip_apply_same, hside (p (rootIndex i)),
      show o 0 = b from hside (p 0)] at he
    cases b <;> contradiction
  let first' : Fin 3 ↪ Fin 9 := ⟨first, hfirstInj⟩
  have hlink : hollow opposite (rootIndex 0) (cycleIndex 0) = true := by
    cases opposite <;> decide
  obtain ⟨m, _, hm1, hm2⟩ := hmid _ _ hlink
  obtain ⟨u, hu⟩ := adjacent_exists_flip hm1
  obtain ⟨v, hv⟩ := adjacent_exists_flip hm2.symm
  have hpoint : (p (cycleIndex 0)).val = flip (flip (flip o (first 0)) u) v := by
    change m.val = flip (p (rootIndex 0)).val u at hu
    change (p (cycleIndex 0)).val = flip m.val v at hv
    rw [hv, hu, hfirst 0]
  obtain ⟨g, σ, hg, hplane0, hg0, hgstar, hgpoint⟩ :=
    normalize_root_and_first_point o first' hfirst0 u v
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
  obtain ⟨f, hf, hfinj⟩ := select_subdivision_vertices G opposite p hmid
  let P (i : Fin 10) : Vertex := norm (p i).val
  let M (edge : Fin 10 × Fin 10) : Vertex := norm (f edge).val
  have hpinj : Function.Injective P := fun _ _ he => p.injective (Subtype.ext (hnorm he))
  have hAdjM (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges opposite) (i : Fin 10) :
      adjacent (M edge) (P i) = true ↔ i = edge.1 ∨ i = edge.2 := by
    have heq := (hf edge he).2
    refine (hAdj (f edge) (p i)).trans ?_
    have hset := congrArg
      (fun t : Finset (S : Set (Q 9)) => (↑t : Set (S : Set (Q 9)))) heq
    simp only [SimpleGraph.coe_neighborFinset, Finset.coe_insert, Finset.coe_singleton] at hset
    change p i ∈ G.neighborSet (f edge) ↔ _
    rw [hset]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, p.injective.eq_iff]
  have hstep (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges opposite) :
      P edge.2 ∈ moves (P edge.1) ∧ hasTwoSetBits (P edge.1 ^^^ P edge.2) = true := by
    have hx : adjacent (P edge.1) (M edge) = true := (hAdj _ _).mpr
      ((hAdj _ _).mp ((hAdjM edge he edge.1).mpr (Or.inl rfl))).symm
    exact two_step hx ((hAdjM edge he edge.2).mpr (Or.inr rfl))
      (hpinj.ne ((mem_hollowEdges opposite edge).mp he).1.ne)
  have hoptions (edge : Fin 10 × Fin 10) (he : edge ∈ hollowEdges opposite) :
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
  have hvalid : valid opposite labels P = true := by
    unfold valid
    apply List.all_eq_true.mpr
    intro i _
    apply List.all_eq_true.mpr
    intro j _
    by_cases hij : i < j
    · have hadj : adjacent (P i) (P j) = solid i j :=
        Bool.eq_iff_iff.mpr ((hAdj (p i) (p j)).trans (hsolid i j))
      have hne := beq_eq_false_iff_ne.mpr (hpinj.ne hij.ne)
      simp only [hij, ite_true, bne, hne, Bool.not_false, hadj, beq_self_eq_true, Bool.true_and]
      by_cases hh : hollow opposite i j = true
      · have he := (mem_hollowEdges opposite (i, j)).mpr ⟨hij, hh⟩
        have ho := List.isEmpty_eq_false_iff_exists_mem.mpr ⟨M (i, j), hoptions _ he⟩
        simp [hh, (hstep _ he).2, ho]
      · simp [Bool.eq_false_iff.mpr hh]
    · simp [hij]
  have hroot : ∀ i ∈ ([0, 1, 2, 3] : List (Fin 10)), root i = P i := by
    have h0 : P 0 = 0 := e.injective ((e.apply_symm_apply _).trans hg0)
    have hstar' (i : Fin 3) :
        P (rootIndex i) = BitVec.ofNat 9 (2 ^ (i.val + 1)) := e.injective (by
      change e (e.symm (g (p (rootIndex i)).val)) = _
      rw [e.apply_symm_apply, hfirst i]
      exact hgstar i)
    have hmult : ∀ i ∈ ([0, 1, 2, 3] : List (Fin 10)),
        i = 0 ∨ ∃ j : Fin 3, i = rootIndex j := by decide
    have htable : ∀ j : Fin 3, root (rootIndex j) = BitVec.ofNat 9 (2 ^ (j.val + 1)) := by decide
    intro i hi
    rcases hmult i hi with rfl | ⟨j, rfl⟩
    · exact h0.symm
    · exact (htable j).trans (hstar' j).symm
  have hP := high_candidate_of_normalized opposite P hroot hvalid (fun i => hplane (p _))
    (by
      change firstPointAxes (norm (p (cycleIndex 0)).val) = true
      rw [hpoint]
      exact hgpoint)
    (fun i => (hstep _ (middle_edge opposite i)).1)
  let es := hollowEdges opposite
  have hpairs : (es.map M).Pairwise separated := by
    apply List.pairwise_map.mpr
    apply (edge_sizes opposite).1.imp_of_mem
    intro x y hx hy hxy
    constructor
    · intro he
      exact hxy (hfinj hx hy (Subtype.ext (hnorm he)))
    · apply Bool.eq_false_iff.mpr
      exact fun h => coordinate_slice_low_independent hr hb ((hAdj _ _).mp h)
        (hf x hx).1 (hf y hy).1
  let half := (es.map M).reverse ++ labels.map P
  have hmem := candidate_of_normalized opposite P hP M hoptions hpairs
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
      simp [half, labels, es, (edge_sizes opposite).2]
  have hmap (x : Vertex) : x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice T false := by
    rw [← hhalf, Finset.mem_map]
    constructor
    · intro hx
      exact ⟨x, List.mem_toFinset.mpr hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      have e' : y = x := e.injective he
      exact e' ▸ List.mem_toFinset.mp hy
  have hTcard : T.card = 72 := (Finset.card_image_of_injective _ g.injective).trans hc
  obtain ⟨hrT, hbT⟩ := cube_action_regular_balanced g σ hg hr hb
  exact no_listed_singleton_half hTcard hsT hrT hbT half hn hmap hmem

#print axioms no_singleton_model

/-- Both parity classes in a 22-point half compress to the complete
bipartite graph on parts of orders two and three. -/
theorem paired_compression {C : Finset (Q 9)} (hc : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    ∃ side : Bool,
      let L := paritySide S side
      let R := paritySide S (!side)
      Nonempty (compressed G L ≃g SimpleGraph.turanGraph 5 2) ∧
      Nonempty (compressed G R ≃g SimpleGraph.turanGraph 5 2) ∧
      (∀ x : SideHigh G L, (compressed G L).degree x = 2 ↔
        ∃! y : SideHigh G R, G.Adj x.val y.val) ∧
      (∀ y : SideHigh G R, (compressed G R).degree y = 2 ↔
        ∃! x : SideHigh G L, G.Adj y.val x.val) := by
  obtain ⟨side, h | h⟩ := half_compression hc hr hb b hs
  · let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    let L := paritySide S side
    let R := paritySide S (!side)
    obtain ⟨hL, r, hA, _, _, e, _, _, _, _⟩ := h
    let A := Finset.univ.filter (fun x : SideHigh G R => G.Adj r.val x.val)
    let B := Finset.univ \ A
    have hB : B.card = 6 := by
      have h := Nat.card_congr e.toEquiv
      have he : Nat.card (B : Set (SideHigh G R)) = B.card :=
        Nat.card_eq_fintype_card.trans (Fintype.card_coe B)
      change Nat.card (Fin 6) = Nat.card (B : Set (SideHigh G R)) at h
      rw [Nat.card_fin, he] at h
      exact h.symm
    have hR : Fintype.card (SideHigh G R) = 9 := by
      have ht := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
      rw [Finset.card_univ] at ht
      change B.card + A.card = _ at ht
      change A.card = 3 at hA
      omega
    have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := by
      cases side
      · exact parity_bipartite S
      · exact (parity_bipartite S).symm
    have hdeg (x : (S : Set (Q 9))) : G.degree x = 2 ∨ G.degree x = 3 :=
      coordinate_slice_degree_cases x.property hr
    have hg := BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
    obtain ⟨opposite, p, hhigh, hsolid, hmid⟩ := singleton_model hp hdeg
      (fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy) hg hL hR
    exact (no_singleton_model hc hr hb b hs opposite p hhigh hsolid hmid).elim
  · exact ⟨side, h⟩

#print axioms paired_compression

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoSingletonExclusion

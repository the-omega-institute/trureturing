import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9EightCubicGraphCertificate
import Batteries.Tactic.OpenPrivate

/-! Degree separation in a twenty-vertex literal half of a balanced cubic
support of order seventy-two. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice

attribute [local instance] Classical.propDecidable

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count flip)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  parts_card balanced_subset from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private highWithHigh high_neighbor_deficit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

/-- A twenty-vertex half has twelve cut endpoints and eight cubic vertices.
Every edge joins different degree classes, so suppressing the degree-two
vertices uses every edge of the half. -/
theorem degree_classes {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
    (degreeTwo G Finset.univ).card = 12 ∧ (degreeThree G Finset.univ).card = 8 ∧
      ∀ {v w}, G.Adj v w →
        (G.degree v = 2 ∧ G.degree w = 3) ∨ (G.degree v = 3 ∧ G.degree w = 2) := by
  classical
  let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False :=
    fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy
  have hcut : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hlo : (degreeTwo G Finset.univ).card = 12 := by
    calc
      _ = directionEdges C 0 := low_slice_card_eq_q hr
      _ = 12 := by omega
  have htotal := parts_card G hdeg Finset.univ
  have hsize : Fintype.card (coordinateSlice C b : Set (Q 9)) = 20 := by
    simpa using hs
  rw [Finset.card_univ, hsize, hlo] at htotal
  have hhi : (degreeThree G Finset.univ).card = 8 := by omega
  have hdeficit := high_neighbor_deficit G hdeg hlow
  rw [hlo, hhi] at hdeficit
  have hnone : highWithHigh G = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨hlo, hhi, ?_⟩
  intro v w hAdj
  rcases hdeg v with hv | hv <;> rcases hdeg w with hw | hw
  · exact (hlow hAdj hv hw).elim
  · exact Or.inl ⟨hv, hw⟩
  · exact Or.inr ⟨hv, hw⟩
  · have hmem : v ∈ highWithHigh G :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, w, hAdj, hw⟩
    simp [hnone] at hmem

#print axioms degree_classes

/-- Suppressing the twelve degree-two vertices yields a triangle-free cubic
graph on eight vertices, with every compressed edge realized in the half. -/
theorem compressed_cubic {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
    ∃ (H : SimpleGraph (Fin 8)) (vertices : Fin 8 ↪ (coordinateSlice C b : Set (Q 9))),
      H.IsRegularOfDegree 3 ∧
      (∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) ∧
      ∀ x y, H.Adj x y ↔ x ≠ y ∧
        ∃ m, G.degree m = 2 ∧ G.Adj (vertices x) m ∧ G.Adj (vertices y) m := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := degreeThree G Finset.univ
  let R := degreeTwo G Finset.univ
  obtain ⟨_, hhi, hsplit⟩ := degree_classes hC hr hb b hs
  change ∀ {v w : (S : Set (Q 9))}, G.Adj v w →
    (G.degree v = 2 ∧ G.degree w = 3) ∨ (G.degree v = 3 ∧ G.degree w = 2) at hsplit
  have hpart : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have h3 := (Finset.mem_filter.mp (show x ∈ L from hx)).2
      have h2 := (Finset.mem_filter.mp (show x ∈ R from hy)).2
      omega
    · intro x y hxy
      rcases hsplit hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False :=
    fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy
  have hg : (8 : ℕ∞) ≤ G.egirth :=
    BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (Finset.filter_subset _ _))
  have hL : degreeThree G L = L := by
    ext v
    simp [L, degreeThree]
  have hcard : Fintype.card (SideHigh G L) = 8 := by
    change Fintype.card ↥(degreeThree G L) = 8
    rw [Fintype.card_coe, hL]
    exact hhi
  let label := (Fintype.equivFinOfCardEq hcard).symm
  let H := (compressed G L).comap label
  let vertices := label.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨H, vertices, ?_, ?_, ?_⟩
  · intro i
    have hdegree : (compressed G L).degree (label i) +
        (degreeThree G (G.neighborFinset (label i).val)).card = 3 :=
      compressed_degree hpart hdeg hlow hg (label i)
    have hnone : degreeThree G (G.neighborFinset (label i).val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨ha, hv3⟩ := Finset.mem_filter.mp hv
      have hi3 : G.degree (label i).val = 3 := (Finset.mem_filter.mp (label i).property).2
      rcases hsplit ((G.mem_neighborFinset _ _).mp ha) with ⟨h2, _⟩ | ⟨_, h2⟩
      · exact (by decide : (2 : ℕ) ≠ 3) (h2.symm.trans hi3)
      · exact (by decide : (2 : ℕ) ≠ 3) (h2.symm.trans hv3)
    rw [hnone, Finset.card_empty, Nat.add_zero] at hdegree
    exact ((SimpleGraph.Iso.comap label (compressed G L)).degree_eq i).symm.trans hdegree
  · intro x y z
    exact compressed_triangle_free hpart hg (label x) (label y) (label z)
  · intro x y
    change (label x ≠ label y ∧ _) ↔ x ≠ y ∧ _
    rw [label.injective.ne_iff]
    rfl

#print axioms compressed_cubic

/-- The actual degree-two subdivision in a twenty-point half compresses to
the three-cube or Wagner graph. -/
theorem compressed_cube_or_wagner {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
    ∃ (wagner : Bool) (vertices : Fin 8 ↪ (coordinateSlice C b : Set (Q 9))),
      ∀ x y, Q9EightCubicGraphCertificate.modelAdj wagner x y = true ↔
        x ≠ y ∧ ∃ m, G.degree m = 2 ∧ G.Adj (vertices x) m ∧ G.Adj (vertices y) m := by
  obtain ⟨H, vertices, hreg, htriangle, hrealize⟩ := compressed_cubic hC hr hb b hs
  obtain ⟨wagner, label, hlabel⟩ :=
    Q9EightCubicGraphCertificate.cube_or_wagner H hreg htriangle
  refine ⟨wagner, label.symm.toEmbedding.trans vertices, fun x y => ?_⟩
  have h := (hlabel (label.symm x) (label.symm y)).symm.trans
    (hrealize (label.symm x) (label.symm y))
  simpa only [Equiv.apply_symm_apply, label.symm.injective.ne_iff,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using h

#print axioms compressed_cube_or_wagner

/-- The neighbors of vertex zero in the two compressed graph models. -/
def modelRootNeighbors (wagner : Bool) : Fin 3 → Fin 8 :=
  if wagner then ![1, 4, 7] else ![1, 2, 4]

/-- In either model, the three two-edge paths out of the root use distinct
first axes. Each second axis lies outside the first three axes. No axis is
the coordinate defining the half. -/
theorem compressed_root_axes {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let S := coordinateSlice C b
    let G := (hypercube 9).induce (S : Set (Q 9))
    ∃ (wagner : Bool) (vertices : Fin 8 ↪ (S : Set (Q 9)))
      (first : Fin 3 ↪ Fin 9) (second : Fin 3 → Fin 9),
      (∀ x y, Q9EightCubicGraphCertificate.modelAdj wagner x y = true ↔
        x ≠ y ∧ ∃ m, G.degree m = 2 ∧ G.Adj (vertices x) m ∧ G.Adj (vertices y) m) ∧
      (∀ a, ((vertices (modelRootNeighbors wagner a)).val : Q 9) =
        flip (flip (vertices 0).val (first a)) (second a)) ∧
      (∀ a, first a ≠ 0 ∧ second a ≠ 0) ∧
      ∀ a d, second a ≠ first d := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  obtain ⟨wagner, vertices, hrealize⟩ := compressed_cube_or_wagner hC hr hb b hs
  let leaf := modelRootNeighbors wagner
  have hleaf : Function.Injective leaf := by
    cases wagner <;> decide
  have hmodel (a : Fin 3) :
      Q9EightCubicGraphCertificate.modelAdj wagner 0 (leaf a) = true := by
    cases wagner <;> fin_cases a <;> decide
  have hpaths (a : Fin 3) := (hrealize 0 (leaf a)).mp (hmodel a)
  choose middle hmid hroot hleafAdj using fun a => (hpaths a).2
  have hmiddle_inj : Function.Injective middle := by
    intro a d had
    by_contra hne
    have h0a := vertices.injective.ne ((hpaths a).1)
    have h0d := vertices.injective.ne ((hpaths d).1)
    have had' := vertices.injective.ne (hleaf.ne hne)
    have hsubset : ({vertices 0, vertices (leaf a), vertices (leaf d)} :
        Finset (S : Set (Q 9))) ⊆ G.neighborFinset (middle a) := by
      intro v hv
      apply (G.mem_neighborFinset _ _).mpr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact (hroot a).symm
      · exact (hleafAdj a).symm
      · rw [had]
        exact (hleafAdj d).symm
    have hcount := Finset.card_le_card hsubset
    have hdeg : G.degree (middle a) = 2 := hmid a
    simp [G.card_neighborFinset_eq_degree, hdeg, h0a, h0d, had'] at hcount
  choose first hfirst using fun a => adjacent_exists_flip
    (show (hypercube 9).Adj (vertices 0).val (middle a).val from hroot a)
  choose second hsecond using fun a => adjacent_exists_flip
    (show (hypercube 9).Adj (middle a).val (vertices (leaf a)).val from (hleafAdj a).symm)
  have hfirst_inj : Function.Injective first := by
    intro a d had
    apply hmiddle_inj
    apply Subtype.ext
    rw [hfirst a, hfirst d, had]
  have hflip (x y : (S : Set (Q 9))) (i : Fin 9) (h : y.val = flip x.val i) : i ≠ 0 := by
    intro hi
    subst i
    have hx := (Finset.mem_filter.mp x.property).2
    have hy := (Finset.mem_filter.mp y.property).2
    have hzero := congrFun h (0 : Fin 9)
    rw [BalancedCriticalSpectrum.flip_apply_same, hx, hy] at hzero
    cases b <;> contradiction
  refine ⟨wagner, vertices, ⟨first, hfirst_inj⟩, second, hrealize, ?_, ?_, ?_⟩
  · intro a
    change (vertices (leaf a)).val = flip (flip (vertices 0).val (first a)) (second a)
    rw [hsecond a, hfirst a]
  · intro a
    exact ⟨hflip _ _ _ (hfirst a), hflip _ _ _ (hsecond a)⟩
  · intro a d had
    change second a = first d at had
    have hlast := (hsecond a).trans
      (congrArg (fun x => BalancedCriticalSpectrum.flip x (second a)) (hfirst a))
    rw [had] at hlast
    have hne : first a ≠ first d := by
      intro heq
      rw [← heq, BalancedCriticalSpectrum.flip_flip] at hlast
      exact (hpaths a).1 (vertices.injective (Subtype.ext hlast.symm))
    have hm (v : (S : Set (Q 9))) : v.val ∈ C :=
      (Finset.mem_filter.mp v.property).1
    exact BalancedCubeGirth.no_selected_square hb hne
      (hm (vertices 0)) (hfirst a ▸ hm (middle a)) (hfirst d ▸ hm (middle d))
      (hlast ▸ hm (vertices (leaf a)))

#print axioms compressed_root_axes

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice

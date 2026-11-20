/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipExtensionBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipExtensionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod]
   utility: none
   digest: Three-flip translates of balanced cubic components bound subcubic extensions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipSpectralLayers
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipProjectedParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q6EvenResidualNeighborhood

/-! Pack the occupied and residual fibres of a subcubic extension in the split nine-cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipExtensionBound

open scoped Classical
open BalancedCriticalSpectrum (Q IsBalanced flip flip_adj)
open Hypercube (hypercube)
open Q9ThreeFlipSpectralLayers
open private split vertex_flip_left vertex_flip_right translate_adj antipode_antipode
  pattern_edge_degree from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipSpectralLayers
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

local notation "productCube" => (SimpleGraph.boxProd (hypercube 3) (hypercube 6))

private def inProduct (e : Coordinates) (X : Finset (Q 9)) : Finset (Q 3 × Q 6) :=
  X.map (split e).toEmbedding

@[simp] private theorem mem_inProduct (e : Coordinates) (X : Finset (Q 9))
    (v : Q 3 × Q 6) : v ∈ inProduct e X ↔ vertex e v.1 v.2 ∈ X :=
  Finset.mem_map_equiv

private theorem vertex_adj_iff (e : Coordinates) (v w : Q 3 × Q 6) :
    (hypercube 9).Adj (vertex e v.1 v.2) (vertex e w.1 w.2) ↔ (productCube).Adj v w := by
  obtain ⟨p, y⟩ := v
  obtain ⟨q, z⟩ := w
  constructor
  · intro h
    obtain ⟨k, hk⟩ := adjacent_exists_flip h
    obtain ⟨i | j, rfl⟩ := e.surjective k
    · rw [← vertex_flip_left] at hk
      have he : (q, z) = (flip p i, y) := (split e).symm.injective hk
      cases he
      exact SimpleGraph.boxProd_adj_left.mpr (flip_adj p i)
    · rw [← vertex_flip_right] at hk
      have he : (q, z) = (p, flip y j) := (split e).symm.injective hk
      cases he
      exact SimpleGraph.boxProd_adj_right.mpr (flip_adj y j)
  · intro h
    change (hypercube 3).Adj p q ∧ y = z ∨ (hypercube 6).Adj y z ∧ p = q at h
    rcases h with ⟨hpq, rfl⟩ | ⟨hyz, rfl⟩
    · obtain ⟨i, rfl⟩ := adjacent_exists_flip hpq
      rw [vertex_flip_left]
      exact flip_adj _ _
    · obtain ⟨j, rfl⟩ := adjacent_exists_flip hyz
      rw [vertex_flip_right]
      exact flip_adj _ _

private theorem product_neighbor_card (e : Coordinates) (C : Finset (Q 9))
    (v : Q 3 × Q 6) :
    ((productCube).neighborFinset v ∩ inProduct e C).card =
      ((hypercube 9).neighborFinset (vertex e v.1 v.2) ∩ C).card := by
  have he : (productCube).neighborFinset v ∩ inProduct e C =
      inProduct e ((hypercube 9).neighborFinset (vertex e v.1 v.2) ∩ C) := by
    ext w
    simp only [Finset.mem_inter, mem_inProduct, SimpleGraph.mem_neighborFinset, vertex_adj_iff]
  rw [he, inProduct, Finset.card_map]

private theorem product_parity (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : Q9ThreeFlipProjectedParity.UnsignedAdjacencyParity (inProduct e C) := by
  intro v
  let x := vertex e v.1 v.2
  change (((productCube).neighborFinset v ∩ inProduct e C).card : ZMod 2) =
    if v ∈ inProduct e C then 1 else 0
  rw [product_neighbor_card]
  by_cases hx : x ∈ C
  · rw [ite_eq_left ((mem_inProduct e C v).mpr hx), selected_neighbor_card hx, hr.degree_eq] <;> decide
  · have hv : v ∉ inProduct e C := fun hv => hx ((mem_inProduct e C v).mp hv)
    rw [ite_eq_right hv, ZMod.natCast_eq_zero_iff_even]
    have he : C.filter ((hypercube 9).Adj x) = (hypercube 9).neighborFinset x ∩ C := by
      ext y
      simp [and_comm]
    rw [← he, ← directions_card]
    exact BalancedCubeComponentBoundary.exterior_even C hr hb x hx

private theorem closed_of_regular (U C : Finset (Q 9)) (hCU : C ⊆ U)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hCdeg : ∀ x ∈ C, ((hypercube 9).neighborFinset x ∩ C).card = 3) :
    ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C := by
  intro x hx y hy hxy
  let N := (hypercube 9).neighborFinset x
  have hsub : N ∩ C ⊆ N ∩ U := Finset.inter_subset_inter Finset.Subset.rfl hCU
  have hle : (N ∩ U).card ≤ (N ∩ C).card := by
    rw [hCdeg x hx, selected_neighbor_card (hCU hx)]
    exact hdeg ⟨x, hCU hx⟩
  have he := Finset.eq_of_subset_of_card_le hsub hle
  have hy' : y ∈ N ∩ U :=
    Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hxy, hy⟩
  rw [← he] at hy'
  exact (Finset.mem_inter.mp hy').2

private theorem separated_of_translate_subset (e : Coordinates) (U C : Finset (Q 9))
    (htranslate : ∀ x ∈ C, translate e x ∈ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hC : C.Nonempty) (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y) := by
  obtain ⟨a, ha, hta⟩ := exists_translate_not_mem e C hC hc hr hb
  have hdisj (y : (C : Set (Q 9))) : translate e y.1 ∉ C := by
    obtain ⟨walk⟩ := hc.preconnected y ⟨a, ha⟩
    have hwalk {s t : (C : Set (Q 9))}
        (path : ((hypercube 9).induce (C : Set (Q 9))).Walk s t) :
        translate e s.1 ∈ C → translate e t.1 ∈ C := by
      induction path with
      | nil => exact id
      | @cons s b t hsb _ ih =>
        intro hs
        exact ih (hclosed _ hs _ (htranslate _ b.2) (translate_adj e hsb))
    exact fun hy => hta (hwalk walk hy)
  intro x hx y hy
  exact ⟨fun he => hdisj ⟨y, hy⟩ (he ▸ hx),
    fun hadj => hdisj ⟨y, hy⟩ (hclosed _ hx _ (htranslate _ hy) hadj)⟩

-- The four labels in an occupied fibre are its edge and the antipodal edge.
private def edgeAndAntipodes (p : Q 3) (i : Fin 3) : Finset (Q 3) :=
  {p, flip p i} ∪ {antipode p, antipode (flip p i)}

set_option maxRecDepth 4096 in
private theorem edgeAndAntipodes_card :
    ∀ (p : Q 3) (i : Fin 3), (edgeAndAntipodes p i).card = 4 := by decide

private theorem outside_edgeAndAntipodes {p q : Q 3} {i : Fin 3}
    (hq : q ∉ edgeAndAntipodes p i) :
    ∃ r ∈ ({p, flip p i} : Finset (Q 3)), (hypercube 3).Adj r q := by
  have hanti : ¬ (q = antipode p ∨ q = antipode (flip p i)) := by
    intro h
    exact hq (Finset.mem_union_right _ (by simpa using h))
  have h := pattern_edge_degree p q i
  rw [ite_eq_right hanti] at h
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (h.symm ▸ Nat.zero_lt_one)
  exact ⟨flip q j, by simpa using (Finset.mem_filter.mp hj).2, (flip_adj q j).symm⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Evaluate the two parity classes of the 64 fixed-coordinate vertices.
private theorem paritySide_univ_card :
    ∀ b : Bool, (paritySide (Finset.univ : Finset (Q 6)) b).card = 32 := by decide

/-- A subcubic nine-cube extension containing a nonempty connected balanced cubic
induced subgraph and its three-flip translate has at most 256 vertices. -/
theorem card_le_256_of_three_flip_translate (e : Coordinates) (U C : Finset (Q 9))
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hCU : C ⊆ U) (hC : C.Nonempty) (hconn : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hbal : IsBalanced C) (htranslate : ∀ x ∈ C, translate e x ∈ U) : U.card ≤ 256 := by
  have hCdeg (x : Q 9) (hx : x ∈ C) :
      ((hypercube 9).neighborFinset x ∩ C).card = 3 :=
    (selected_neighbor_card hx).trans (hreg.degree_eq ⟨x, hx⟩)
  have hclosed := closed_of_regular U C hCU hdeg hCdeg
  have hsep := separated_of_translate_subset e U C htranslate hclosed hC hconn hreg hbal
  -- Translation preserves the three internal neighbors, so its image is closed as well.
  let t : Q 9 ≃ Q 9 :=
    (show Function.Involutive (translate e) from translate_involutive e).toPerm (translate e)
  let D := C.map t.toEmbedding
  have hDmem (x : Q 9) : x ∈ D ↔ translate e x ∈ C := Finset.mem_map_equiv
  have hDU : D ⊆ U := by
    intro x hx
    simpa using htranslate _ ((hDmem x).mp hx)
  have hDdeg (x : Q 9) (hx : x ∈ D) :
      ((hypercube 9).neighborFinset x ∩ D).card = 3 := by
    have hmap : ((hypercube 9).neighborFinset x ∩ D) =
        (((hypercube 9).neighborFinset (translate e x)) ∩ C).map t.toEmbedding := by
      ext y
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, hDmem, Finset.mem_map_equiv]
      change (_ ∧ _) ↔ (hypercube 9).Adj (translate e x) (translate e y) ∧ _
      exact and_congr_left' ⟨translate_adj e, fun h => by simpa using translate_adj e h⟩
    rw [hmap, Finset.card_map]
    exact hCdeg _ ((hDmem x).mp hx)
  have hDclosed := closed_of_regular U D hDU hdeg hDdeg
  -- Transfer the all-vertex adjacency parity to the occupied projection.
  let F := occupied e C
  let R := (Finset.univ : Finset (Q 6)) \ F
  have hfibre (y : Q 6) : Q9ThreeFlipProjectedParity.fiber (inProduct e C) y = fibre e C y := by
    ext p
    simp [Q9ThreeFlipProjectedParity.fiber, fibre]
  have hF : Q9ThreeFlipProjectedParity.occupied (inProduct e C) = F := by
    ext y
    simp [Q9ThreeFlipProjectedParity.occupied, hfibre, F, occupied, Finset.Nonempty, fibre]
  have hEdge : Q9ThreeFlipProjectedParity.EdgeFibers (inProduct e C) := by
    intro y
    rw [hfibre]
    by_cases hy : y ∈ F
    · obtain ⟨p, i, hp⟩ := fibre_eq_edge e C hreg hbal hsep y hy
      exact Or.inr ⟨p, flip p i, flip_adj p i, hp⟩
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hy (by simpa [F, occupied] using
        (show ∃ q, vertex e q y ∈ C from ⟨p, by simpa [fibre] using hp⟩))
  have hEven (y : Q 6) : Even (R.filter ((hypercube 6).Adj y)).card := by
    have h := (Q9ThreeFlipProjectedParity.occupied_and_complement_even
      (inProduct e C) (product_parity e C hreg hbal) hEdge y).2
    rw [hF] at h
    have he : R.filter ((hypercube 6).Adj y) = (hypercube 6).neighborFinset y ∩ R := by
      ext z
      simp [and_comm]
    rwa [he]
  have hSides (b : Bool) : (R.filter fun y => cubeParity y = b).card = 8 := by
    have hcards := (component_and_fibre_cards e C hC hreg hbal hsep).2.2.2 b
    have he : R.filter (fun y => cubeParity y = b) =
        paritySide (Finset.univ : Finset (Q 6)) b \ paritySide F b := by
      ext y
      by_cases hy : cubeParity y = b <;> simp [R, paritySide, hy]
    have hsub : paritySide F b ⊆ paritySide (Finset.univ : Finset (Q 6)) b :=
      Finset.filter_subset_filter _ (Finset.subset_univ _)
    rw [he, Finset.card_sdiff_of_subset hsub, paritySide_univ_card, hcards]
  -- Apply the residual packing bound to the actual split vertex set of the extension.
  have hR (z : Q 6) (hz : z ∉ R) : z ∈ F := by simpa [R] using hz
  have hex (z : Q 6) (hz : z ∉ R) : ∃ p i, fibre e C z = {p, flip p i} :=
    fibre_eq_edge e C hreg hbal hsep z (hR z hz)
  let S (z : Q 6) := fibre e C z ∪ fibre e D z
  have hS (z : Q 6) (p : Q 3) (i : Fin 3) (hp : fibre e C z = {p, flip p i}) :
      S z = edgeAndAntipodes p i := by
    have hD (q : Q 3) : q ∈ fibre e D z ↔ antipode q ∈ fibre e C z := by
      simp [fibre, hDmem]
    have hanti (a b : Q 3) : antipode a = b ↔ a = antipode b :=
      ⟨fun h => by simpa only [antipode_antipode] using congrArg antipode h,
        fun h => by rw [h, antipode_antipode]⟩
    ext q
    simp only [S, edgeAndAntipodes, Finset.mem_union, hD, hp, Finset.mem_insert,
      Finset.mem_singleton, hanti]
  have hCard (z : Q 6) (hz : z ∉ R) : (S z).card = 4 := by
    obtain ⟨p, i, hp⟩ := hex z hz
    rw [hS z p i hp, edgeAndAntipodes_card]
  have hOccupied (z : Q 6) (hz : z ∉ R) (q : Q 3)
      (hqu : (q, z) ∈ inProduct e U) : q ∈ S z := by
    by_contra hq
    obtain ⟨p, i, hp⟩ := hex z hz
    obtain ⟨r, hr, hrq⟩ := outside_edgeAndAntipodes (hS z p i hp ▸ hq)
    have hadj := (vertex_adj_iff e (r, z) (q, z)).mpr (SimpleGraph.boxProd_adj_left.mpr hrq)
    rw [← hp] at hr
    have hrc : vertex e r z ∈ C := by simpa [fibre] using hr
    have hqc := hclosed _ hrc _ ((mem_inProduct e U _).mp hqu) hadj
    exact hq (Finset.mem_union_left _ (by simpa [fibre] using hqc))
  have hSeparated (y : Q 6) (hy : y ∈ R) (z : Q 6) (_hz : z ∉ R)
      (hyz : (hypercube 6).Adj y z) (q : Q 3) (hq : q ∈ S z) :
      (q, y) ∉ inProduct e U := by
    intro hqu
    have hadj := (vertex_adj_iff e (q, z) (q, y)).mpr (SimpleGraph.boxProd_adj_right.mpr hyz.symm)
    have hu : vertex e q y ∈ U := (mem_inProduct e U _).mp hqu
    have hout : y ∉ F := by simpa [R] using hy
    have hnot (r : Q 3) : vertex e r y ∉ C := by
      intro hr
      exact hout (by simpa [F, occupied] using (show ∃ r, vertex e r y ∈ C from ⟨r, hr⟩))
    rcases Finset.mem_union.mp hq with hqC | hqD
    · exact hnot q (hclosed _ (by simpa [fibre] using hqC) _ hu hadj)
    · have hd := hDclosed _ (by simpa [fibre] using hqD) _ hu hadj
      exact hnot (antipode q) (by simpa only [translate_vertex] using (hDmem _).mp hd)
  have hbound := Q6EvenResidualNeighborhood.card_le_256_of_residual_fibers
    hSides hEven (inProduct e U) S hCard hOccupied hSeparated
  simpa only [inProduct, Finset.card_map] using hbound

#print axioms card_le_256_of_three_flip_translate

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipExtensionBound

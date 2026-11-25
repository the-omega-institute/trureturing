/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Full eight-stars on distinct axes have disjoint 32-vertex footprints in a cubic Q9 component. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwoStarAxisBound

/-!
# Packing full eight-star footprints in the nine-cube

For Hong–Wu–Xia, [arXiv:2610.09483v1](https://arxiv.org/abs/2610.09483v1),
§7, Problem 2. An eight-star supplies sixteen paired spoke vertices and
one selected lift of each of sixteen cross-part corners. The center
endpoints of a paired-spoke star on another axis are excluded from all
transverse positions at distance at most three from the first center.

Consequently a spoke of either star cannot belong to the other's
footprint. A common cross-part corner would then have four distinct
selected neighbors, two spokes of each star, contrary to cubicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarFootprintPacking

open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
local notation "flip" => BalancedCriticalSpectrum.flip
local notation "flip_flip" => BalancedCriticalSpectrum.flip_flip
open BalancedCriticalSpectrum (Q)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open Q9TwoStarAxisBound (fibreVertex PairedSpokeStar EightStar)
open private flip_fibre_comm flip_fibre_axis fibreVertex_apply_other from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwoStarAxisBound

/-- Local conditions at either endpoint of the empty center fibre of a paired-spoke star. -/
private structure CenterEndpoint (C : Finset (Q 9)) (j : Fin 9) (x : Q 9) : Prop where
  empty : x ∉ C
  partner_empty : flip x j ∉ C
  neighbor_mem : ∀ k : Fin 9, k ≠ j → flip x k ∈ C
  partner_neighbor_mem : ∀ k : Fin 9, k ≠ j → flip (flip x j) k ∈ C

private theorem centerEndpoint_of_star {C : Finset (Q 9)} {j : Fin 9} {d : Q 9}
    (h : PairedSpokeStar C j d) (t : Bool) : CenterEndpoint C j (fibreVertex d j t) where
  empty := h.center_empty t
  partner_empty := by rw [flip_fibre_axis]; exact h.center_empty (!t)
  neighbor_mem k hk := by rw [flip_fibre_comm]; exact h.spoke_mem k hk t
  partner_neighbor_mem k hk := by
    rw [flip_fibre_axis, flip_fibre_comm]
    exact h.spoke_mem k hk (!t)

private theorem center_no_zero {C : Finset (Q 9)} {i j : Fin 9} {c : Q 9}
    (h : PairedSpokeStar C i c) (hji : j ≠ i) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex c i t)) : False := by
  apply hc.partner_empty
  rw [flip_fibre_comm]
  exact h.spoke_mem j hji t

private theorem center_no_one {C : Finset (Q 9)} {i j a : Fin 9} {c : Q 9}
    (h : PairedSpokeStar C i c) (hai : a ≠ i) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex (flip c a) i t)) : False :=
  hc.empty (h.spoke_mem a hai t)

private theorem center_no_mixed {C : Finset (Q 9)} {i j a b : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (hji : j ≠ i)
    (ha : a ∈ A) (hb : b ∈ B) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex (flip (flip c a) b) i t)) : False := by
  have hai : a ≠ i := (h.partition a).mp (Or.inl ha)
  have hbi : b ≠ i := (h.partition b).mp (Or.inr hb)
  by_cases hja : j = a
  · subst j
    apply hc.partner_empty
    rw [flip_fibre_comm, flip_comm c a b, flip_flip]
    exact h.paired.spoke_mem b hbi t
  by_cases hjb : j = b
  · subst j
    apply hc.partner_empty
    rw [flip_fibre_comm, flip_flip]
    exact h.paired.spoke_mem a hai t
  rcases (h.partition j).mpr hji with hj | hj
  · have hs := hc.partner_neighbor_mem b (Ne.symm hjb)
    simp only [flip_fibre_comm] at hs
    rw [flip_comm (flip c a) b j, flip_flip] at hs
    exact h.same_part_empty a j (Ne.symm hja) (Or.inl ⟨ha, hj⟩) t hs
  · have hs := hc.partner_neighbor_mem a (Ne.symm hja)
    simp only [flip_fibre_comm] at hs
    rw [flip_comm c a b, flip_comm (flip c b) a j, flip_flip] at hs
    exact h.same_part_empty b j (Ne.symm hjb) (Or.inr ⟨hb, hj⟩) t hs

private theorem center_no_two {C : Finset (Q 9)} {i j a b : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B)
    (hji : j ≠ i) (hai : a ≠ i) (hbi : b ≠ i) (hab : a ≠ b) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex (flip (flip c a) b) i t)) : False := by
  rcases (h.partition a).mpr hai with ha | ha
  · rcases (h.partition b).mpr hbi with hb | hb
    · have hs := hc.neighbor_mem i (Ne.symm hji)
      rw [flip_fibre_axis] at hs
      exact h.same_part_empty a b hab (Or.inl ⟨ha, hb⟩) (!t) hs
    · exact center_no_mixed h hji ha hb t hc
  · rcases (h.partition b).mpr hbi with hb | hb
    · rw [flip_comm c a b] at hc
      exact center_no_mixed h hji hb ha t hc
    · have hs := hc.neighbor_mem i (Ne.symm hji)
      rw [flip_fibre_axis] at hs
      exact h.same_part_empty a b hab (Or.inr ⟨ha, hb⟩) (!t) hs

-- A same-part corner is absent in both axial layers. No center endpoint
-- can have it as a transverse neighbor, even along its own empty axis.
private theorem center_no_same_part_extension {C : Finset (Q 9)}
    {i j a b k : Fin 9} {c : Q 9} {A B : Finset (Fin 9)}
    (h : EightStar C i c A B) (hji : j ≠ i) (hab : a ≠ b)
    (hSame : (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B)) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex (flip (flip (flip c a) b) k) i t)) :
    False := by
  rw [← flip_fibre_comm (flip (flip c a) b) i k t] at hc
  by_cases hkj : k = j
  · subst k
    have hs := hc.partner_neighbor_mem i (Ne.symm hji)
    rw [flip_flip, flip_fibre_axis] at hs
    exact h.same_part_empty a b hab hSame (!t) hs
  · have hs := hc.neighbor_mem k hkj
    rw [flip_flip] at hs
    exact h.same_part_empty a b hab hSame t hs

private theorem center_no_three {C : Finset (Q 9)} {i j a b k : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B)
    (hji : j ≠ i) (hai : a ≠ i) (hbi : b ≠ i) (hki : k ≠ i)
    (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) (t : Bool)
    (hc : CenterEndpoint C j (fibreVertex (flip (flip (flip c a) b) k) i t)) :
    False := by
  rcases (h.partition a).mpr hai with ha | ha <;>
    rcases (h.partition b).mpr hbi with hb | hb
  · exact center_no_same_part_extension h hji hab (Or.inl ⟨ha, hb⟩) t hc
  · rcases (h.partition k).mpr hki with hk | hk
    · rw [flip_comm (flip c a) b k] at hc
      exact center_no_same_part_extension h hji hak (Or.inl ⟨ha, hk⟩) t hc
    · rw [flip_comm c a b, flip_comm (flip c b) a k] at hc
      exact center_no_same_part_extension h hji hbk (Or.inr ⟨hb, hk⟩) t hc
  · rcases (h.partition k).mpr hki with hk | hk
    · rw [flip_comm c a b, flip_comm (flip c b) a k] at hc
      exact center_no_same_part_extension h hji hbk (Or.inl ⟨hb, hk⟩) t hc
    · rw [flip_comm (flip c a) b k] at hc
      exact center_no_same_part_extension h hji hak (Or.inr ⟨ha, hk⟩) t hc
  · exact center_no_same_part_extension h hji hab (Or.inr ⟨ha, hb⟩) t hc

-- A vertex of the first footprint, flipped in any direction, cannot be
-- a center endpoint of another star.
private theorem center_no_flip_spoke {C : Finset (Q 9)} {i j a k : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (hji : j ≠ i)
    (hai : a ≠ i) (t : Bool)
    (hc : CenterEndpoint C j (flip (fibreVertex (flip c a) i t) k)) : False := by
  by_cases hki : k = i
  · subst k
    rw [flip_fibre_axis] at hc
    exact center_no_one h.paired hai (!t) hc
  rw [flip_fibre_comm] at hc
  by_cases hka : k = a
  · subst k
    rw [flip_flip] at hc
    exact center_no_zero h.paired hji t hc
  exact center_no_two h hji hai hki (Ne.symm hka) t hc

private theorem center_no_flip_corner {C : Finset (Q 9)} {i j a b k : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (hji : j ≠ i)
    (ha : a ∈ A) (hb : b ∈ B) (t : Bool)
    (hc : CenterEndpoint C j (flip (fibreVertex (flip (flip c a) b) i t) k)) :
    False := by
  have hai : a ≠ i := (h.partition a).mp (Or.inl ha)
  have hbi : b ≠ i := (h.partition b).mp (Or.inr hb)
  have hab : a ≠ b := fun he => Finset.disjoint_left.mp h.disjoint ha (he ▸ hb)
  by_cases hki : k = i
  · subst k
    rw [flip_fibre_axis] at hc
    exact center_no_mixed h hji ha hb (!t) hc
  rw [flip_fibre_comm] at hc
  by_cases hka : k = a
  · subst k
    rw [flip_comm c a b, flip_flip] at hc
    exact center_no_one h.paired hbi t hc
  by_cases hkb : k = b
  · subst k
    rw [flip_flip] at hc
    exact center_no_one h.paired hai t hc
  exact center_no_three h hji hai hbi hki hab (Ne.symm hka) (Ne.symm hkb) t hc

/-- All sixteen lifts of the eight paired spokes. -/
def spokeVertices (i : Fin 9) (c : Q 9) : Finset (Q 9) :=
  (univ : Finset (↥(univ.erase i) × Bool)).image
    (fun p => fibreVertex (flip c p.1) i p.2)

theorem mem_spokeVertices {i : Fin 9} {c v : Q 9} :
    v ∈ spokeVertices i c ↔ ∃ a : Fin 9, a ≠ i ∧
      ∃ t : Bool, v = fibreVertex (flip c a) i t := by
  constructor
  · intro hv
    obtain ⟨p, _, hp⟩ := mem_image.mp hv
    exact ⟨p.1, (mem_erase.mp p.1.property).1, p.2, hp.symm⟩
  · rintro ⟨a, hai, t, rfl⟩
    exact mem_image.mpr ⟨(⟨a, mem_erase.mpr ⟨hai, mem_univ a⟩⟩, t), mem_univ _, rfl⟩

/-- A lift of a mixed corner in the first star's four-four partition. -/
def IsMixedCorner (i : Fin 9) (c : Q 9) (A B : Finset (Fin 9)) (v : Q 9) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ t : Bool, v = fibreVertex (flip (flip c a) b) i t

/-- A full star's spokes and mixed corner lifts exclude every spoke of a
paired-spoke star on a distinct axis. This uses occupancy alone. -/
theorem footprint_vertex_not_other_spoke {C : Finset (Q 9)} {i j : Fin 9} {c d v : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (hji : j ≠ i)
    (hother : PairedSpokeStar C j d)
    (hv : v ∈ spokeVertices i c ∨ IsMixedCorner i c A B v) :
    v ∉ spokeVertices j d := by
  intro hspoke
  obtain ⟨k, hkj, s, hk⟩ := mem_spokeVertices.mp hspoke
  have hc : CenterEndpoint C j (flip v k) := by
    rw [hk, flip_fibre_comm, flip_flip]
    exact centerEndpoint_of_star hother s
  rcases hv with hv | hv
  · obtain ⟨a, hai, t, rfl⟩ := mem_spokeVertices.mp hv
    exact center_no_flip_spoke h hji hai t hc
  · obtain ⟨a, ha, b, hb, t, rfl⟩ := hv
    exact center_no_flip_corner h hji ha hb t hc

private theorem mixed_corner_spoke_neighbors {i a b : Fin 9} {c : Q 9}
    (hai : a ≠ i) (hbi : b ≠ i) (t : Bool) :
    flip (fibreVertex (flip (flip c a) b) i t) a ∈ spokeVertices i c ∧
    flip (fibreVertex (flip (flip c a) b) i t) b ∈ spokeVertices i c := by
  constructor
  · rw [flip_fibre_comm, flip_comm c a b, flip_flip]
    exact mem_spokeVertices.mpr ⟨b, hbi, t, rfl⟩
  · rw [flip_fibre_comm, flip_flip]
    exact mem_spokeVertices.mpr ⟨a, hai, t, rfl⟩

private theorem spokeVertices_subset {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    (h : PairedSpokeStar C i c) : spokeVertices i c ⊆ C := by
  intro v hv
  obtain ⟨a, hai, t, rfl⟩ := mem_spokeVertices.mp hv
  exact h.spoke_mem a hai t

/-- The two sets of possible footprint vertices cannot share a selected
vertex when both stars lie in a cubic set. -/
theorem footprint_vertices_disjoint {C : Finset (Q 9)} {i j : Fin 9} {c d v : Q 9}
    {A B D E : Finset (Fin 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hfirst : EightStar C i c A B) (hsecond : EightStar C j d D E)
    (hji : j ≠ i) (hv : v ∈ C)
    (hvi : v ∈ spokeVertices i c ∨ IsMixedCorner i c A B v)
    (hvj : v ∈ spokeVertices j d ∨ IsMixedCorner j d D E v) : False := by
  have hi := footprint_vertex_not_other_spoke hsecond (Ne.symm hji) hfirst.paired hvj
  have hj := footprint_vertex_not_other_spoke hfirst hji hsecond.paired hvi
  rcases hvi with hvi | hvi
  · exact hi hvi
  rcases hvj with hvj | hvj
  · exact hj hvj
  obtain ⟨a, ha, b, hb, t, hvab⟩ := hvi
  obtain ⟨k, hk, l, hl, s, hvkl⟩ := hvj
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp hfirst.disjoint ha (h ▸ hb)
  have hkl : k ≠ l := fun h => Finset.disjoint_left.mp hsecond.disjoint hk (h ▸ hl)
  have hfirst_neighbors : flip v a ∈ spokeVertices i c ∧ flip v b ∈ spokeVertices i c := by
    rw [hvab]
    exact mixed_corner_spoke_neighbors ((hfirst.partition a).mp (Or.inl ha))
      ((hfirst.partition b).mp (Or.inr hb)) t
  have hsecond_neighbors : flip v k ∈ spokeVertices j d ∧ flip v l ∈ spokeVertices j d := by
    rw [hvkl]
    exact mixed_corner_spoke_neighbors ((hsecond.partition k).mp (Or.inl hk))
      ((hsecond.partition l).mp (Or.inr hl)) s
  let I : Finset (Fin 9) := {a, b}
  let J : Finset (Fin 9) := {k, l}
  have hI (r : Fin 9) (hrI : r ∈ I) : flip v r ∈ spokeVertices i c := by
    have he : r = a ∨ r = b := by simpa [I] using hrI
    rcases he with rfl | rfl
    · exact hfirst_neighbors.1
    · exact hfirst_neighbors.2
  have hJ (r : Fin 9) (hrJ : r ∈ J) : flip v r ∈ spokeVertices j d := by
    have he : r = k ∨ r = l := by simpa [J] using hrJ
    rcases he with rfl | rfl
    · exact hsecond_neighbors.1
    · exact hsecond_neighbors.2
  have hd : Disjoint I J := by
    apply Finset.disjoint_left.mpr
    intro r hrI hrJ
    exact footprint_vertex_not_other_spoke hfirst hji hsecond.paired (Or.inl (hI r hrI))
      (hJ r hrJ)
  have hsub : I ∪ J ⊆ directions C v := by
    intro r hrIJ
    apply (mem_directions C v r).mpr
    rcases mem_union.mp hrIJ with hrI | hrJ
    · exact spokeVertices_subset hfirst.paired (hI r hrI)
    · exact spokeVertices_subset hsecond.paired (hJ r hrJ)
  have hIc : I.card = 2 := by simp [I, hab]
  have hJc : J.card = 2 := by simp [J, hkl]
  have hbound := card_le_card hsub
  rw [card_union_of_disjoint hd, hIc, hJc, regular_directions C hr hv] at hbound
  omega

-- Counting is done via the transverse coordinates of the footprint.
private def transverseDiff (i : Fin 9) (c v : Q 9) : Finset (Fin 9) :=
  (univ.erase i).filter (fun k => v k ≠ c k)

private theorem transverseDiff_spoke (i : Fin 9) (c : Q 9) {a : Fin 9}
    (hai : a ≠ i) (t : Bool) :
    transverseDiff i c (fibreVertex (flip c a) i t) = {a} := by
  ext k
  simp only [transverseDiff, mem_filter, mem_erase, mem_univ, true_and, mem_singleton]
  by_cases hki : k = i
  · subst k
    simp [hai.symm]
  rw [fibreVertex_apply_other _ hki]
  by_cases hka : k = a
  · subst k
    cases hca : c a <;> simp [hca, hai]
  · simp [BalancedCriticalSpectrum.flip, hki, hka]

private theorem transverseDiff_corner (i : Fin 9) (c : Q 9) {a b : Fin 9}
    (hai : a ≠ i) (hbi : b ≠ i) (hab : a ≠ b) (t : Bool) :
    transverseDiff i c (fibreVertex (flip (flip c a) b) i t) = {a, b} := by
  ext k
  simp only [transverseDiff, mem_filter, mem_erase, mem_univ, true_and, mem_insert,
    mem_singleton]
  by_cases hki : k = i
  · subst k
    simp [hai.symm, hbi.symm]
  rw [fibreVertex_apply_other _ hki]
  by_cases hka : k = a
  · subst k
    cases hca : c a <;> simp [BalancedCriticalSpectrum.flip, hca, hab, hai]
  by_cases hkb : k = b
  · subst k
    cases hcb : c b <;> simp [BalancedCriticalSpectrum.flip, hcb, hab.symm, hbi]
  · simp [BalancedCriticalSpectrum.flip, hki, hka, hkb]

private theorem fibreVertex_injective (x : Q 9) (i : Fin 9) :
    Function.Injective (fibreVertex x i) := by
  intro s t h
  have he := congrFun h i
  cases s <;> cases t <;> cases hxi : x i <;> simp [fibreVertex, hxi] at he ⊢

theorem card_spokeVertices (i : Fin 9) (c : Q 9) : (spokeVertices i c).card = 16 := by
  have hne (a : ↥(univ.erase i)) : (a : Fin 9) ≠ i := (mem_erase.mp a.property).1
  have hinj : Function.Injective
      (fun p : ↥(univ.erase i) × Bool => fibreVertex (flip c p.1) i p.2) := by
    intro p q he
    have hd := congrArg (transverseDiff i c) he
    rw [transverseDiff_spoke i c (hne p.1), transverseDiff_spoke i c (hne q.1)] at hd
    have hpq : p.1 = q.1 := Subtype.ext (by simpa using hd)
    apply Prod.ext hpq
    apply fibreVertex_injective (flip c p.1) i
    simpa only [hpq] using he
  rw [spokeVertices, card_image_of_injective _ hinj, card_univ, Fintype.card_prod,
    Fintype.card_coe, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin, Fintype.card_bool]

private def cornerVertex {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (p : ↥A × ↥B) : Q 9 :=
  fibreVertex (flip (flip c p.1) p.2) i
    (Classical.choose (h.cross_occupied p.1 p.2 (Or.inl ⟨p.1.property, p.2.property⟩)))

private theorem cornerVertex_mem {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (p : ↥A × ↥B) :
    cornerVertex h p ∈ C :=
  Classical.choose_spec (h.cross_occupied p.1 p.2 (Or.inl ⟨p.1.property, p.2.property⟩))

private theorem cornerVertex_mixed {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (p : ↥A × ↥B) :
    IsMixedCorner i c A B (cornerVertex h p) :=
  ⟨p.1, p.1.property, p.2, p.2.property, _, rfl⟩

private theorem cornerVertex_diff {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (p : ↥A × ↥B) :
    transverseDiff i c (cornerVertex h p) = {(p.1 : Fin 9), (p.2 : Fin 9)} := by
  apply transverseDiff_corner i c
  · exact (h.partition p.1).mp (Or.inl p.1.property)
  · exact (h.partition p.2).mp (Or.inr p.2.property)
  · intro he
    exact Finset.disjoint_left.mp h.disjoint p.1.property (he ▸ p.2.property)

private theorem cornerVertex_injective {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) :
    Function.Injective (cornerVertex h) := by
  intro p q he
  have hd := congrArg (transverseDiff i c) he
  rw [cornerVertex_diff h p, cornerVertex_diff h q] at hd
  have hp : (p.1 : Fin 9) ∈ ({(q.1 : Fin 9), (q.2 : Fin 9)} : Finset (Fin 9)) := by
    rw [← hd]
    simp
  have hq : (p.2 : Fin 9) ∈ ({(q.1 : Fin 9), (q.2 : Fin 9)} : Finset (Fin 9)) := by
    rw [← hd]
    simp
  apply Prod.ext
  · apply Subtype.ext
    rcases mem_insert.mp hp with he | he
    · exact he
    · have he' := mem_singleton.mp he
      exact False.elim (Finset.disjoint_left.mp h.disjoint p.1.property (he' ▸ q.2.property))
  · apply Subtype.ext
    rcases mem_insert.mp hq with he | he
    · exact False.elim (Finset.disjoint_left.mp h.disjoint (he ▸ q.1.property) p.2.property)
    · exact mem_singleton.mp he

/-- The sixteen spokes and one selected endpoint of each mixed corner fibre. -/
def starFootprint {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) : Finset (Q 9) :=
  spokeVertices i c ∪ (univ : Finset (↥A × ↥B)).image (cornerVertex h)

theorem starFootprint_subset {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) : starFootprint h ⊆ C := by
  intro v hv
  rcases mem_union.mp hv with hv | hv
  · exact spokeVertices_subset h.paired hv
  · obtain ⟨p, _, rfl⟩ := mem_image.mp hv
    exact cornerVertex_mem h p

theorem mem_starFootprint_cases {C : Finset (Q 9)} {i : Fin 9} {c v : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) (hv : v ∈ starFootprint h) :
    v ∈ spokeVertices i c ∨ IsMixedCorner i c A B v := by
  rcases mem_union.mp hv with hv | hv
  · exact Or.inl hv
  · obtain ⟨p, _, rfl⟩ := mem_image.mp hv
    exact Or.inr (cornerVertex_mixed h p)

theorem card_starFootprint {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) : (starFootprint h).card = 32 := by
  have hd : Disjoint (spokeVertices i c) ((univ : Finset (↥A × ↥B)).image (cornerVertex h)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨p, _, rfl⟩ := mem_image.mp hw
    obtain ⟨a, hai, t, he⟩ := mem_spokeVertices.mp hv
    have he' := congrArg (transverseDiff i c) he
    rw [cornerVertex_diff h p, transverseDiff_spoke i c hai t] at he'
    have hne : (p.1 : Fin 9) ≠ (p.2 : Fin 9) := fun heq =>
      Finset.disjoint_left.mp h.disjoint p.1.property (heq ▸ p.2.property)
    have hcard := congrArg Finset.card he'
    simp [hne] at hcard
  rw [starFootprint, card_union_of_disjoint hd, card_spokeVertices,
    card_image_of_injective _ (cornerVertex_injective h), card_univ, Fintype.card_prod,
    Fintype.card_coe, Fintype.card_coe, h.card_left, h.card_right]

/-- Different star axes have disjoint full footprints. -/
theorem starFootprint_disjoint {C : Finset (Q 9)} {i j : Fin 9} {c d : Q 9}
    {A B D E : Finset (Fin 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hji : j ≠ i) (hfirst : EightStar C i c A B) (hsecond : EightStar C j d D E) :
    Disjoint (starFootprint hfirst) (starFootprint hsecond) := by
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact footprint_vertices_disjoint hr hfirst hsecond hji (starFootprint_subset hfirst hvi)
    (mem_starFootprint_cases hfirst hvi) (mem_starFootprint_cases hsecond hvj)

/-- Any set of full eight-star axes in a cubic Q9 component uses at least
thirty-two vertices per axis. There is no balance hypothesis. -/
theorem thirty_two_mul_card_le_of_eight_stars {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (J : Finset (Fin 9))
    (hstars : ∀ i ∈ J, ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B) :
    32 * J.card ≤ C.card := by
  have hex (i : ↥J) : ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B :=
    hstars i i.property
  choose center A B hstar using hex
  let F (i : ↥J) : Finset (Q 9) := starFootprint (hstar i)
  have hd : (↑(univ : Finset ↥J) : Set ↥J).PairwiseDisjoint F := by
    intro i _ j _ hij
    exact starFootprint_disjoint hr (fun he => hij (Subtype.ext he.symm)) (hstar i) (hstar j)
  have hsub : (univ : Finset ↥J).biUnion F ⊆ C := by
    intro v hv
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
    exact starFootprint_subset (hstar i) hi
  calc
    32 * J.card = ∑ i : ↥J, (F i).card := by
      simp [F, card_starFootprint, Fintype.card_coe, nsmul_eq_mul, Nat.mul_comm]
    _ = ((univ : Finset ↥J).biUnion F).card := (card_biUnion hd).symm
    _ ≤ C.card := card_le_card hsub

/-- At most eight distinct star axes occur in a cubic set of at most 258 vertices. -/
theorem card_star_axes_le_eight {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hC : C.card ≤ 258) (J : Finset (Fin 9))
    (hstars : ∀ i ∈ J, ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B) :
    J.card ≤ 8 := by
  have h := thirty_two_mul_card_le_of_eight_stars hr J hstars
  omega

/-- Hence a cubic subset of a 258-vertex set cannot have full stars on all nine axes. -/
theorem not_all_axes_eight_stars {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hC : C.card ≤ 258) :
    ¬ (∀ i : Fin 9, ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B) := by
  intro h
  have hbound := card_star_axes_le_eight hr hC univ (fun i _ => h i)
  rw [card_univ, Fintype.card_fin] at hbound
  omega

/-- In a cubic component of at most 126 vertices, at most three axes have full stars. -/
theorem card_star_axes_le_three {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hC : C.card ≤ 126) (J : Finset (Fin 9))
    (hstars : ∀ i ∈ J, ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B) :
    J.card ≤ 3 := by
  have h := thirty_two_mul_card_le_of_eight_stars hr J hstars
  omega

open Q9OccupiedFibreParity (doubleFibres)
open Q9FoldedIncidence (restrictCoordinates)
open private liftVertex insert_drop flip_insert dropCoordinate_flip_keep parity_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

local notation "drop" => fun a : Fin 9 => restrictCoordinates (Fin.succAboveEmb a)
local notation "parity" => fun z : Q 8 => ∑ r, z r

private theorem drop_mem_doubleFibres {C : Finset (Q 9)} {j : Fin 9} {x : Q 9}
    {p : Bool} (hx : x ∈ C) (hflip : flip x j ∈ C) (hp : parity (drop j x) = p) :
    drop j x ∈ doubleFibres C j p := by
  have he := insert_drop j x
  have hf := flip_insert j (x j) (drop j x)
  rw [insert_drop] at hf
  simp only [doubleFibres, mem_filter, mem_univ, true_and]
  refine ⟨?_, hp⟩
  cases ht : x j
  · simp only [ht, Bool.not_false] at he hf
    exact ⟨by rw [he]; exact hx, by rw [← hf]; exact hflip⟩
  · simp only [ht, Bool.not_true] at he hf
    exact ⟨by rw [← hf]; exact hflip, by rw [he]; exact hx⟩

private theorem projectedParity_flip {j a : Fin 9} (haj : a ≠ j) (x : Q 9) :
    parity (drop j (flip x a)) = !(parity (drop j x)) := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq haj
  rw [dropCoordinate_flip_keep, parity_flip]

-- The corner lifts of the four opposite-part directions must split
-- two and two between the axial layers of the first star.
private theorem doubleFibres_ge_two_of_cross_corners {C : Finset (Q 9)} {i j : Fin 9}
    {c : Q 9} (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hstar : PairedSpokeStar C i c) (hji : j ≠ i)
    (P : Finset (Fin 9)) (hP : P.card = 4)
    (hPi : ∀ b ∈ P, b ≠ i) (hPj : ∀ b ∈ P, b ≠ j)
    (hcross : ∀ b ∈ P, ∃ t, fibreVertex (flip (flip c j) b) i t ∈ C)
    (p : Bool) : 2 ≤ (doubleFibres C j p).card := by
  have hex (b : ↥P) : ∃ t, fibreVertex (flip (flip c j) b) i t ∈ C :=
    hcross b b.property
  choose layer hlayer using hex
  let L (t : Bool) : Finset ↥P := univ.filter (fun b => layer b = t)
  have hLle (t : Bool) : (L t).card ≤ 2 := by
    let x := fibreVertex (flip c j) i t
    let R := (L t).image (fun b : ↥P => (b : Fin 9))
    have hiR : i ∉ R := by
      intro hi
      obtain ⟨b, _, he⟩ := mem_image.mp hi
      exact hPi b b.property he
    have hsub : insert i R ⊆ directions C x := by
      intro a ha
      apply (mem_directions C x a).mpr
      rcases mem_insert.mp ha with rfl | ha
      · dsimp only [x]
        rw [flip_fibre_axis]
        exact hstar.spoke_mem j hji (!t)
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
        have ht : layer b = t := (mem_filter.mp hb).2
        dsimp only [x]
        rw [flip_fibre_comm, ← ht]
        exact hlayer b
    have hc := card_le_card hsub
    have hx : x ∈ C := hstar.spoke_mem j hji t
    rw [card_insert_of_notMem hiR, regular_directions C hr hx] at hc
    have hR : R.card = (L t).card := card_image_of_injective _ Subtype.val_injective
    rw [hR] at hc
    omega
  have hLsum : (L false).card + (L true).card = 4 := by
    have hnot : L true = (univ : Finset ↥P).filter (fun b => ¬ layer b = false) := by
      ext b
      cases hb : layer b <;> simp [L, hb]
    rw [hnot]
    dsimp only [L]
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_coe, hP]
  have hLcard (t : Bool) : (L t).card = 2 := by
    have hf := hLle false
    have ht := hLle true
    cases t <;> omega
  have hparity : parity (drop j (fibreVertex c i true)) =
      !(parity (drop j (fibreVertex c i false))) :=
    projectedParity_flip (Ne.symm hji) c
  obtain ⟨t, ht⟩ : ∃ t : Bool, (!(parity (drop j (fibreVertex c i t)))) = p := by
    by_cases hp : (!(parity (drop j (fibreVertex c i false)))) = p
    · exact ⟨false, hp⟩
    · refine ⟨true, ?_⟩
      rw [hparity]
      cases he : parity (drop j (fibreVertex c i false)) <;> cases p <;> simp_all
  let base (b : ↥P) := fibreVertex (flip c b) i t
  let project (b : ↥P) := drop j (base b)
  have hinj : Function.Injective project := by
    intro b b' he
    apply Subtype.ext
    by_contra hne
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (hPj b b.property)
    have hbit := congrFun he k
    change base b (j.succAbove k) = base b' (j.succAbove k) at hbit
    rw [hk] at hbit
    simp only [base, fibreVertex_apply_other _ (hPi b b.property),
      BalancedCriticalSpectrum.flip_apply_same] at hbit
    cases hb : c b <;> simp [BalancedCriticalSpectrum.flip, hne, hb] at hbit
  have hsub : (L t).image project ⊆ doubleFibres C j p := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hz
    apply drop_mem_doubleFibres
    · exact hstar.spoke_mem b (hPi b b.property) t
    · have hbt : layer b = t := (mem_filter.mp hb).2
      change flip (fibreVertex (flip c b) i t) j ∈ C
      rw [flip_fibre_comm, flip_comm c b j, ← hbt]
      exact hlayer b
    · change parity (drop j (fibreVertex (flip c b) i t)) = p
      rw [← flip_fibre_comm c i b t, projectedParity_flip (hPj b b.property)]
      exact ht
  have hle := card_le_card hsub
  rw [card_image_of_injective _ hinj, hLcard t] at hle
  exact hle

/-- Each other axis has at least two paired fibres of either projected parity.
The four cross-corner edges parallel to that axis split evenly between the
two layers of the first star, because each paired spoke endpoint has only
two further selected neighbors. -/
theorem doubleFibres_ge_two_of_eightStar {C : Finset (Q 9)} {i j : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (h : EightStar C i c A B) (hji : j ≠ i) (p : Bool) :
    2 ≤ (doubleFibres C j p).card := by
  rcases (h.partition j).mpr hji with hj | hj
  · exact doubleFibres_ge_two_of_cross_corners hr h.paired hji B h.card_right
      (fun b hb => (h.partition b).mp (Or.inr hb))
      (fun b hb he => Finset.disjoint_left.mp h.disjoint hj (he ▸ hb))
      (fun b hb => h.cross_occupied j b (Or.inl ⟨hj, hb⟩)) p
  · exact doubleFibres_ge_two_of_cross_corners hr h.paired hji A h.card_left
      (fun b hb => (h.partition b).mp (Or.inl hb))
      (fun b hb he => Finset.disjoint_left.mp h.disjoint (he ▸ hb) hj)
      (fun b hb => h.cross_occupied j b (Or.inr ⟨hj, hb⟩)) p

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarFootprintPacking

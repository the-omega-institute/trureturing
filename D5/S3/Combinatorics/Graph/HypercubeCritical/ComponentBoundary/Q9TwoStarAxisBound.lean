/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TwoStarAxisBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two stars on different Q9 axes force twelve parallel edges in the second direction. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

/-!
# Two-axis eight-star bound in the nine-cube

For Hong–Wu–Xia, [arXiv:2610.09483v1](https://arxiv.org/abs/2610.09483v1),
§7, Problem 2. In a full star on axis `i`, place the distinct axis `j` in
one part of the four-four split. Each coordinate in the opposite part gives
a selected `j`-edge joining a spoke lift to a cross-corner lift.

If such an edge were a spoke of a second star on `j`, flipping its spoke
direction would take it to the second center fibre. A flip on `i` or on
the opposite-part coordinate makes that center occupied. Every other flip
makes one of the second star's required spoke lifts a forbidden same-part
corner of the first star. The four cross edges and the eight spokes
therefore give twelve distinct edges on `j` using occupancy alone.
Uniform direction counts then give seventy-two vertices in a balanced
cubic component with these stars.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwoStarAxisBound

open Finset
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
local notation "flip" => BalancedCriticalSpectrum.flip
local notation "flip_flip" => BalancedCriticalSpectrum.flip_flip
open BalancedCriticalSpectrum (Q flip_adj directionEdges direction_edge_count
  IsBalanced)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions directions_card mem_directions)
open private liftVertex flip_insert from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

/-- The two vertices in the fibre of `x` on axis `i`, indexed relative to `x`. -/
def fibreVertex (x : Q 9) (i : Fin 9) : Bool → Q 9
  | false => x
  | true => flip x i

/-- The center fibre is empty and every transverse spoke fibre is paired. -/
structure PairedSpokeStar (C : Finset (Q 9)) (i : Fin 9) (c : Q 9) : Prop where
  center_empty : ∀ t, fibreVertex c i t ∉ C
  spoke_mem : ∀ a : Fin 9, a ≠ i → ∀ t, fibreVertex (flip c a) i t ∈ C

/-- The transverse axes of a paired-spoke star split into two sets of four.
Same-part corner fibres are empty and cross-part corner fibres are occupied. -/
structure EightStar (C : Finset (Q 9)) (i : Fin 9) (c : Q 9)
    (A B : Finset (Fin 9)) : Prop where
  paired : PairedSpokeStar C i c
  card_left : A.card = 4
  card_right : B.card = 4
  disjoint : Disjoint A B
  partition : ∀ a : Fin 9, a ∈ A ∨ a ∈ B ↔ a ≠ i
  same_part_empty : ∀ a b : Fin 9, a ≠ b →
    ((a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B)) →
    ∀ t, fibreVertex (flip (flip c a) b) i t ∉ C
  cross_occupied : ∀ a b : Fin 9, ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A)) →
    ∃ t, fibreVertex (flip (flip c a) b) i t ∈ C

private theorem EightStar.swap {C : Finset (Q 9)} {i : Fin 9} {c : Q 9}
    {A B : Finset (Fin 9)} (h : EightStar C i c A B) : EightStar C i c B A where
  paired := h.paired
  card_left := h.card_right
  card_right := h.card_left
  disjoint := h.disjoint.symm
  partition a := (or_comm : (a ∈ B ∨ a ∈ A) ↔ (a ∈ A ∨ a ∈ B)).trans (h.partition a)
  same_part_empty a b hab hSame := h.same_part_empty a b hab (hSame.elim Or.inr Or.inl)
  cross_occupied a b hCross := h.cross_occupied a b (hCross.elim Or.inr Or.inl)

private theorem flip_fibre_comm (x : Q 9) (i k : Fin 9) (t : Bool) :
    flip (fibreVertex x i t) k = fibreVertex (flip x k) i t := by
  cases t
  · rfl
  · exact flip_comm x i k

private theorem flip_fibre_axis (x : Q 9) (i : Fin 9) (t : Bool) :
    flip (fibreVertex x i t) i = fibreVertex x i (!t) := by
  cases t
  · rfl
  · exact flip_flip x i

private theorem flip_apply_other (v : Q 9) {i k : Fin 9} (hk : k ≠ i) :
    flip v i k = v k := by
  simp [BalancedCriticalSpectrum.flip, hk]

private theorem fibreVertex_apply_other (v : Q 9) {i k : Fin 9} (hk : k ≠ i) (t : Bool) :
    fibreVertex v i t k = v k := by
  cases t
  · rfl
  · exact flip_apply_other v hk

/-- The endpoint used by `directionEdges` to count an axial edge. -/
private def edgeBase (j : Fin 9) (v : Q 9) : Q 9 :=
  if v j = false then v else flip v j

private theorem edgeBase_apply_other (v : Q 9) {j k : Fin 9} (hk : k ≠ j) :
    edgeBase j v k = v k := by
  by_cases h : v j = false
  · rw [edgeBase, if_pos h]
  · rw [edgeBase, if_neg h, flip_apply_other v hk]

private theorem edgeBase_mem {C : Finset (Q 9)} {j : Fin 9} {v : Q 9}
    (hv : v ∈ C) (hflip : flip v j ∈ C) :
    edgeBase j v ∈ C.filter (fun x => x j = false ∧ flip x j ∈ C) := by
  cases h : v j <;> simp [edgeBase, h, hv, hflip]

private theorem edgeBase_eq_cases {j : Fin 9} {v w : Q 9}
    (h : edgeBase j v = edgeBase j w) : v = w ∨ v = flip w j := by
  cases hv : v j <;> cases hw : w j
  · exact Or.inl (by simpa [edgeBase, hv, hw] using h)
  · exact Or.inr (by simpa [edgeBase, hv, hw] using h)
  · exact Or.inr (by
      have he : flip v j = w := by simpa [edgeBase, hv, hw] using h
      simpa only [flip_flip] using congrArg (fun z => flip z j) he)
  · exact Or.inl (by
      have he : flip v j = flip w j := by simpa [edgeBase, hv, hw] using h
      simpa only [flip_flip] using congrArg (fun z => flip z j) he)

private theorem cross_edge_ne_spoke {C : Finset (Q 9)} {i j : Fin 9} {c d : Q 9}
    {A B : Finset (Fin 9)} (hfirst : EightStar C i c A B)
    (hsecond : PairedSpokeStar C j d) {b k : Fin 9}
    (hj : j ∈ A) (hb : b ∈ B) (hk : k ≠ j) (t : Bool) :
    edgeBase j (fibreVertex (flip c b) i t) ≠ edgeBase j (flip d k) := by
  intro he
  have hji : j ≠ i := (hfirst.partition j).mp (Or.inl hj)
  have hbi : b ≠ i := (hfirst.partition b).mp (Or.inr hb)
  have hbj : b ≠ j := fun h => Finset.disjoint_left.mp hfirst.disjoint hj (h ▸ hb)
  obtain ⟨s, hcenter⟩ :
      ∃ s, flip (fibreVertex (flip c b) i t) k = fibreVertex d j s := by
    rcases edgeBase_eq_cases he with h | h
    · exact ⟨false, by
        change flip (fibreVertex (flip c b) i t) k = d
        rw [h, flip_flip]⟩
    · exact ⟨true, by
        change flip (fibreVertex (flip c b) i t) k = flip d j
        rw [h, flip_comm (flip d k) j k, flip_flip]⟩
  by_cases hki : k = i
  -- The opposite lift of the first spoke lies in the second center.
  · subst k
    apply hsecond.center_empty s
    rw [← hcenter, flip_fibre_axis]
    exact hfirst.paired.spoke_mem b hbi (!t)
  by_cases hkb : k = b
  -- The other endpoint of the second center lies on the first j-spoke.
  · subst k
    apply hsecond.center_empty (!s)
    rw [← flip_fibre_axis d j s, ← hcenter]
    simp only [flip_fibre_comm, flip_flip]
    exact hfirst.paired.spoke_mem j hji t
  rcases (hfirst.partition k).mpr hki with hkA | hkB
  -- The second star's b-spoke requires the forbidden corner on k and j.
  · have hselected : flip (flip (fibreVertex d j s) j) b ∈ C := by
      rw [flip_fibre_axis, flip_fibre_comm]
      exact hsecond.spoke_mem b hbj (!s)
    have hcorner : flip (flip (fibreVertex d j s) j) b =
        fibreVertex (flip (flip c k) j) i t := by
      rw [← hcenter]
      simp only [flip_fibre_comm]
      rw [flip_comm (flip (flip c b) k) j b, flip_comm (flip c b) k b, flip_flip]
    exact hfirst.same_part_empty k j hk (Or.inl ⟨hkA, hj⟩) t (hcorner ▸ hselected)
  -- The second star's i-spoke requires the forbidden corner on b and k.
  · have hselected : flip (fibreVertex d j s) i ∈ C := by
      rw [flip_fibre_comm]
      exact hsecond.spoke_mem i (Ne.symm hji) s
    have hcorner : flip (fibreVertex d j s) i =
        fibreVertex (flip (flip c b) k) i (!t) := by
      rw [← hcenter, flip_fibre_comm, flip_fibre_axis]
    exact hfirst.same_part_empty b k (Ne.symm hkb) (Or.inr ⟨hb, hkB⟩) (!t) (hcorner ▸ hselected)

private theorem directionEdges_ge_twelve_of_mem_left {C : Finset (Q 9)} {i j : Fin 9}
    {c d : Q 9} {A B : Finset (Fin 9)} (hfirst : EightStar C i c A B)
    (hsecond : PairedSpokeStar C j d) (hj : j ∈ A) : 12 ≤ directionEdges C j := by
  let other : Finset (Fin 9) := univ.erase j
  have hB_ne (b : ↥B) : (b : Fin 9) ≠ j :=
    fun h => Finset.disjoint_left.mp hfirst.disjoint hj (h ▸ b.property)
  have hB_axis (b : ↥B) : (b : Fin 9) ≠ i :=
    (hfirst.partition b).mp (Or.inr b.property)
  have hOther_ne (k : ↥other) : (k : Fin 9) ≠ j := (mem_erase.mp k.property).1
  have hcorner (b : ↥B) : ∃ t, fibreVertex (flip (flip c b) j) i t ∈ C :=
    hfirst.cross_occupied b j (Or.inr ⟨b.property, hj⟩)
  choose layer hlayer using hcorner
  let cross (b : ↥B) := edgeBase j (fibreVertex (flip c b) i (layer b))
  let spoke (k : ↥other) := edgeBase j (flip d k)
  have hcross_inj : Function.Injective cross := by
    intro b b' he
    apply Subtype.ext
    by_contra hne
    have hbit := congrArg (fun v : Q 9 => v b) he
    simp only [cross, edgeBase_apply_other _ (hB_ne b),
      fibreVertex_apply_other _ (hB_axis b), BalancedCriticalSpectrum.flip_apply_same,
      flip_apply_other _ hne] at hbit
    cases h : c b <;> simp [h] at hbit
  have hspoke_inj : Function.Injective spoke := by
    intro k k' he
    apply Subtype.ext
    by_contra hne
    have hbit := congrArg (fun v : Q 9 => v k) he
    simp only [spoke, edgeBase_apply_other _ (hOther_ne k),
      BalancedCriticalSpectrum.flip_apply_same, flip_apply_other _ hne] at hbit
    cases h : d k <;> simp [h] at hbit
  let crossEdges := univ.image cross
  let spokeEdges := univ.image spoke
  have hcross_card : crossEdges.card = 4 := by
    simpa only [crossEdges, card_image_of_injective _ hcross_inj, card_univ, Fintype.card_coe]
      using hfirst.card_right
  have hspoke_card : spokeEdges.card = 8 := by
    simp only [spokeEdges, card_image_of_injective _ hspoke_inj, card_univ, Fintype.card_coe,
      other, card_erase_of_mem (mem_univ j), Fintype.card_fin]
  have hdisj : Disjoint crossEdges spokeEdges := by
    apply Finset.disjoint_left.mpr
    intro v hvCross hvSpoke
    obtain ⟨b, _, hb⟩ := mem_image.mp hvCross
    obtain ⟨k, _, hk⟩ := mem_image.mp hvSpoke
    exact cross_edge_ne_spoke hfirst hsecond hj b.property (hOther_ne k) (layer b)
      (hb.trans hk.symm)
  have hsub : crossEdges ∪ spokeEdges ⊆
      C.filter (fun v => v j = false ∧ flip v j ∈ C) := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨b, _, rfl⟩ := mem_image.mp hv
      apply edgeBase_mem (hfirst.paired.spoke_mem b (hB_axis b) (layer b))
      rw [flip_fibre_comm]
      exact hlayer b
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hv
      exact edgeBase_mem (hsecond.spoke_mem k (hOther_ne k) false)
        (hsecond.spoke_mem k (hOther_ne k) true)
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hcross_card, hspoke_card] at hcount
  exact hcount

/-- A full eight-star on `i` and a paired-spoke star on a different axis `j`
force at least twelve selected edges parallel to `j`. -/
theorem directionEdges_ge_twelve_of_two_stars {C : Finset (Q 9)} {i j : Fin 9}
    {c d : Q 9} {A B : Finset (Fin 9)} (hji : j ≠ i)
    (hfirst : EightStar C i c A B) (hsecond : PairedSpokeStar C j d) :
    12 ≤ directionEdges C j := by
  rcases (hfirst.partition j).mpr hji with hj | hj
  · exact directionEdges_ge_twelve_of_mem_left hfirst hsecond hj
  · exact directionEdges_ge_twelve_of_mem_left hfirst.swap hsecond hj

/-- A balanced cubic Q9 component with the two stars has at least seventy-two vertices. -/
theorem card_ge_seventy_two_of_two_stars {C : Finset (Q 9)} {i j : Fin 9}
    {c d : Q 9} {A B : Finset (Fin 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hji : j ≠ i)
    (hfirst : EightStar C i c A B) (hsecond : PairedSpokeStar C j d) :
    72 ≤ C.card := by
  have h12 := directionEdges_ge_twelve_of_two_stars hji hfirst hsecond
  have hcount : 6 * directionEdges C j = C.card := direction_edge_count (d := 3) C hr hb j
  omega

private theorem flip_lift_transverse (i : Fin 9) (t : Bool) (q : Q 8) (a : Fin 8) :
    flip (liftVertex i t q) (i.succAbove a) = liftVertex i t (flip q a) := by
  simpa only [BalancedCriticalSpectrum.flip, liftVertex, Fin.insertNth_apply_succAbove] using
    (Fin.insertNth_update (α := fun _ => Bool) i t a (!q a) q).symm

private theorem fibreVertex_lift_false (i : Fin 9) (q : Q 8) (t : Bool) :
    fibreVertex (liftVertex i false q) i t = liftVertex i t q := by
  cases t
  · rfl
  · simp only [fibreVertex, flip_insert, Bool.not_false]

private theorem occupied_iff_exists_lift {C : Finset (Q 9)} {i : Fin 9}
    {occupied : Q 8 → Bool}
    (hoccupied : ∀ q, occupied q = true ↔
      liftVertex i false q ∈ C ∨ liftVertex i true q ∈ C) (q : Q 8) :
    occupied q = true ↔ ∃ t : Bool, liftVertex i t q ∈ C := by
  rw [hoccupied q]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨t, ht⟩
    cases t
    · exact Or.inl ht
    · exact Or.inr ht

/-- Lift a projected empty center and its eight paired neighbors to Q9. -/
theorem pairedSpokeStar_of_projected {C : Finset (Q 9)} {i : Fin 9}
    {K : Finset (Q 8)} {occupied : Q 8 → Bool} {r : Q 8}
    (hpaired : ∀ q ∈ K, ∀ t, liftVertex i t q ∈ C)
    (hoccupied : ∀ q, occupied q = true ↔
      liftVertex i false q ∈ C ∨ liftVertex i true q ∈ C)
    (hempty : occupied r = false)
    (hspokes : ∀ q, q ∈ K ↔ (hypercube 8).Adj r q) :
    PairedSpokeStar C i (liftVertex i false r) := by
  constructor
  · intro t ht
    rw [fibreVertex_lift_false] at ht
    have h := (occupied_iff_exists_lift hoccupied r).mpr ⟨t, ht⟩
    simp [hempty] at h
  · intro a ha t
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
    rw [flip_lift_transverse, fibreVertex_lift_false]
    exact hpaired _ ((hspokes _).mpr (flip_adj r k)) t

/-- Transport the equality certificate of
`Q9PositiveSpectrumApplication.positive_component_eight_star` to actual
Q9 vertices. Take `K` to be `componentColumns` and `occupied` to be
`projectedOccupied`, with `hpaired` supplied by the paired columns.
The four-four partition is carried to the transverse Q9 axes by `succAbove`. -/
theorem eightStar_of_projected_certificate {C : Finset (Q 9)} {i : Fin 9}
    {K : Finset (Q 8)} {occupied : Q 8 → Bool}
    (hpaired : ∀ q ∈ K, ∀ t, liftVertex i t q ∈ C)
    (hoccupied : ∀ q, occupied q = true ↔
      liftVertex i false q ∈ C ∨ liftVertex i true q ∈ C)
    (hstar : ∃ A B : Finset (Q 8), A.card = 4 ∧ B.card = 4 ∧ Disjoint A B ∧
      A ∪ B = K ∧
      ∃! r : Q 8, occupied r = false ∧
        (∀ q, q ∈ K ↔ (hypercube 8).Adj r q) ∧
        (∀ a b : Fin 8, a ≠ b →
          (occupied (flip (flip r a) b) = true ↔
            (flip r a ∈ A ∧ flip r b ∈ B) ∨ (flip r a ∈ B ∧ flip r b ∈ A)))) :
    ∃ (c : Q 9) (A B : Finset (Fin 9)), EightStar C i c A B := by
  obtain ⟨A, B, hA, hB, hAB, hUnion, r, ⟨hempty, hspokes, hcorners⟩, _⟩ := hstar
  let liftAxes (P : Finset (Q 8)) := (directions P r).map (Fin.succAboveEmb i)
  have hmem (P : Finset (Q 8)) (a : Fin 8) :
      i.succAbove a ∈ liftAxes P ↔ flip r a ∈ P :=
    (mem_map' (Fin.succAboveEmb i)).trans (mem_directions P r a)
  have hne (P : Finset (Q 8)) {a : Fin 9} (ha : a ∈ liftAxes P) : a ≠ i := by
    obtain ⟨k, _, rfl⟩ := mem_map.mp ha
    exact Fin.succAbove_ne i k
  have hcard (P : Finset (Q 8)) (hP : P ⊆ K) : (liftAxes P).card = P.card := by
    dsimp only [liftAxes]
    rw [card_map, directions_card]
    congr 1
    ext q
    simp only [mem_filter]
    exact ⟨And.left, fun hq => ⟨hq, (hspokes q).mp (hP hq)⟩⟩
  have hsubsetA : A ⊆ K := by
    intro q hq
    rw [← hUnion]
    exact mem_union_left B hq
  have hsubsetB : B ⊆ K := by
    intro q hq
    rw [← hUnion]
    exact mem_union_right A hq
  refine ⟨liftVertex i false r, liftAxes A, liftAxes B,
    ⟨pairedSpokeStar_of_projected hpaired hoccupied hempty hspokes,
      (hcard A hsubsetA).trans hA, (hcard B hsubsetB).trans hB, ?_, ?_, ?_, ?_⟩⟩
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (hne A ha)
    exact Finset.disjoint_left.mp hAB ((hmem A k).mp ha) ((hmem B k).mp hb)
  · intro a
    constructor
    · rintro (ha | ha)
      · exact hne A ha
      · exact hne B ha
    · intro ha
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
      have hq : flip r k ∈ K := (hspokes _).mpr (flip_adj r k)
      rw [← hUnion] at hq
      rcases mem_union.mp hq with h | h
      · exact Or.inl ((hmem A k).mpr h)
      · exact Or.inr ((hmem B k).mpr h)
  · intro a b hab hSame t ht
    have ha : a ≠ i := hSame.elim (fun h => hne A h.1) (fun h => hne B h.1)
    have hb : b ≠ i := hSame.elim (fun h => hne A h.2) (fun h => hne B h.2)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hb
    have hkl : k ≠ l := fun h => hab (congrArg (Fin.succAbove i) h)
    simp only [flip_lift_transverse, fibreVertex_lift_false] at ht
    have hCross := (hcorners k l hkl).mp
      ((occupied_iff_exists_lift hoccupied _).mpr ⟨t, ht⟩)
    rcases hSame with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · rcases hCross with ⟨_, hl'⟩ | ⟨hk', _⟩
      · exact Finset.disjoint_left.mp hAB ((hmem A l).mp hl) hl'
      · exact Finset.disjoint_left.mp hAB ((hmem A k).mp hk) hk'
    · rcases hCross with ⟨hk', _⟩ | ⟨_, hl'⟩
      · exact Finset.disjoint_left.mp hAB hk' ((hmem B k).mp hk)
      · exact Finset.disjoint_left.mp hAB hl' ((hmem B l).mp hl)
  · intro a b hCross
    have ha : a ≠ i := hCross.elim (fun h => hne A h.1) (fun h => hne B h.1)
    have hb : b ≠ i := hCross.elim (fun h => hne B h.2) (fun h => hne A h.2)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq ha
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hb
    have hCross' : (flip r k ∈ A ∧ flip r l ∈ B) ∨ (flip r k ∈ B ∧ flip r l ∈ A) :=
      hCross.elim (fun h => Or.inl ⟨(hmem A k).mp h.1, (hmem B l).mp h.2⟩)
        (fun h => Or.inr ⟨(hmem B k).mp h.1, (hmem A l).mp h.2⟩)
    have hkl : k ≠ l := by
      intro h
      subst l
      exact hCross'.elim (fun h => Finset.disjoint_left.mp hAB h.1 h.2)
        (fun h => Finset.disjoint_left.mp hAB h.2 h.1)
    simpa only [flip_lift_transverse, fibreVertex_lift_false] using
      (occupied_iff_exists_lift hoccupied _).mp ((hcorners k l hkl).mpr hCross')

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9TwoStarAxisBound

/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9ExteriorEdgeLiftCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Parallel flips force edges inside the exterior of a balanced cubic support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Count exterior edges by simultaneous flips of interior edges. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeGirth (flip_comm)
open BalancedCubeComponentBoundary (directions directions_card mem_directions regular_directions exterior_even)
open SupportedEigenSaturation (selected_neighbor_card)
open private adjacent_direction_union_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

private def tagged {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (F : α → Finset β) : Finset (α × β) :=
  A.biUnion fun a => (F a).image (Prod.mk a)

private theorem mem_tagged {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A : Finset α} {F : α → Finset β} {p : α × β} :
    p ∈ tagged A F ↔ p.1 ∈ A ∧ p.2 ∈ F p.1 := by
  obtain ⟨a, b⟩ := p
  change (a, b) ∈ tagged A F ↔ a ∈ A ∧ b ∈ F a
  simp only [tagged, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, y, hy, rfl, rfl⟩
    exact ⟨hx, hy⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

private theorem card_tagged {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (F : α → Finset β) : (tagged A F).card = ∑ a ∈ A, (F a).card := by
  have hd : (A : Set α).PairwiseDisjoint (fun a => (F a).image (Prod.mk a)) := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro p hpa hpb
    obtain ⟨u, _, hu⟩ := mem_image.mp hpa
    obtain ⟨v, _, hv⟩ := mem_image.mp hpb
    exact hab (congrArg Prod.fst (hu.trans hv.symm))
  calc
    (tagged A F).card = ∑ a ∈ A, ((F a).image (Prod.mk a)).card := card_biUnion hd
    _ = _ := sum_congr rfl fun a _ =>
      card_image_of_injective (F a) (fun _ _ h => congrArg Prod.snd h)

/-- The exterior neighbors of a support. -/
def exterior (C : Finset (Q 9)) : Finset (Q 9) :=
  (univ \ C).filter fun x => (directions C x).Nonempty

private theorem mem_exterior {C : Finset (Q 9)} {x : Q 9} :
    x ∈ exterior C ↔ x ∉ C ∧ (directions C x).Nonempty := by
  simp only [exterior, mem_filter, mem_sdiff, mem_univ, true_and]

private abbrev Dart := Q 9 × Fin 9

private abbrev darts (A B : Finset (Q 9)) : Finset Dart := tagged A (directions B)

open Classical in
private theorem card_darts {B : Finset (Q 9)} :
    (darts B B).card = 2 * ((hypercube 9).induce (B : Set (Q 9))).edgeFinset.card := by
  classical
  have hdeg (x : ↥B) :
      (directions B x.val).card = ((hypercube 9).induce (B : Set (Q 9))).degree x := by
    rw [directions_card]
    have he : B.filter (fun y => (hypercube 9).Adj x.val y) =
        (hypercube 9).neighborFinset x.val ∩ B := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [he, selected_neighbor_card x.property] <;> rfl
  calc
    (darts B B).card = ∑ x ∈ B, (directions B x).card := card_tagged B (directions B)
    _ = ∑ x : ↥B, (directions B x.val).card :=
      (sum_coe_sort B (fun x => (directions B x).card)).symm
    _ = ∑ x : ↥B, ((hypercube 9).induce (B : Set (Q 9))).degree x :=
      sum_congr rfl fun x _ => hdeg x
    _ = _ := SimpleGraph.sum_degrees_eq_twice_card_edges _

open Classical in
/-- A balanced cubic support with at least forty-eight vertices and forty-five
exterior vertices of degree two into it forces one hundred and four exterior
edges if each of those vertices has two exterior neighbors outside that set. -/
theorem exterior_edges_ge_one_hundred_four
    (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hC : 48 ≤ C.card)
    (A : Finset (Q 9)) (hA : 45 ≤ A.card) (hAB : A ⊆ exterior C)
    (ha₂ : ∀ x ∈ A, (directions C x).card = 2)
    (haRoute : ∀ x ∈ A, 2 ≤ (directions (exterior C \ A) x).card) :
    104 ≤ ((hypercube 9).induce (exterior C : Set (Q 9))).edgeFinset.card := by
  let B := exterior C
  let E := darts B B
  let L := E.filter fun q => q.1 ∈ A ∨ flip q.1 q.2 ∈ A
  let J (q : Dart) := (univ : Finset (Fin 9)) \
    (directions C q.1 ∪ directions C (flip q.1 q.2))
  let K (q : Dart) := directions C q.1 ∩ directions C (flip q.1 q.2)
  have hJ {q : Dart} (hq : q ∈ darts C C) : (J q).card = 4 := by
    rcases q with ⟨x, i⟩
    obtain ⟨hx, hi⟩ := mem_tagged.mp hq
    have hu := adjacent_direction_union_card hr hb hx ((mem_directions C x i).mp hi)
    change ((univ : Finset (Fin 9)) \ (directions C x ∪ directions C (flip x i))).card = 4
    rw [card_univ_sdiff, Fintype.card_fin, hu]
  -- Translate each interior dart along an axis missing from both endpoints.
  have hlifts : 12 * C.card ≤ (tagged E K).card := by
    have hInterior : (darts C C).card = C.card * 3 :=
      (card_tagged C (directions C)).trans
        (sum_const_nat fun _ hx => regular_directions C hr hx)
    have hleft : (tagged (darts C C) J).card = 12 * C.card := by
      calc
        (tagged (darts C C) J).card = ∑ q ∈ darts C C, (J q).card :=
          card_tagged (darts C C) J
        _ = (darts C C).card * 4 := sum_const_nat fun _ hq => hJ hq
        _ = 12 * C.card := by
          rw [hInterior]
          omega
    rw [← hleft]
    let parallelFlip (q : Dart × Fin 9) : Dart × Fin 9 :=
      ((flip q.1.1 q.2, q.1.2), q.2)
    have hlift : Function.Involutive parallelFlip := by
      rintro ⟨⟨x, i⟩, j⟩
      change ((flip (flip x j) j, i), j) = ((x, i), j)
      rw [BalancedCriticalSpectrum.flip_flip]
    apply card_le_card_of_injOn parallelFlip
    · rintro ⟨⟨x, i⟩, j⟩ hq
      change ((x, i), j) ∈ tagged (darts C C) J at hq
      obtain ⟨hxi, hj⟩ := mem_tagged.mp hq
      obtain ⟨hx, hi⟩ := mem_tagged.mp hxi
      have hxiC := (mem_directions C x i).mp hi
      have hnot := (mem_sdiff.mp hj).2
      have hnot₁ : flip x j ∉ C := fun h => hnot (mem_union_left _ ((mem_directions C x j).mpr h))
      have hnot₂ : flip (flip x i) j ∉ C := fun h =>
        hnot (mem_union_right _ ((mem_directions C (flip x i) j).mpr h))
      have hback₁ : j ∈ directions C (flip x j) :=
        (mem_directions C (flip x j) j).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)
      have hback₂ : j ∈ directions C (flip (flip x i) j) :=
        (mem_directions C (flip (flip x i) j) j).mpr
          (by simpa only [BalancedCriticalSpectrum.flip_flip] using hxiC)
      have hB₁ : flip x j ∈ B := mem_exterior.mpr ⟨hnot₁, ⟨j, hback₁⟩⟩
      have hB₂ : flip (flip x i) j ∈ B :=
        mem_exterior.mpr ⟨hnot₂, ⟨j, hback₂⟩⟩
      have hcomm : flip (flip x j) i = flip (flip x i) j := flip_comm x j i
      have hB₂' : flip (flip x j) i ∈ B := by
        rw [hcomm]
        exact hB₂
      change ((flip x j, i), j) ∈ tagged E K
      refine mem_tagged.mpr ⟨mem_tagged.mpr ⟨hB₁, (mem_directions B (flip x j) i).mpr hB₂'⟩, ?_⟩
      change j ∈ directions C (flip x j) ∩ directions C (flip (flip x j) i)
      rw [hcomm]
      exact mem_inter.mpr ⟨hback₁, hback₂⟩
    · exact hlift.injective.injOn
  -- Every edge from A to its exterior complement contributes both orientations.
  have hL : 4 * A.card ≤ L.card := by
    let Out := darts A (B \ A)
    let rev (q : Dart) : Dart := (flip q.1 q.2, q.2)
    have hrev : Function.Involutive rev := by
      rintro ⟨x, i⟩
      change (flip (flip x i) i, i) = (x, i)
      rw [BalancedCriticalSpectrum.flip_flip]
    have hout : 2 * A.card ≤ Out.card := by
      rw [card_tagged]
      calc
        _ = ∑ _x ∈ A, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := sum_le_sum fun x hx => haRoute x hx
    have hdis : Disjoint Out (Out.image rev) := by
      apply disjoint_left.mpr
      intro p hp hpr
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hpr
      obtain ⟨_, hqT⟩ := mem_tagged.mp hq
      obtain ⟨hpA, _⟩ := mem_tagged.mp hp
      exact (mem_sdiff.mp ((mem_directions (B \ A) q.1 q.2).mp hqT)).2 hpA
    have hsub : Out ∪ Out.image rev ⊆ L := by
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨hpa, hpT⟩ := mem_tagged.mp hp
        have hpB := (mem_sdiff.mp ((mem_directions (B \ A) p.1 p.2).mp hpT)).1
        exact mem_filter.mpr ⟨mem_tagged.mpr ⟨hAB hpa, (mem_directions B p.1 p.2).mpr hpB⟩, Or.inl hpa⟩
      · obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
        obtain ⟨hqa, hqT⟩ := mem_tagged.mp hq
        have hqB := (mem_sdiff.mp ((mem_directions (B \ A) q.1 q.2).mp hqT)).1
        have hback : flip (rev q).1 (rev q).2 ∈ A := by
          simpa only [rev, BalancedCriticalSpectrum.flip_flip] using hqa
        exact mem_filter.mpr ⟨mem_tagged.mpr ⟨hqB,
          (mem_directions B (rev q).1 (rev q).2).mpr (hAB hback)⟩, Or.inr hback⟩
    have hbound := card_le_card hsub
    rw [card_union_of_disjoint hdis, card_image_of_injective _ hrev.injective] at hbound
    omega
  have hcap {q : Dart} (hq : q ∈ E) : (K q).card ≤ 8 := by
    obtain ⟨hqB, _⟩ := mem_tagged.mp hq
    obtain ⟨n, hn⟩ := exterior_even C hr hb q.1 (mem_exterior.mp hqB).1
    have h9 : (directions C q.1).card ≤ 9 := by
      simpa only [Fintype.card_fin] using (directions C q.1).card_le_univ
    have hlo := card_le_card (show K q ⊆ directions C q.1 from inter_subset_left)
    omega
  have hcapL {q : Dart} (hq : q ∈ L) : (K q).card ≤ 2 := by
    rcases (mem_filter.mp hq).2 with ha | ha
    · exact (card_le_card (show K q ⊆ directions C q.1 from inter_subset_left)).trans_eq
        (ha₂ q.1 ha)
    · exact (card_le_card (show K q ⊆ directions C (flip q.1 q.2) from inter_subset_right)).trans_eq
        (ha₂ (flip q.1 q.2) ha)
  have hs : L ⊆ E := filter_subset _ _
  have hsum := sum_sdiff (f := fun q => (K q).card) hs
  have hhigh : ∑ q ∈ E \ L, (K q).card ≤ 8 * (E \ L).card := by
    calc
      _ ≤ ∑ _q ∈ E \ L, (8 : ℕ) := sum_le_sum fun q hq => hcap (mem_sdiff.mp hq).1
      _ = _ := by simp [Nat.mul_comm]
  have hlow : ∑ q ∈ L, (K q).card ≤ 2 * L.card := by
    calc
      _ ≤ ∑ _q ∈ L, (2 : ℕ) := sum_le_sum fun q hq => hcapL hq
      _ = _ := by simp [Nat.mul_comm]
  have hc := card_sdiff_of_subset hs
  have hle := card_le_card hs
  rw [card_tagged E K] at hlifts
  have hE : E.card = 2 * ((hypercube 9).induce (B : Set (Q 9))).edgeFinset.card :=
    card_darts (B := B)
  change 104 ≤ ((hypercube 9).induce (B : Set (Q 9))).edgeFinset.card
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount

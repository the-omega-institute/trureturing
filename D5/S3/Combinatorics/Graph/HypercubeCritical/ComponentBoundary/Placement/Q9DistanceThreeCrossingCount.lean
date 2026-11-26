/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeCrossingCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Unshared distance-three contacts force at least 45 active rows per side and 162 crossing edges. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeActiveBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumContactDirectionChart

/-! Count active exterior vertices and crossing darts in the unshared distance-three case. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeCrossingCount

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (directions mem_directions flip_injective)
open Q9ExteriorEdgeLiftCount (exterior)
open Q9DistanceThreeUnsharedDirections (directionOrigin unsharedContactAxes
  axes_and_partition_of_unshared_contacts)
open Q9MinimumContactDirectionChart (eighteen_endpoints_of_fixed_direction_origin)
open private differingAxes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_flip_left from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private differingAxes_symm differingAxes_right_inj from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactComplement

open Q9DistanceThreeActiveBoundary (active)

private abbrev contacts (D : Finset (Q 9)) (x : Q 9) : Finset (Q 9) :=
  D.filter fun y => hammingDist x y = 3

private abbrev near (C D : Finset (Q 9)) : Finset (Q 9) :=
  C.filter fun x => (contacts D x).Nonempty

private abbrev Separated (C D : Finset (Q 9)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y

private abbrev Unshared (C D : Finset (Q 9)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 → Disjoint (directions C x) (directions D y)

private theorem mem_contactAxes {D : Finset (Q 9)} {x : Q 9} {i : Fin 9} :
    i ∈ unsharedContactAxes D x ↔ ∃ y ∈ contacts D x, i ∈ differingAxes x y := by
  unfold unsharedContactAxes
  constructor
  · rintro h
    obtain ⟨y, hy, hi⟩ := mem_biUnion.mp h
    obtain ⟨hyD, hd⟩ := mem_filter.mp hy
    exact ⟨y, mem_filter.mpr ⟨hyD, by rwa [hammingDist_comm]⟩,
      differingAxes_symm y x ▸ hi⟩
  · rintro ⟨y, hy, hi⟩
    obtain ⟨hyD, hd⟩ := mem_filter.mp hy
    exact mem_biUnion.mpr ⟨y, mem_filter.mpr ⟨hyD, by rwa [hammingDist_comm]⟩,
      differingAxes_symm x y ▸ hi⟩

private theorem dist_flip_of_mem {x y : Q 9} {i : Fin 9} (hi : i ∈ differingAxes x y) :
    hammingDist (flip x i) y + 1 = hammingDist x y := by
  change (differingAxes (flip x i) y).card + 1 = (differingAxes x y).card
  rw [diff_flip_left, ite_eq_left hi, card_erase_add_one hi]

private theorem dist_flip_of_notMem {x y : Q 9} {i : Fin 9} (hi : i ∉ differingAxes x y) :
    hammingDist (flip x i) y = hammingDist x y + 1 := by
  change (differingAxes (flip x i) y).card = (differingAxes x y).card + 1
  rw [diff_flip_left, ite_eq_right hi, card_insert_of_notMem hi]

private theorem exterior_of_neighbor {C : Finset (Q 9)} {z : Q 9} {i : Fin 9}
    (hz : z ∉ C) (hi : flip z i ∈ C) : z ∈ exterior C :=
  mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, hz⟩, ⟨i, (mem_directions C z i).mpr hi⟩⟩

private theorem active_of_crossing {C D : Finset (Q 9)} {z : Q 9} {i : Fin 9}
    (hz : z ∈ exterior C) (hw : flip z i ∈ exterior D) : z ∈ active C D :=
  mem_filter.mpr ⟨hz, ⟨i, (mem_directions (exterior D) z i).mpr hw⟩⟩

private theorem crossing_of_contact {C D : Finset (Q 9)} (hsep : Separated C D)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hd : hammingDist x y = 3)
    {i j : Fin 9} (hi : i ∈ differingAxes x y) (hj : j ∈ (differingAxes x y).erase i) :
    flip x i ∈ exterior C ∧ flip (flip x i) j ∈ exterior D ∧
      hammingDist (flip (flip x i) j) y = 1 := by
  have hzDist : hammingDist (flip x i) y = 2 := by
    have := dist_flip_of_mem hi
    omega
  have hj' : j ∈ differingAxes (flip x i) y := by
    rwa [diff_flip_left, ite_eq_left hi]
  have hwDist : hammingDist (flip (flip x i) j) y = 1 := by
    have := dist_flip_of_mem hj'
    omega
  refine ⟨exterior_of_neighbor (i := i) ?_ (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx), ?_, hwDist⟩
  · intro hz
    have hmin := hsep _ hz y hy
    omega
  · obtain ⟨k, hk⟩ := adjacent_exists_flip (n := 9) hwDist
    refine exterior_of_neighbor (i := k) ?_ (hk ▸ hy)
    intro hw
    have h := hammingDist_triangle x (flip x i) (flip (flip x i) j)
    have h₁ : hammingDist x (flip x i) = 1 := flip_adj x i
    have h₂ : hammingDist (flip x i) (flip (flip x i) j) = 1 := flip_adj (flip x i) j
    have hmin := hsep x hx _ hw
    omega

private theorem contact_of_midpoint_neighbor {x y : Q 9} {i j : Fin 9}
    (hmin : 3 ≤ hammingDist x y) (hw : hammingDist (flip (flip x i) j) y = 1) :
    hammingDist x y = 3 ∧ i ∈ differingAxes x y ∧ j ∈ differingAxes x y := by
  have hstep : hammingDist (flip x i) (flip (flip x i) j) = 1 := flip_adj (flip x i) j
  have htri := hammingDist_triangle (flip x i) (flip (flip x i) j) y
  have hi : i ∈ differingAxes x y := by
    by_contra hn
    have h := dist_flip_of_notMem hn
    omega
  have hfirst := dist_flip_of_mem hi
  have hj : j ∈ differingAxes (flip x i) y := by
    by_contra hn
    have h := dist_flip_of_notMem hn
    omega
  rw [diff_flip_left, ite_eq_left hi] at hj
  exact ⟨by omega, hi, mem_of_mem_erase hj⟩

/-- The two neighbors of a crossing midpoint are the two contacts extending its pair. -/
private theorem contact_pair_card {C D : Finset (Q 9)} (hsep : Separated C D)
    (hdegreeD : ∀ w ∈ active D C, (directions D w).card = 2)
    {x : Q 9} (hx : x ∈ C) {P : Finset (Fin 9)} (hPcard : P.card = 2)
    {y : Q 9} (hy : y ∈ contacts D x) (hPy : P ⊆ differingAxes x y) :
    ((contacts D x).filter fun v => P ⊆ differingAxes x v).card = 2 := by
  obtain ⟨i, j, hij, hP⟩ := card_eq_two.mp hPcard
  have hiP : i ∈ P := by simp [hP]
  have hjP : j ∈ P := by simp [hP]
  obtain ⟨hyD, hxy⟩ := mem_filter.mp hy
  obtain ⟨hz, hw, _⟩ := crossing_of_contact hsep hx hyD hxy (hPy hiP)
    (mem_erase.mpr ⟨hij.symm, hPy hjP⟩)
  let w := flip (flip x i) j
  have hwActive : w ∈ active D C :=
    active_of_crossing (i := j) hw (by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hz)
  have heq : (contacts D x).filter (fun v => P ⊆ differingAxes x v) =
      (directions D w).image (flip w) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvClose, hPv⟩ := mem_filter.mp hv
      obtain ⟨hvD, hxv⟩ := mem_filter.mp hvClose
      obtain ⟨_, _, hdist⟩ := crossing_of_contact hsep hx hvD hxv (hPv hiP)
        (mem_erase.mpr ⟨hij.symm, hPv hjP⟩)
      obtain ⟨k, hk⟩ := adjacent_exists_flip (n := 9) hdist
      exact mem_image.mpr ⟨k, (mem_directions D w k).mpr (hk ▸ hvD), hk.symm⟩
    · intro hv
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hv
      have hvD := (mem_directions D w k).mp hk
      obtain ⟨hd, hi, hj⟩ := contact_of_midpoint_neighbor (i := i) (j := j)
        (hsep x hx _ hvD) (flip_adj w k)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨hvD, hd⟩, ?_⟩
      rw [hP, insert_subset_iff, singleton_subset_iff]
      exact ⟨hi, hj⟩
  rw [heq, card_image_of_injective _ (flip_injective w)]
  exact hdegreeD w hwActive

private theorem sum_card_filter_swap {α β : Type*} (A : Finset α) (B : Finset β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    (∑ a ∈ A, (B.filter (p a)).card) = ∑ b ∈ B, (A.filter fun a => p a b).card := by
  simpa only [bipartiteAbove, bipartiteBelow] using
    (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow p (s := A) (t := B))

private theorem contacts_card_ge_six {C D : Finset (Q 9)} (hsep : Separated C D)
    (hdegreeD : ∀ w ∈ active D C, (directions D w).card = 2)
    {x : Q 9} (hx : x ∈ C) (haxes : 5 ≤ (unsharedContactAxes D x).card) :
    6 ≤ (contacts D x).card := by
  let B := contacts D x
  let A := unsharedContactAxes D x
  have hsize (y : Q 9) (hy : y ∈ B) : (differingAxes x y).card = 3 := (mem_filter.mp hy).2
  -- If an axis occurs in only two contacts, both contacts must contain every pair through it.
  have haxisCard (i : Fin 9) (hi : i ∈ A) :
      3 ≤ (B.filter fun y => i ∈ differingAxes x y).card := by
    let L := B.filter fun y => i ∈ differingAxes x y
    obtain ⟨y, hy, hiy⟩ := mem_contactAxes.mp hi
    change 3 ≤ L.card
    by_contra hsmall
    have hfaceCard (j : Fin 9) (hj : j ∈ (differingAxes x y).erase i) :
        (B.filter fun v => ({i, j} : Finset (Fin 9)) ⊆ differingAxes x v).card = 2 := by
      have hp : ({i, j} : Finset (Fin 9)) ⊆ differingAxes x y :=
        insert_subset_iff.mpr ⟨hiy, singleton_subset_iff.mpr (mem_of_mem_erase hj)⟩
      exact contact_pair_card hsep hdegreeD hx (card_pair (ne_of_mem_erase hj).symm) hy hp
    have hface (j : Fin 9) (hj : j ∈ (differingAxes x y).erase i) :
        (B.filter fun v => ({i, j} : Finset (Fin 9)) ⊆ differingAxes x v) = L := by
      apply eq_of_subset_of_card_le
      · intro v hv
        obtain ⟨hvB, hvP⟩ := mem_filter.mp hv
        exact mem_filter.mpr ⟨hvB, hvP (mem_insert_self _ _)⟩
      · rw [hfaceCard j hj]
        omega
    have hrest : ((differingAxes x y).erase i).card = 2 := by
      rw [card_erase_of_mem hiy, hsize y hy]
    obtain ⟨j, hj⟩ := card_pos.mp (show 0 < ((differingAxes x y).erase i).card by omega)
    have hL : L.card = 2 := by
      rw [← hface j hj]
      exact hfaceCard j hj
    have hyL : y ∈ L := mem_filter.mpr ⟨hy, hiy⟩
    have hErase := card_erase_add_one hyL
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < (L.erase y).card by omega)
    have hvL := mem_of_mem_erase hv
    have hsub : differingAxes x y ⊆ differingAxes x v := by
      intro k hk
      by_cases hki : k = i
      · subst k
        exact (mem_filter.mp hvL).2
      · have hvP : v ∈ B.filter (fun u => ({i, k} : Finset (Fin 9)) ⊆ differingAxes x u) := by
          rw [hface k (mem_erase.mpr ⟨hki, hk⟩)]
          exact hvL
        exact (mem_filter.mp hvP).2 (by simp)
    have hsame := eq_of_subset_of_card_le hsub (by
      rw [hsize v (mem_filter.mp hvL).1, hsize y hy])
    exact (ne_of_mem_erase hv) (differingAxes_right_inj hsame).symm
  have haxisSum : 3 * A.card ≤ 3 * B.card := by
    calc
      _ = ∑ _i ∈ A, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ A, (B.filter fun y => i ∈ differingAxes x y).card :=
        sum_le_sum haxisCard
      _ = ∑ y ∈ B, (A.filter fun i => i ∈ differingAxes x y).card :=
        sum_card_filter_swap A B (fun i y => i ∈ differingAxes x y)
      _ = 3 * B.card := by
        have hfiber (y : Q 9) (hy : y ∈ B) :
            (A.filter fun i => i ∈ differingAxes x y) = differingAxes x y := by
          ext i
          exact mem_filter.trans ⟨And.right, fun hi => ⟨mem_contactAxes.mpr ⟨y, hy, hi⟩, hi⟩⟩
        rw [sum_const_nat (m := 3) (fun y hy => by rw [hfiber y hy, hsize y hy]), Nat.mul_comm]
  let P := B.biUnion fun y => (differingAxes x y).powersetCard 2
  -- There are three pairs per contact and two contacts per occurring pair.
  have hpairSum : 3 * B.card = 2 * P.card := by
    calc
      _ = ∑ y ∈ B, (P.filter fun R => R ∈ (differingAxes x y).powersetCard 2).card := by
        have hfiber (y : Q 9) (hy : y ∈ B) :
            (P.filter fun R => R ∈ (differingAxes x y).powersetCard 2) =
              (differingAxes x y).powersetCard 2 := by
          ext R
          exact mem_filter.trans ⟨And.right, fun hR => ⟨mem_biUnion.mpr ⟨y, hy, hR⟩, hR⟩⟩
        rw [sum_const_nat (m := 3) (fun y hy => by
          rw [hfiber y hy, card_powersetCard, hsize y hy]; decide), Nat.mul_comm]
      _ = ∑ R ∈ P, (B.filter fun y => R ∈ (differingAxes x y).powersetCard 2).card :=
        sum_card_filter_swap B P (fun y R => R ∈ (differingAxes x y).powersetCard 2)
      _ = 2 * P.card := by
        have hfiber (R : Finset (Fin 9)) (hR : R ∈ P) :
            (B.filter fun y => R ∈ (differingAxes x y).powersetCard 2).card = 2 := by
          obtain ⟨y, hy, hRy⟩ := mem_biUnion.mp hR
          obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hRy
          simpa only [mem_powersetCard, hcard, eq_self, and_true] using
            contact_pair_card hsep hdegreeD hx hcard hy hsub
        rw [sum_const_nat hfiber, Nat.mul_comm]
  change 6 ≤ B.card
  change 5 ≤ A.card at haxes
  omega

open private tagged mem_tagged card_tagged from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ExteriorEdgeLiftCount

private theorem active_card_of_near {C D : Finset (Q 9)} (hsep : Separated C D)
    (hdegreeC : ∀ z ∈ active C D, (directions C z).card = 2)
    (hnear : 18 ≤ (near C D).card)
    (haxes : ∀ x ∈ near C D, 5 ≤ (unsharedContactAxes D x).card) :
    45 ≤ (active C D).card := by
  have hinc : (tagged (near C D) (unsharedContactAxes D)).card ≤
      (tagged (active C D) (directions C)).card := by
    let f (p : Q 9 × Fin 9) : Q 9 × Fin 9 := (flip p.1 p.2, p.2)
    apply card_le_card_of_injOn f
    · rintro ⟨x, i⟩ hp
      obtain ⟨hx, hi⟩ := mem_tagged.mp hp
      obtain ⟨y, hy, hiy⟩ := mem_contactAxes.mp hi
      obtain ⟨hyD, hd⟩ := mem_filter.mp hy
      have ht : (differingAxes x y).card = 3 := hd
      change i ∈ differingAxes x y at hiy
      have he : ((differingAxes x y).erase i).card + 1 = (differingAxes x y).card :=
        card_erase_add_one hiy
      obtain ⟨j, hj⟩ := card_pos.mp (show 0 < ((differingAxes x y).erase i).card by omega)
      obtain ⟨hz, hw, _⟩ := crossing_of_contact hsep (mem_filter.mp hx).1 hyD hd hiy hj
      have hback : i ∈ directions C (flip x i) :=
        (mem_directions C _ i).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using (mem_filter.mp hx).1)
      exact mem_tagged.mpr ⟨active_of_crossing hz hw, hback⟩
    · rintro ⟨x, i⟩ _ ⟨y, j⟩ _ he
      change (flip x i, i) = (flip y j, j) at he
      obtain ⟨hxy, hij⟩ := Prod.mk.inj he
      subst j
      have h : x = y := by simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun z : Q 9 => BalancedCriticalSpectrum.flip z i) hxy
      subst y
      rfl
  have hcount : 5 * (near C D).card ≤ (tagged (near C D) (unsharedContactAxes D)).card := by
    rw [card_tagged]
    calc
      _ = ∑ _x ∈ near C D, (5 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum haxes
  rw [card_tagged (active C D) (directions C), sum_const_nat hdegreeC] at hinc
  omega

private theorem crossing_darts_of_near {C D : Finset (Q 9)} (hsep : Separated C D)
    (hdegreeC : ∀ z ∈ active C D, (directions C z).card = 2)
    (hdegreeD : ∀ w ∈ active D C, (directions D w).card = 2)
    (hnear : 18 ≤ (near C D).card)
    (haxes : ∀ x ∈ near C D, 5 ≤ (unsharedContactAxes D x).card) :
    162 ≤ ∑ z ∈ exterior C, (directions (exterior D) z).card := by
  let pairs := tagged (near C D) (contacts D)
  let orders (p : Q 9 × Q 9) := tagged (differingAxes p.1 p.2) fun i =>
    (differingAxes p.1 p.2).erase i
  let darts := tagged (exterior C) (directions (exterior D))
  let endpoints (d : Q 9 × Fin 9) := (directions C d.1) ×ˢ
    ((directions D (flip d.1 d.2)).image (flip (flip d.1 d.2)))
  have hpairs : 6 * (near C D).card ≤ pairs.card := by
    change 6 * (near C D).card ≤ (tagged (near C D) (contacts D)).card
    rw [card_tagged]
    calc
      _ = ∑ _x ∈ near C D, (6 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun x hx =>
        contacts_card_ge_six hsep hdegreeD (mem_filter.mp hx).1 (haxes x hx)
  have horders : (tagged pairs orders).card = pairs.card * 6 := by
    rw [card_tagged]
    apply sum_const_nat
    rintro ⟨x, y⟩ hp
    have hy := (mem_tagged.mp (show (x, y) ∈ tagged (near C D) (contacts D) from hp)).2
    have ht : (differingAxes x y).card = 3 := (mem_filter.mp hy).2
    change (tagged (differingAxes x y) (fun i => (differingAxes x y).erase i)).card = 6
    rw [card_tagged, sum_const_nat (m := 2) (fun i hi => by rw [card_erase_of_mem hi, ht])]
    simp [ht]
  have hendpoints : (tagged darts endpoints).card =
      (∑ z ∈ exterior C, (directions (exterior D) z).card) * 4 := by
    calc
      _ = darts.card * 4 := by
        rw [card_tagged]
        apply sum_const_nat
        rintro ⟨z, j⟩ hd
        obtain ⟨hz, hj⟩ :=
          mem_tagged.mp (show (z, j) ∈ tagged (exterior C) (directions (exterior D)) from hd)
        have hw := (mem_directions (exterior D) z j).mp hj
        have hzA := active_of_crossing hz hw
        have hwA := active_of_crossing (i := j) hw (by simpa only [BalancedCriticalSpectrum.flip_flip] using hz)
        change ((directions C z) ×ˢ
          ((directions D (flip z j)).image (flip (flip z j)))).card = 4
        rw [card_product, card_image_of_injective _ (flip_injective (flip z j)),
          hdegreeC z hzA, hdegreeD (flip z j) hwA]
      _ = _ := by dsimp only [darts]; rw [card_tagged]
  have hinc : (tagged pairs orders).card ≤ (tagged darts endpoints).card := by
    -- Store the middle dart, the axis of the first step, and the final endpoint.
    let f (p : (Q 9 × Q 9) × (Fin 9 × Fin 9)) : (Q 9 × Fin 9) × (Fin 9 × Q 9) :=
      ((flip p.1.1 p.2.1, p.2.2), (p.2.1, p.1.2))
    apply card_le_card_of_injOn f
    · rintro ⟨⟨x, y⟩, ⟨i, j⟩⟩ hp
      obtain ⟨hpair, horder⟩ := mem_tagged.mp hp
      obtain ⟨hx, hy⟩ :=
        mem_tagged.mp (show (x, y) ∈ tagged (near C D) (contacts D) from hpair)
      obtain ⟨hi, hj⟩ := mem_tagged.mp (show
        (i, j) ∈ tagged (differingAxes x y) (fun a => (differingAxes x y).erase a) from horder)
      obtain ⟨hyD, hd⟩ := mem_filter.mp hy
      have hxC := (mem_filter.mp hx).1
      obtain ⟨hz, hw, hwy⟩ := crossing_of_contact hsep hxC hyD hd hi hj
      have hdart : (flip x i, j) ∈ darts :=
        mem_tagged.mpr ⟨hz, (mem_directions (exterior D) _ j).mpr hw⟩
      let w := flip (flip x i) j
      obtain ⟨k, hk⟩ := adjacent_exists_flip (n := 9) hwy
      have hback : i ∈ directions C (flip x i) :=
        (mem_directions C _ i).mpr (by simpa only [BalancedCriticalSpectrum.flip_flip] using hxC)
      have hendpoint : y ∈ (directions D w).image (flip w) :=
        mem_image.mpr ⟨k, (mem_directions D w k).mpr (hk ▸ hyD), hk.symm⟩
      exact mem_tagged.mpr ⟨hdart, mem_product.mpr ⟨hback, hendpoint⟩⟩
    · rintro ⟨⟨x, y⟩, ⟨i, j⟩⟩ _ ⟨⟨x', y'⟩, ⟨i', j'⟩⟩ _ h
      change ((flip x i, j), (i, y)) = ((flip x' i', j'), (i', y')) at h
      obtain ⟨hzw, hiy⟩ := Prod.mk.inj h
      obtain ⟨hi, hy⟩ := Prod.mk.inj hiy
      obtain ⟨hx, hj⟩ := Prod.mk.inj hzw
      subst i'
      subst y'
      subst j'
      have hxx : x = x' := by simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun z : Q 9 => BalancedCriticalSpectrum.flip z i) hx
      subst x'
      rfl
  rw [horders, hendpoints] at hinc
  omega

open Classical in
private theorem near_card_ge_eighteen {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hsep : Separated C D) (hdis : Unshared C D)
    {y : Q 9} (hy : y ∈ near D C) : 18 ≤ (near D C).card := by
  obtain ⟨hyD, x, hx⟩ := mem_filter.mp hy
  obtain ⟨hxC, hd⟩ := mem_filter.mp hx
  have hxy : hammingDist x y = 3 := by rwa [hammingDist_comm]
  refine (eighteen_endpoints_of_fixed_direction_origin hrC hrD hbC hbD hsep hdis
    (directionOrigin D y) ⟨y, hyD, rfl, x, hxC, hxy⟩).trans ?_
  apply card_le_card
  intro v hv
  obtain ⟨hvD, _, u, huC, huv⟩ := mem_filter.mp hv
  exact mem_filter.mpr ⟨hvD, ⟨u, mem_filter.mpr ⟨huC, by rwa [hammingDist_comm]⟩⟩⟩

open Classical in
private theorem near_axes_ge_five {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hsep : Separated C D) (hdis : Unshared C D)
    (y : Q 9) (hy : y ∈ near D C) : 5 ≤ (unsharedContactAxes C y).card := by
  obtain ⟨hyD, x, hx⟩ := mem_filter.mp hy
  obtain ⟨hxC, hd⟩ := mem_filter.mp hx
  exact (axes_and_partition_of_unshared_contacts hrC hrD hbC hbD hsep hyD
    ⟨x, hxC, by rwa [hammingDist_comm]⟩ (fun v hv hvy => hdis v hv y hyD hvy)).1

open Classical in
/-- Each exterior has at least forty-five active vertices. Counting darts from
the first exterior to the second gives at least one hundred and sixty-two. -/
theorem active_card_and_crossing_darts
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    (hne : ∃ x ∈ C, ∃ y ∈ D, hammingDist x y = 3)
    (hdegreeC : ∀ z ∈ active C D, (directions C z).card = 2)
    (hdegreeD : ∀ w ∈ active D C, (directions D w).card = 2) :
    45 ≤ (active C D).card ∧ 45 ≤ (active D C).card ∧
      162 ≤ ∑ z ∈ exterior C, (directions (exterior D) z).card := by
  have hsep' : Separated D C := fun y hy x hx => by
    rw [hammingDist_comm]
    exact hsep x hx y hy
  have hdis' : Unshared D C := fun y hy x hx hd =>
    (hdis x hx y hy (by rwa [hammingDist_comm])).symm
  obtain ⟨x, hx, y, hy, hd⟩ := hne
  have hxNear : x ∈ near C D := mem_filter.mpr ⟨hx, ⟨y, mem_filter.mpr ⟨hy, hd⟩⟩⟩
  have hyNear : y ∈ near D C :=
    mem_filter.mpr ⟨hy, ⟨x, mem_filter.mpr ⟨hx, by rwa [hammingDist_comm]⟩⟩⟩
  have hnearC := near_card_ge_eighteen hrD hrC hbD hbC hsep' hdis' hxNear
  have hnearD := near_card_ge_eighteen hrC hrD hbC hbD hsep hdis hyNear
  have haxesC := near_axes_ge_five hrD hrC hbD hbC hsep' hdis'
  have haxesD := near_axes_ge_five hrC hrD hbC hbD hsep hdis
  exact ⟨active_card_of_near hsep hdegreeC hnearC haxesC,
    active_card_of_near hsep' hdegreeD hnearD haxesD,
    crossing_darts_of_near hsep hdegreeC hdegreeD hnearC haxesC⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeCrossingCount

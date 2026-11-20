/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FivefoldCoverDynamics
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FivefoldCoverDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The small-side corner switches across a nine-cube exterior edge with coverage (3, 2). -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Batteries.Tactic.OpenPrivate

/-! A fivefold-covered exterior edge preserves the small-side direction pair
and switches membership of the corner in that pair. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FivefoldCoverDynamics

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeComponentBoundary (directions exterior_even neighbor_card_add_le_six
  regular_directions)
open BalancedCubeGirth (no_selected_square)
open private flip_comm from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions_card mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

open Classical in
private theorem endpoint_cards {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {x : Q 9} (hxC : x ∉ C) (hxD : x ∉ D)
    (hC : 3 ≤ (directions C x).card) (hD : 2 ≤ (directions D x).card) :
    (directions C x).card = 4 ∧ (directions D x).card = 2 := by
  have hsum : (directions C x).card + (directions D x).card ≤ 6 := by
    rw [directions_card C x, directions_card D x]
    exact neighbor_card_add_le_six C D hrC hrD hbC hbD hdisj hcross x hxC hxD
      (by rw [← directions_card]; omega) (by rw [← directions_card]; omega)
  obtain ⟨a, ha⟩ := exterior_even C hrC hbC x hxC
  obtain ⟨b, hb⟩ := exterior_even D hrD hbD x hxD
  omega

private theorem directions_disjoint {C D : Finset (Q 9)} (hdisj : Disjoint C D) (x : Q 9) :
    Disjoint (directions C x) (directions D x) := by
  refine Finset.disjoint_left.mpr fun r hrC hrD => ?_
  exact Finset.disjoint_left.mp hdisj ((mem_directions C x r).mp hrC)
    ((mem_directions D x r).mp hrD)

open Classical in
private theorem directions_eq_unoccupied_of_corner_absent {C D : Finset (Q 9)}
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    {x : Q 9} {i j : Fin 9} (hxD : x ∉ D)
    (hC : (directions C x).card = 4) (hD : (directions D x).card = 2)
    (hpair : directions D x = {i, j}) (hcorner : flip (flip x i) j ∉ D) :
    directions D (flip x i) = Finset.univ \ (directions C x ∪ directions D x) := by
  have hi : flip x i ∈ D := (mem_directions D x i).mp (by rw [hpair]; simp)
  have hfree : (Finset.univ \ (directions C x ∪ directions D x)).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_union_of_disjoint (directions_disjoint hdisj x), hC, hD]
  apply Finset.eq_of_subset_of_card_le _ (by rw [hfree, regular_directions D hrD hi])
  intro r hr
  have hrSelected : flip (flip x i) r ∈ D := (mem_directions D (flip x i) r).mp hr
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => ?_⟩
  rcases Finset.mem_union.mp h with hrC | hrPair
  · apply hcross _ ((mem_directions C x r).mp hrC) _ hrSelected
    rw [flip_comm x i r]
    exact flip_adj (flip x r) i
  · rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hrPair
    rcases hrPair with rfl | rfl
    · exact hxD (by simpa only [BalancedCriticalSpectrum.flip_flip] using hrSelected)
    · exact hcorner hrSelected

private theorem no_shared_continuation {D : Finset (Q 9)} (hbD : IsBalanced D)
    {v : Q 9} {i k r : Fin 9} (hrk : r ≠ k)
    (hi : flip v i ∈ D) (hi' : flip (flip v k) i ∈ D)
    (hr : flip (flip v i) r ∈ D) (hr' : flip (flip (flip v k) i) r ∈ D) : False := by
  have hk : flip (flip v i) k ∈ D := by rwa [flip_comm v i k]
  apply no_selected_square hbD hrk hi hr hk
  rwa [flip_comm (flip v i) r k, flip_comm v i k]

open Classical in
/-- Along a complement edge with coverage three by `C` and two by `D`, `C` has four
neighbor directions at each endpoint and `D` has the same pair at both endpoints.
Exactly one of the corner in those two directions and its translate lies in `D`. -/
theorem fivefold_cover_endpoint_switch (C D : Finset (Q 9))
    (hrC : ((hypercube 9).induce (C : Set _)).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set _)).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hdisj : Disjoint C D)
    (hcross : ∀ x ∈ C, ∀ y ∈ D, ¬ (hypercube 9).Adj x y)
    (v : Q 9) (k : Fin 9)
    (hvC : v ∉ C) (hvD : v ∉ D) (hwC : flip v k ∉ C) (hwD : flip v k ∉ D)
    (hC : (directions C v ∩ directions C (flip v k)).card = 3)
    (hD : (directions D v ∩ directions D (flip v k)).card = 2) :
    (directions C v).card = 4 ∧ (directions C (flip v k)).card = 4 ∧
      ∃ i j : Fin 9, i ≠ j ∧ directions D v = {i, j} ∧
        directions D (flip v k) = {i, j} ∧
        (flip (flip v i) j ∈ D ↔ flip (flip (flip v i) j) k ∉ D) := by
  let w := flip v k
  have hcard_left : ∀ {S T : Finset (Fin 9)}, (S ∩ T).card ≤ S.card :=
    fun {_ _} => Finset.card_le_card Finset.inter_subset_left
  have hcard_right : ∀ {S T : Finset (Fin 9)}, (S ∩ T).card ≤ T.card :=
    fun {_ _} => Finset.card_le_card Finset.inter_subset_right
  obtain ⟨hvC4, hvD2⟩ := endpoint_cards hrC hrD hbC hbD hdisj hcross hvC hvD
    (hC ▸ hcard_left) (hD ▸ hcard_left)
  obtain ⟨hwC4, hwD2⟩ := endpoint_cards hrC hrD hbC hbD hdisj hcross hwC hwD
    (hC ▸ hcard_right) (hD ▸ hcard_right)
  obtain ⟨i, j, hij, hpair⟩ := Finset.card_eq_two.mp hD
  have hvPair : directions D v = {i, j} := hpair ▸
    (Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hvD2, hD])).symm
  have hwPair : directions D w = {i, j} := hpair ▸
    (Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hwD2, hD])).symm
  have hvi : flip v i ∈ D := (mem_directions D v i).mp (by rw [hvPair]; simp)
  have hwi : flip w i ∈ D := (mem_directions D w i).mp (by rw [hwPair]; simp)
  have hjk : j ≠ k := by
    intro h
    subst j
    exact hwD ((mem_directions D v k).mp (by rw [hvPair]; simp))
  refine ⟨hvC4, hwC4, i, j, hij, hvPair, hwPair, ?_⟩
  rw [flip_comm (flip v i) j k, flip_comm v i k]
  change flip (flip v i) j ∈ D ↔ flip (flip w i) j ∉ D
  constructor
  · intro hvCorner hwCorner
    exact no_shared_continuation hbD hjk hvi hwi hvCorner hwCorner
  · intro hwCorner
    by_contra hvCorner
    have hvFree := directions_eq_unoccupied_of_corner_absent hrD hdisj hcross
      hvD hvC4 hvD2 hvPair hvCorner
    have hwFree := directions_eq_unoccupied_of_corner_absent hrD hdisj hcross
      hwD hwC4 hwD2 hwPair hwCorner
    -- Three shared C directions and one extra at each end occupy five coordinates.
    have hCUnion : (directions C v ∪ directions C w).card = 5 := by
      rw [Finset.card_union, hvC4, hwC4, hC]
    have hUnionDisj : Disjoint (directions C v ∪ directions C w) (directions D v) := by
      refine Finset.disjoint_union_left.mpr ⟨directions_disjoint hdisj v, ?_⟩
      rw [hvPair, ← hwPair]
      exact directions_disjoint hdisj w
    -- The shared pair occupies two more. Removing k leaves a free direction at both ends.
    let occupied := (directions C v ∪ directions C w) ∪ directions D v
    have hoccupied : occupied.card = 7 := by
      dsimp [occupied]
      rw [Finset.card_union_of_disjoint hUnionDisj, hCUnion, hvD2]
    have hfree : (Finset.univ \ insert k occupied).card = 1 := by
      have hk : k ∉ occupied := by
        simp only [occupied, Finset.mem_union, mem_directions, not_or]
        exact ⟨⟨hwC, by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hvC⟩, hwD⟩
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, Finset.card_insert_of_notMem hk, hoccupied]
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (show 0 < (Finset.univ \ insert k occupied).card by
      rw [hfree]; decide)
    have hrFree : r ≠ k ∧ (r ∉ directions C v ∧ r ∉ directions C w) ∧
        r ∉ directions D v := by
      simpa only [occupied, Finset.mem_insert, Finset.mem_union, not_or]
        using (Finset.mem_sdiff.mp hr).2
    apply no_shared_continuation hbD hrFree.1 hvi hwi
    · apply (mem_directions D (flip v i) r).mp
      rw [hvFree]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_union.mp h).elim hrFree.2.1.1 hrFree.2.2⟩
    · apply (mem_directions D (flip w i) r).mp
      rw [hwFree, hwPair, ← hvPair]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        fun h => (Finset.mem_union.mp h).elim hrFree.2.1.2 hrFree.2.2⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FivefoldCoverDynamics

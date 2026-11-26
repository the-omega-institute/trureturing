/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/CubicContactDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: If one cubic cube support is Huang balanced, closest pairs agree on at least five axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

/-! A distance restriction at closest pairs in the cube. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeGirth (no_selected_square)
open BalancedCubeComponentBoundary (directions mem_directions regular_directions)
open TwoBalancedComponents (componentFinset exists_two_balanced_components)

attribute [local instance] Classical.propDecidable

private theorem flip_eq_flip_iff {n : ℕ} (x y : Q n) (i j : Fin n) :
    flip x i j = flip y i j ↔ x j = y j := by
  by_cases hij : j = i
  · subst j
    cases hx : x i <;> cases hy : y i <;> simp [BalancedCriticalSpectrum.flip, hx, hy]
  · simp [BalancedCriticalSpectrum.flip, hij]

private theorem hamming_flip_of_ne {n : ℕ} {x y : Q n} {i : Fin n} (hi : x i ≠ y i) :
    hammingDist (flip x i) y + 1 = hammingDist x y := by
  classical
  let S := Finset.univ.filter fun k : Fin n => x k ≠ y k
  have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have he : (Finset.univ.filter fun k => flip x i k ≠ y k) = S.erase i := by
    ext k
    have hbit : flip x i k ≠ y k ↔ k ≠ i ∧ x k ≠ y k := by
      by_cases hk : k = i
      · subst k
        cases hx : x i <;> cases hy : y i <;> simp_all [BalancedCriticalSpectrum.flip]
      · simp [BalancedCriticalSpectrum.flip, hk]
    constructor
    · intro h
      obtain ⟨hki, hxy⟩ := hbit.mp (Finset.mem_filter.mp h).2
      exact Finset.mem_erase.mpr ⟨hki, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩⟩
    · intro h
      obtain ⟨hki, hs⟩ := Finset.mem_erase.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbit.mpr ⟨hki, (Finset.mem_filter.mp hs).2⟩⟩
  change (Finset.univ.filter fun k => flip x i k ≠ y k).card + 1 = S.card
  rw [he, Finset.card_erase_add_one hiS]

private theorem directions_subset_agreement {n : ℕ} {C D : Finset (Q n)} {x y : Q n}
    (hy : y ∈ D) (hmin : ∀ u ∈ C, ∀ v ∈ D, hammingDist x y ≤ hammingDist u v) :
    directions C x ⊆ Finset.univ.filter fun i => x i = y i := by
  intro i hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  by_contra hne
  have h₁ := hamming_flip_of_ne hne
  have h₂ := hmin (flip x i) ((mem_directions C x i).mp hi) y hy
  omega

private theorem adjacent_direction_union_card {n : ℕ} {C : Finset (Q n)}
    (hr : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {x : Q n} (hx : x ∈ C) {i : Fin n} (hxi : flip x i ∈ C) :
    (directions C x ∪ directions C (flip x i)).card = 5 := by
  have he : directions C x ∩ directions C (flip x i) = {i} := by
    ext j
    simp only [Finset.mem_inter, mem_directions, Finset.mem_singleton]
    constructor
    · rintro ⟨hxj, hxij⟩
      by_contra hji
      exact no_selected_square hb (Ne.symm hji) hx hxi hxj hxij
    · rintro rfl
      exact ⟨hxi, by simpa only [BalancedCriticalSpectrum.flip_flip] using hx⟩
  have hcard := Finset.card_union_add_card_inter (directions C x) (directions C (flip x i))
  rw [he, Finset.card_singleton, regular_directions C hr hx,
    regular_directions C hr hxi] at hcard
  omega

/-- A closest pair of vertices in two cubic cube supports agrees on at least
five axes if the first support is Huang balanced. If there were fewer axes
of agreement, the two degree-three vertices would have a common direction.
Flipping this axis preserves distance, whereas the resulting adjacent pair
in the first support already needs five distinct directions. -/
theorem closest_pair_distance_add_five_le {n : ℕ} {C D : Finset (Q n)}
    (hc : ((hypercube n).induce (C : Set (Q n))).IsRegularOfDegree 3)
    (hd : ((hypercube n).induce (D : Set (Q n))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {x y : Q n} (hx : x ∈ C) (hy : y ∈ D)
    (hmin : ∀ u ∈ C, ∀ v ∈ D, hammingDist x y ≤ hammingDist u v) :
    hammingDist x y + 5 ≤ n := by
  classical
  let A := Finset.univ.filter fun i => x i = y i
  have hAc : A.card + hammingDist x y = n := by
    change A.card + (Finset.univ.filter fun i => x i ≠ y i).card = n
    rw [Finset.card_filter_add_card_filter_not]
    simp
  suffices hA : 5 ≤ A.card by omega
  by_contra! hA
  have hC : directions C x ⊆ A := directions_subset_agreement hy hmin
  have hD : directions D y ⊆ A := by
    have h := directions_subset_agreement hx (C := D) (D := C) (x := y)
      (fun u hu v hv => by simpa only [hammingDist_comm] using hmin v hv u hu)
    intro i hi
    simpa only [A, Finset.mem_filter, eq_comm] using h hi
  have hUnion := Finset.card_le_card (Finset.union_subset hC hD)
  have hCD := Finset.card_union_add_card_inter (directions C x) (directions D y)
  rw [regular_directions C hc hx, regular_directions D hd hy] at hCD
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (show 0 < (directions C x ∩ directions D y).card by omega)
  obtain ⟨hxi, hyi⟩ := Finset.mem_inter.mp hi
  have hx' := (mem_directions C x i).mp hxi
  have hy' := (mem_directions D y i).mp hyi
  have hflip : hammingDist (flip x i) (flip y i) = hammingDist x y := by
    change (Finset.univ.filter fun j => flip x i j ≠ flip y i j).card =
      (Finset.univ.filter fun j => x j ≠ y j).card
    simp only [ne_eq, flip_eq_flip_iff]
  have hmin' (u : Q n) (hu : u ∈ C) (v : Q n) (hv : v ∈ D) :
      hammingDist (flip x i) (flip y i) ≤ hammingDist u v := hflip.le.trans (hmin u hu v hv)
  have hC' : directions C (flip x i) ⊆ A := by
    have h := directions_subset_agreement hy' hmin'
    intro j hj
    have hh := (Finset.mem_filter.mp (h hj)).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (flip_eq_flip_iff x y i j).mp hh
  have hbound := Finset.card_le_card (Finset.union_subset hC hC')
  rw [adjacent_direction_union_card hc hb hx hx'] at hbound
  omega

open Classical in
/-- In the separated cubic branch of Hong, Wu and Xia's Problem 2, two actual
components have a closest pair at distance two, three, or four. -/
theorem exists_two_components_at_distance_two_to_four (U : Finset (Q 9))
    (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧ ∃ x ∈ componentFinset U K, ∃ y ∈ componentFinset U L,
        2 ≤ hammingDist x y ∧ hammingDist x y ≤ 4 ∧
          ∀ u ∈ componentFinset U K, ∀ v ∈ componentFinset U L,
            hammingDist x y ≤ hammingDist u v := by
  obtain ⟨K, L, hKL, C, D, hCK, hDL, hC, hD, _, hDU, hdis, hclosed, _, hc, hd, hb, _⟩ :=
    exists_two_balanced_components U hU hdeg
  -- Use one finite minimization so both endpoint coordinates may vary.
  obtain ⟨⟨x, y⟩, hxy, hmin⟩ :=
    Finset.exists_min_image (C.product D) (fun p => hammingDist p.1 p.2) (hC.product hD)
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v :=
    hmin (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩)
  have hzero : hammingDist x y ≠ 0 := fun hz =>
    Finset.disjoint_left.mp hdis ((hammingDist_eq_zero.mp hz) ▸ hx) hy
  have hone : hammingDist x y ≠ 1 := fun ho =>
    Finset.disjoint_left.mp hdis (hclosed x hx y (hDU hy) ho) hy
  have hhigh : hammingDist x y + 5 ≤ 9 := closest_pair_distance_add_five_le hc hd hb hx hy hm
  refine ⟨K, L, hKL, x, hCK ▸ hx, y, hDL ▸ hy, by omega, by omega, ?_⟩
  simpa only [hCK, hDL] using hm

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

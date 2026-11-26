/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceFourExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exterior evenness and simultaneous flips exclude separation four for balanced cubic nine-cube supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

/-! Simultaneous coordinate flips and the exclusion of minimum distance four. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceFourExclusion

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_apply_same flip_flip IsBalanced)
open BalancedCubeComponentBoundary (directions exterior_even mem_directions regular_directions)
open CubicContactDistance (closest_pair_distance_add_five_le)
open private adjacent_direction_union_card directions_subset_agreement flip_eq_flip_iff hamming_flip_of_ne from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.CubicContactDistance

open Classical in
/-- Balanced induced cubic supports in the nine-cube with mutual separation at
least four have no pair at distance four. The two counts are made around a
single, fixed endpoint. -/
theorem no_distance_four_of_four_separated
    {C D : Finset (Q 9)}
    (hC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 4 ≤ hammingDist u v)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) : hammingDist x y ≠ 4 := by
  intro hxy
  let agree (z : Q 9) := Finset.univ.filter fun i => z i = y i
  let sphere := C.filter fun z => hammingDist z y = 4
  have hAgree {z : Q 9} (hz : hammingDist z y = 4) : (agree z).card = 5 := by
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 9)))
      (p := fun i => z i = y i)
    change (agree z).card + hammingDist z y = (Finset.univ : Finset (Fin 9)).card at hc
    rw [hz, Finset.card_univ, Fintype.card_fin] at hc
    omega
  -- A common flip determines the entire agreement set from the second support.
  have hcommon (z : Q 9) (hz : z ∈ sphere) :
      ∃ i ∈ directions D y, agree z = directions D y ∪ directions D (flip y i) := by
    obtain ⟨hzC, hzy⟩ := Finset.mem_filter.mp hz
    have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
        hammingDist z y ≤ hammingDist u v := hzy.le.trans (hsep u hu v hv)
    have hleft : directions C z ⊆ agree z := directions_subset_agreement hy hm
    have hright : directions D y ⊆ agree z := by
      have h := directions_subset_agreement hzC (C := D) (D := C) (x := y)
        (fun u hu v hv => by simpa only [hammingDist_comm] using hm v hv u hu)
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (h hi)).2.symm⟩
    have hunion := Finset.card_le_card (Finset.union_subset hleft hright)
    have hsum := Finset.card_union_add_card_inter (directions C z) (directions D y)
    rw [regular_directions C hC hzC, regular_directions D hD hy] at hsum
    have ha := hAgree hzy
    obtain ⟨i, hi⟩ := Finset.card_pos.mp
      (show 0 < (directions C z ∩ directions D y).card by omega)
    obtain ⟨hzi, hyi⟩ := Finset.mem_inter.mp hi
    have hz' := (mem_directions C z i).mp hzi
    have hy' := (mem_directions D y i).mp hyi
    have hdist : hammingDist (flip y i) (flip z i) = 4 := by
      rw [hammingDist_comm]
      change (Finset.univ.filter fun j => flip z i j ≠ flip y i j).card = 4
      change (Finset.univ.filter fun j => z j ≠ y j).card = 4 at hzy
      simpa only [ne_eq, flip_eq_flip_iff] using hzy
    have hnew : directions D (flip y i) ⊆ agree z := by
      have h := directions_subset_agreement hz' (C := D) (D := C) (x := flip y i)
        (fun u hu v hv => by rw [hdist, hammingDist_comm]; exact hsep v hv u hu)
      intro j hj
      have hbit := (Finset.mem_filter.mp (h hj)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((flip_eq_flip_iff y z i j).mp hbit).symm⟩
    refine ⟨i, hyi, (Finset.eq_of_subset_of_card_le (Finset.union_subset hright hnew) ?_).symm⟩
    rw [adjacent_direction_union_card hD hbD hy hy', ha]
  have hupper : sphere.card ≤ 3 := by
    let axis (z : Q 9) := if hz : z ∈ sphere then Classical.choose (hcommon z hz) else 0
    have haxis {z : Q 9} (hz : z ∈ sphere) :
        axis z ∈ directions D y ∧ agree z = directions D y ∪ directions D (flip y (axis z)) := by
      simpa only [axis, dite_eq_left hz] using Classical.choose_spec (hcommon z hz)
    rw [← regular_directions D hD hy]
    apply Finset.card_le_card_of_injOn axis (fun z hz => (haxis hz).1)
    intro u hu v hv heq
    have he := (haxis hu).2.trans (heq ▸ (haxis hv).2.symm)
    funext i
    have hbit : u i = y i ↔ v i = y i := by
      have h := Finset.ext_iff.mp he i
      simpa [agree] using h
    cases hyi : y i <;> cases hui : u i <;> cases hvi : v i <;> simp_all
  -- Flipping a differing axis toward y reaches an exterior row. A second
  -- occupied neighbor repairs the distance, changing a different agreement bit.
  let diff := Finset.univ.filter fun i => x i ≠ y i
  have hrepair (i : Fin 9) (hi : i ∈ diff) :
      ∃ z ∈ sphere, ∀ j ∈ diff, z j = y j ↔ j = i := by
    have hxi : x i ≠ y i := (Finset.mem_filter.mp hi).2
    let w := flip x i
    have hwy : hammingDist w y + 1 = 4 := (hamming_flip_of_ne hxi).trans hxy
    have hw : w ∉ C := by
      intro hw
      have := hsep w hw y hy
      omega
    have hiw : i ∈ directions C w := (mem_directions C w i).mpr (by simpa only [w, BalancedCriticalSpectrum.flip_flip] using hx)
    obtain ⟨m, hm⟩ := exterior_even C hC hbC w hw
    have hpos := Finset.card_pos.mpr ⟨i, hiw⟩
    have hrem := Finset.card_erase_add_one hiw
    obtain ⟨k, hk⟩ := Finset.card_pos.mp
      (show 0 < ((directions C w).erase i).card by omega)
    obtain ⟨hki, hkw⟩ := Finset.mem_erase.mp hk
    let z := flip w k
    have hzC : z ∈ C := (mem_directions C w k).mp hkw
    have hlow := hsep z hzC y hy
    have hdist : hammingDist z y = 4 := by
      have hstep : hammingDist z w = 1 :=
        (hammingDist_comm z w).trans (BalancedCriticalSpectrum.flip_adj w k)
      have htri := hammingDist_triangle z w y
      omega
    refine ⟨z, Finset.mem_filter.mpr ⟨hzC, hdist⟩, ?_⟩
    have hagree : w k = y k := by
      by_contra h
      have hs := hamming_flip_of_ne h
      change hammingDist z y + 1 = hammingDist w y at hs
      omega
    have hkdiff : k ∉ diff := by
      intro hk
      have hbit := (Finset.mem_filter.mp hk).2
      exact hbit (by simpa [w, BalancedCriticalSpectrum.flip, hki] using hagree)
    intro j hj
    have hjk : j ≠ k := fun he => hkdiff (he ▸ hj)
    by_cases hji : j = i
    · subst j
      cases hxa : x i <;> cases hya : y i <;>
        simp_all [z, w, BalancedCriticalSpectrum.flip]
    · have hne := (Finset.mem_filter.mp hj).2
      simp [z, w, BalancedCriticalSpectrum.flip, hjk, hji, hne]
  let repair (i : Fin 9) := if hi : i ∈ diff then Classical.choose (hrepair i hi) else x
  have hrepair_spec {i : Fin 9} (hi : i ∈ diff) :
      repair i ∈ sphere ∧ ∀ j ∈ diff, repair i j = y j ↔ j = i := by
    simpa only [repair, dite_eq_left hi] using Classical.choose_spec (hrepair i hi)
  have hCount : diff.card ≤ sphere.card := by
    apply Finset.card_le_card_of_injOn repair (fun i hi => (hrepair_spec hi).1)
    intro i hi j hj heq
    apply ((hrepair_spec hj).2 i hi).mp
    rw [← heq]
    exact ((hrepair_spec hi).2 i hi).mpr rfl
  change hammingDist x y ≤ sphere.card at hCount
  omega

open Classical in
/-- The two components in a hypothetical subcubic 258-set in the nine-cube can
be chosen with minimum distance two or three. -/
theorem exists_two_components_at_distance_two_or_three (U : Finset (Q 9))
    (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧ ∃ x ∈ TwoBalancedComponents.componentFinset U K,
        ∃ y ∈ TwoBalancedComponents.componentFinset U L,
          2 ≤ hammingDist x y ∧ hammingDist x y ≤ 3 ∧
            ∀ u ∈ TwoBalancedComponents.componentFinset U K,
              ∀ v ∈ TwoBalancedComponents.componentFinset U L,
                hammingDist x y ≤ hammingDist u v := by
  obtain ⟨K, L, hKL, C, D, hCK, hDL, hC, hD, _, hDU, hdis, hclosed, _, hc, hd, hbC, hbD, _, _, _⟩ :=
    TwoBalancedComponents.exists_two_balanced_components U hU hdeg
  obtain ⟨⟨x, y⟩, hxy, hmin⟩ :=
    Finset.exists_min_image (C.product D) (fun p => hammingDist p.1 p.2) (hC.product hD)
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
  have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v := hmin (u, v) (Finset.mem_product.mpr ⟨hu, hv⟩)
  have hzero : hammingDist x y ≠ 0 := fun hz =>
    Finset.disjoint_left.mp hdis ((hammingDist_eq_zero.mp hz) ▸ hx) hy
  have hone : hammingDist x y ≠ 1 := fun ho =>
    Finset.disjoint_left.mp hdis (hclosed x hx y (hDU hy) ho) hy
  have hhigh : hammingDist x y + 5 ≤ 9 := closest_pair_distance_add_five_le hc hd hbC hx hy hm
  have hfour : hammingDist x y ≠ 4 := by
    intro he
    exact no_distance_four_of_four_separated hc hd hbC hbD
      (fun u hu v hv => he ▸ hm u hu v hv) hx hy he
  have hlo : 2 ≤ hammingDist x y := by omega
  have hhi : hammingDist x y ≤ 3 := by omega
  refine ⟨K, L, hKL, x, hCK ▸ hx, y, hDL ▸ hy, hlo, hhi, ?_⟩
  simpa only [hCK, hDL] using hm

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceFourExclusion

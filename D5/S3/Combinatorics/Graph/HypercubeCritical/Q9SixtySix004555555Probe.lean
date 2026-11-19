import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix015555555Probe
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixCoordinateTriplesProbe

/-! Applying the six-coordinate triple classification to the false side of
the deficit-four cut. -/

set_option autoImplicit false

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

open BalancedCriticalSpectrum (Q IsBalanced)
local notation "flip" => BalancedCriticalSpectrum.flip
attribute [local instance] Classical.propDecidable

open private heavySupport heavySupport_sliceVertex sliceVertex flip_heavy_erase
  sliceVertex_injective slice_top_directions topFamily mem_topFamily topFamily_four topFamily_pair
  one_more_coordinate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix015555555Probe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions mem_directions directions_card regular_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private sum_cube_membership_property from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe

private abbrev e : Fin 6 ↪ Fin 7 := Fin.succEmb 6

private def H : Finset (Fin 7) := univ.map e

private noncomputable def sixTopFamily (C : Finset (Q 9)) (b : Bool × Bool) :
    Finset (Finset (Fin 6)) :=
  ((univ : Finset (Fin 6)).powersetCard 3).filter fun t => sliceVertex b (t.map e) ∈ C

private lemma mem_sixTopFamily {C : Finset (Q 9)} {b : Bool × Bool} {t : Finset (Fin 6)} :
    t ∈ sixTopFamily C b ↔ t.card = 3 ∧ sliceVertex b (t.map e) ∈ C := by
  simp [sixTopFamily, mem_powersetCard]

private lemma map_sixTopFamily (C : Finset (Q 9)) (b : Bool × Bool) :
    (sixTopFamily C b).map (mapEmbedding e).toEmbedding = topFamily C b H := by
  classical
  ext s
  rw [mem_map, mem_topFamily]
  change (∃ t ∈ sixTopFamily C b, t.map e = s) ↔ _
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨h3, hmem⟩ := mem_sixTopFamily.mp ht
    exact ⟨map_subset_map.mpr (subset_univ _), by rw [card_map, h3], hmem⟩
  · rintro ⟨hs, h3, hmem⟩
    obtain ⟨t, ht⟩ : ∃ t : Finset (Fin 6), t.map e = s := by
      refine ⟨univ.filter fun i => e i ∈ s, ?_⟩
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
        exact (mem_filter.mp hj).2
      · intro hi
        obtain ⟨j, _, rfl⟩ := mem_map.mp (hs hi)
        exact mem_map.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hi⟩, rfl⟩
    refine ⟨t, mem_sixTopFamily.mpr ⟨?_, ?_⟩, ht⟩
    · simpa only [card_map] using (congrArg card ht).trans h3
    · simpa only [ht] using hmem

private noncomputable def sixShadow (T : Finset (Finset (Fin 6))) : Finset (Finset (Fin 6)) :=
  ((univ : Finset (Fin 6)).powersetCard 2).filter fun p => (T.filter (p ⊆ ·)).Nonempty

private lemma shadow_selected {C : Finset (Q 9)} {b : Bool × Bool}
    (hforced : ∀ s ∈ topFamily C b H, ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C)
    {p : Finset (Fin 6)} (hp : p ∈ sixShadow (sixTopFamily C b)) :
    sliceVertex b (p.map e) ∈ C := by
  classical
  obtain ⟨hp2, ht⟩ := mem_filter.mp hp
  obtain ⟨t, ht⟩ := ht
  obtain ⟨htT, hpt⟩ := mem_filter.mp ht
  obtain ⟨ht3, _⟩ := mem_sixTopFamily.mp htT
  have ht' : t.map e ∈ topFamily C b H := by
    rw [← map_sixTopFamily]
    exact mem_map.mpr ⟨t, htT, rfl⟩
  have hsub : p.map e ⊆ t.map e := map_subset_map.mpr hpt
  obtain ⟨i, hi, _, he⟩ := one_more_coordinate hsub (by
    rw [card_map, card_map, ht3, (mem_powersetCard.mp hp2).2])
  simpa only [flip_heavy_erase b hi, he] using hforced (t.map e) ht' i hi

private lemma slice_budget {C : Finset (Q 9)} {b : Bool × Bool}
    (hforced : ∀ s ∈ topFamily C b H, ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C) :
    (sixTopFamily C b).card + (sixShadow (sixTopFamily C b)).card ≤
      (C.filter fun x => x 0 = b.1 ∧ x 1 = b.2 ∧ x 2 = false).card := by
  classical
  let T := sixTopFamily C b
  let P := sixShadow T
  have hdis : Disjoint T P := by
    apply Finset.disjoint_left.mpr
    intro s hs hp
    have h3 := (mem_sixTopFamily.mp hs).1
    have h2 := (mem_powersetCard.mp (mem_filter.mp hp).1).2
    omega
  have hz (s : Finset (Fin 6)) : sliceVertex b (s.map e) 2 = false := by
    change decide ((0 : Fin 7) ∈ s.map e) = false
    apply decide_eq_false
    intro hm
    obtain ⟨i, _, he⟩ := mem_map.mp hm
    exact Fin.succ_ne_zero i he
  have h := card_le_card_of_injOn (s := T ∪ P)
    (t := C.filter fun x => x 0 = b.1 ∧ x 1 = b.2 ∧ x 2 = false)
    (fun x => sliceVertex b (x.map e)) (fun s hs => by
      apply mem_filter.mpr
      refine ⟨?_, rfl, rfl, hz s⟩
      rcases mem_union.mp hs with ht | hp
      · exact (mem_sixTopFamily.mp ht).2
      · exact shadow_selected hforced hp)
    (fun x _ y _ he => map_injective _ (sliceVertex_injective b he))
  rwa [card_union_of_disjoint hdis] at h

private lemma slice_shapes {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcap : ∀ x ∈ C, lastSevenWeight x ≤ 3)
    (b : Bool × Bool)
    (hforced : ∀ s ∈ topFamily C b H, ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C) :
    let T := sixTopFamily C b
    let P := sixShadow T
    (T.card, P.card) ∈ ([(0, 0), (6, 11), (8, 12), (8, 14), (10, 15)] : List (ℕ × ℕ)) ∧
      (T.card = 8 → P.card = 12 → ∀ p : Finset (Fin 6), p.card = 2 →
        (T.filter (Disjoint p ·)).card ≤ 2) := by
  classical
  dsimp only
  apply six_coordinate_triple_family_shapes (sixTopFamily C b)
  · exact fun _ ht => (mem_sixTopFamily.mp ht).1
  · intro s hs
    have h := topFamily_four hr hb hcap b H hforced (s.map e)
      (by rw [card_map, hs]) (map_subset_map.mpr (subset_univ _))
    rw [← map_sixTopFamily C b, filter_map, card_map] at h
    change Even ((sixTopFamily C b).filter (fun t => t.map e ⊆ s.map e)).card ∧
      ((sixTopFamily C b).filter (fun t => t.map e ⊆ s.map e)).card ≤ 2 at h
    simpa only [map_subset_map] using h
  · intro p hp
    have h := topFamily_pair hr b H hforced (p.map e) (by rw [card_map, hp])
    rw [← map_sixTopFamily C b, filter_map, card_map] at h
    change ((sixTopFamily C b).filter (fun t => p.map e ⊆ t.map e)).card ≤ 3 at h
    simpa only [map_subset_map] using h

private def deficit : Fin 9 → ℤ :=
  Fin.cases 0 (Fin.cases 0 (Fin.cases 4 (fun _ : Fin 6 => 5)))

private def sixWeight (x : Q 9) : ℕ :=
  (univ.filter fun i : Fin 6 => x i.succ.succ.succ = true).card

private lemma weight_formula (x : Q 9) :
    (∑ i, if x i = true then deficit i else 0) =
      (if x 2 = true then 4 else 0) + 5 * (sixWeight x : ℤ) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, mul_comm]
  have he (i : Fin 6) : (if x i.succ.succ.succ = true then deficit i.succ.succ.succ else 0) =
      (if x i.succ.succ.succ = true then (1 : ℤ) else 0) * 5 := by
    cases x i.succ.succ.succ <;> simp [deficit]
  have hzero : (if x (0 : Fin 9) = true then deficit 0 else 0) = 0 := by simp [deficit]
  have hone : (if x (1 : Fin 9) = true then deficit 1 else 0) = 0 := by
    have h : deficit 1 = 0 := rfl
    simp [h]
  simp only [he, ← sum_mul, sixWeight, card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [show (0 : Fin 8).succ = (1 : Fin 9) from rfl, hzero, hone, zero_add, zero_add]
  change (if x 2 = true then 4 else 0) + _ = _
  rfl

private lemma seven_weight_formula (x : Q 9) :
    lastSevenWeight x = (if x 2 = true then 1 else 0) + sixWeight x := by
  simp only [lastSevenWeight, sixWeight, card_filter, Fin.sum_univ_succ]
  rfl

private lemma deficit_four_slice_geometry {C : Finset (Q 9)}
    (hC : C.card = 66) (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    (∀ x ∈ C, lastSevenWeight x ≤ 3) ∧
    (∀ b, ∀ s ∈ topFamily C b H, (shell C (sliceVertex b s) 7).card = 8 ∧
      ∀ i ∈ s, flip (sliceVertex b s) i.succ.succ ∈ C) := by
  classical
  have hr_sum : (∑ i, deficit i) = 34 := by decide +kernel
  have hr_nonneg : ∀ i, 0 ≤ deficit i := by decide +kernel
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hr hb
  have hweight (x : Q 9) (hx : x ∈ C) :=
    coordinate_profile_weight_bound hC hr hb (fun _ => true) deficit hhalf hx
  simp only [weight_formula, hr_sum] at hweight
  have hcap (x : Q 9) (hx : x ∈ C) : lastSevenWeight x ≤ 3 := by
    have hw := hweight x hx
    have hs := sixty_six_distance_seven_le_eight hC hr hb hd hx
    rw [seven_weight_formula]
    split_ifs at hw ⊢ <;> omega
  refine ⟨hcap, fun b s hs => ?_⟩
  obtain ⟨hsH, h3, hx⟩ := mem_topFamily.mp hs
  have hz : (0 : Fin 7) ∉ s := by
    intro hm
    obtain ⟨j, _, he⟩ := mem_map.mp (hsH hm)
    exact Fin.succ_ne_zero j he
  have hx2 : sliceVertex b s 2 = false := by
    change decide ((0 : Fin 7) ∈ s) = false
    simp [hz]
  have h7 : lastSevenWeight (sliceVertex b s) = 3 := by
    change (heavySupport (sliceVertex b s)).card = 3
    simpa only [heavySupport_sliceVertex] using h3
  have h6 : sixWeight (sliceVertex b s) = 3 := by
    rw [seven_weight_formula, hx2] at h7
    simpa using h7
  have hw := hweight _ hx
  have h8 : (shell C (sliceVertex b s) 7).card = 8 := by
    have hle := sixty_six_distance_seven_le_eight hC hr hb hd hx
    rw [hx2, h6] at hw
    norm_num at hw
    omega
  refine ⟨h8, fun i hi => ?_⟩
  have htrue : sliceVertex b s i.succ.succ = true := by simpa [sliceVertex] using hi
  obtain ⟨j, _, rfl⟩ := mem_map.mp (hsH hi)
  exact eight_partners_force_minority_directions_used hC hr hb hd
    (fun _ => true) deficit hhalf hr_nonneg hx h8 htrue (show (2 : ℤ) ≤ 5 by decide)

private lemma shape_of_deficit_four_slice {C : Finset (Q 9)}
    (hC : C.card = 66) (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (b : Bool × Bool) :
    let T := sixTopFamily C b
    let P := sixShadow T
    ((T.card, P.card) ∈ ([(0, 0), (6, 11), (8, 12), (8, 14), (10, 15)] : List (ℕ × ℕ)) ∧
      (T.card = 8 → P.card = 12 → ∀ p : Finset (Fin 6), p.card = 2 →
        (T.filter (Disjoint p ·)).card ≤ 2)) ∧
    T.card + P.card ≤ (C.filter fun x => x 0 = b.1 ∧ x 1 = b.2 ∧ x 2 = false).card := by
  obtain ⟨hcap, hgeo⟩ := deficit_four_slice_geometry hC hr hb hhalf
  exact ⟨slice_shapes hr hb hcap b (fun s hs => (hgeo b s hs).2),
    slice_budget (fun s hs => (hgeo b s hs).2)⟩

#print axioms shape_of_deficit_four_slice

private noncomputable def zeroDegree (U : Finset (Q 9)) (x : Q 9) : ℕ :=
  (if flip x 0 ∈ U then 1 else 0) + (if flip x 1 ∈ U then 1 else 0)

private lemma zero_degree_capacity {C U : Finset (Q 9)} (hb : IsBalanced C) (hU : U ⊆ C) :
    3 * (∑ x ∈ U, zeroDegree U x) ≤ 4 * U.card := by
  classical
  let K := U.filter fun x => flip x 0 ∈ U ∧ flip x 1 ∈ U
  let A := K.image fun x => flip x 0
  let B := K.image fun x => flip x 1
  have hK (x : Q 9) (hx : x ∈ K) :
      x ∈ U ∧ flip x 0 ∈ U ∧ flip x 1 ∈ U := mem_filter.mp hx
  have hne : (0 : Fin 9) ≠ 1 := by decide
  have no_corner (x : Q 9) (hx : x ∈ K) : flip (flip x 0) 1 ∉ U := by
    obtain ⟨hxU, hx0, hx1⟩ := hK x hx
    intro hx01
    exact BalancedCubeGirth.no_selected_square hb hne
      (hU hxU) (hU hx0) (hU hx1) (hU hx01)
  have hKA : Disjoint K A := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    change x ∈ K.image (fun y => flip y 0) at hy
    obtain ⟨y, hyK, rfl⟩ := mem_image.mp hy
    exact no_corner y hyK (hK _ hx).2.2
  have hKB : Disjoint K B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    change x ∈ K.image (fun y => flip y 1) at hy
    obtain ⟨y, hyK, rfl⟩ := mem_image.mp hy
    exact no_corner y hyK (by rw [flip_comm y 0 1]; exact (hK _ hx).2.1)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hx
    obtain ⟨v, hv, he⟩ := mem_image.mp hy
    apply no_corner u hu
    rw [← he, BalancedCriticalSpectrum.flip_flip]
    exact (hK v hv).1
  have hsub : K ∪ A ∪ B ⊆ U := by
    intro x hx
    rcases mem_union.mp hx with h | h
    · rcases mem_union.mp h with h | h
      · exact (hK x h).1
      · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
        exact (hK y hy).2.1
    · obtain ⟨y, hy, rfl⟩ := mem_image.mp h
      exact (hK y hy).2.2
  have hinj (i : Fin 9) : Function.Injective (fun x : Q 9 => flip x i) := by
    intro x y h
    simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun v => flip v i) h
  have hcard := card_le_card hsub
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hKB, hAB⟩), card_union_of_disjoint hKA,
    show A.card = K.card from card_image_of_injective _ (hinj 0),
    show B.card = K.card from card_image_of_injective _ (hinj 1)] at hcard
  have hp (x : Q 9) (hx : x ∈ U) :
      zeroDegree U x ≤ 1 + (if flip x 0 ∈ U ∧ flip x 1 ∈ U then 1 else 0) := by
    by_cases h0 : flip x 0 ∈ U <;> by_cases h1 : flip x 1 ∈ U <;> simp [zeroDegree, h0, h1]
  have hs := sum_le_sum hp
  rw [sum_add_distrib, sum_const_nat (fun _ _ => rfl), mul_one, ← card_filter] at hs
  change (∑ x ∈ U, zeroDegree U x) ≤ U.card + K.card at hs
  omega

#print axioms zero_degree_capacity

private noncomputable def topOfCut (C : Finset (Q 9)) (b : Bool) : Finset (Q 9) :=
  C.filter fun x => x 2 = b ∧ lastSevenWeight x = 3

private lemma cut_top_sum {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    31 ≤ (topOfCut C false).card + (topOfCut C true).card := by
  classical
  have hmidd : (C.filter fun x => x 2 = true).card = 25 := by
    have h := hhalf 2
    change _ + 2 * (4 : ℤ) = 33 at h
    omega
  have hheavy (i : Fin 6) : (C.filter fun x => x i.succ.succ.succ = true).card = 23 := by
    have h := hhalf i.succ.succ.succ
    change _ + 2 * (5 : ℤ) = 33 at h
    omega
  have hsum : (∑ x ∈ C, lastSevenWeight x) = 163 := by
    simp only [seven_weight_formula, sum_add_distrib, ← card_filter]
    rw [hmidd]
    have h := show ∑ x ∈ C, sixWeight x = 6 * 23 by
      simp only [sixWeight, card_filter]
      rw [sum_comm]
      simp only [← card_filter, hheavy]
      rw [sum_const_nat (fun _ _ => rfl), card_univ, Fintype.card_fin]
    omega
  have hc := (deficit_four_slice_geometry hC hr hb hhalf).1
  have hpt (x : Q 9) (hx : x ∈ C) :
      lastSevenWeight x ≤ 2 + if lastSevenWeight x = 3 then 1 else 0 := by
    have h := hc x hx
    split <;> omega
  have hs := sum_le_sum hpt
  rw [hsum, sum_add_distrib, sum_const_nat (fun _ _ => rfl), hC, ← card_filter] at hs
  have he : C.filter (fun x => lastSevenWeight x = 3) =
      topOfCut C false ∪ topOfCut C true := by
    ext x
    cases h : x 2 <;> simp [topOfCut, h]
  have hd : Disjoint (topOfCut C false) (topOfCut C true) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hfalse := (mem_filter.mp hx).2.1
    have htrue := (mem_filter.mp hy).2.1
    simp [hfalse] at htrue
  rw [he, card_union_of_disjoint hd] at hs
  omega

#print axioms cut_top_sum

private lemma heavy_flip_changes_weight (x : Q 9) (i : Fin 6) :
    sixWeight (flip x i.succ.succ.succ) ≠ sixWeight x := by
  classical
  let f (v : Q 9) (j : Fin 6) : ℕ := if v j.succ.succ.succ = true then 1 else 0
  have he (v : Q 9) : sixWeight v = ∑ j, f v j := by simp only [sixWeight, card_filter, f]
  rw [he, he, ← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ _ (mem_univ i)]
  have hs : ∑ j ∈ (univ : Finset (Fin 6)).erase i, f (flip x i.succ.succ.succ) j =
      ∑ j ∈ (univ : Finset (Fin 6)).erase i, f x j := by
    apply sum_congr rfl
    intro j hj
    simp [f, BalancedCriticalSpectrum.flip, (mem_erase.mp hj).1]
  rw [hs]
  cases h : x i.succ.succ.succ <;> simp [f, h]

private lemma direction_incidence_comm (A B : Finset (Q 9)) :
    (∑ x ∈ A, (directions B x).card) = ∑ y ∈ B, (directions A y).card := by
  classical
  simp only [directions_card, card_filter]
  rw [sum_comm]
  simp only [(hypercube 9).adj_comm]

private lemma upper_cut_degree_split (C : Finset (Q 9)) {x : Q 9}
    (hx : x ∈ topOfCut C true) :
    (directions C x).card = zeroDegree (topOfCut C true) x +
      (directions ((C.filter (fun y => y 2 = true)) \ topOfCut C true) x).card +
      if flip x 2 ∈ C then 1 else 0 := by
  classical
  let P := topOfCut C true
  let U := C.filter (fun y => y 2 = true)
  let F := C.filter (fun y => y 2 = false)
  let L := U \ P
  have hx2 := (mem_filter.mp hx).2.1
  have hxw : sixWeight x = 2 := by
    have h := (mem_filter.mp hx).2.2
    rw [seven_weight_formula, hx2] at h
    simp at h
    omega
  have hP : directions P x = ({0, 1} : Finset (Fin 9)).filter (fun i => flip x i ∈ P) := by
    ext i
    simp only [mem_directions, mem_filter]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    refine Fin.cases (by simp) (fun j => ?_) i h
    refine Fin.cases (by simp) (fun k => ?_) j
    refine Fin.cases (fun hm => ?_) (fun l hm => ?_) k
    · have h₂ := (mem_filter.mp hm).2.1
      change (flip x 2) 2 = true at h₂
      simp [hx2] at h₂
    · have h₂ := (mem_filter.mp hm).2.1
      have hw := (mem_filter.mp hm).2.2
      rw [seven_weight_formula, h₂] at hw
      simp at hw
      exact False.elim (heavy_flip_changes_weight x l (by omega))
  have hz : (directions P x).card = zeroDegree P x := by
    rw [hP]
    by_cases h0 : flip x 0 ∈ P <;> by_cases h1 : flip x 1 ∈ P <;>
      simp [zeroDegree, filter_insert, filter_singleton, h0, h1]
  have hF : directions F x = ({2} : Finset (Fin 9)).filter (fun _ => flip x 2 ∈ C) := by
    ext i
    simp only [mem_directions, F, mem_filter, mem_singleton]
    by_cases hi : i = 2
    · subst i
      simp [hx2]
    · rw [show (flip x i) 2 = x 2 from Function.update_of_ne (Ne.symm hi) _ _]
      simp [hi, hx2]
  have hf : (directions F x).card = if flip x 2 ∈ C then 1 else 0 := by
    rw [hF]
    split_ifs with h <;> simp [h]
  have hU : directions U x = directions P x ∪ directions L x := by
    ext i
    simp only [mem_directions, mem_union, L, mem_sdiff]
    have hsub : P ⊆ U := fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1, (mem_filter.mp h).2.1⟩
    exact ⟨fun h => by by_cases hp : flip x i ∈ P <;> simp [h, hp],
      fun h => h.elim (fun h => hsub h) And.left⟩
  have hCU : directions C x = directions U x ∪ directions F x := by
    ext i
    cases h : flip x i 2 <;> simp [mem_directions, U, F, h]
  have hdisUF : Disjoint (directions U x) (directions F x) := by
    apply Finset.disjoint_left.mpr
    intro i hu hf
    have htrue := (mem_filter.mp ((mem_directions _ _ _).mp hu)).2
    have hfalse := (mem_filter.mp ((mem_directions _ _ _).mp hf)).2
    simp [htrue] at hfalse
  have hdisPL : Disjoint (directions P x) (directions L x) := by
    apply Finset.disjoint_left.mpr
    intro i hp hl
    exact (mem_sdiff.mp ((mem_directions _ _ _).mp hl)).2 ((mem_directions _ _ _).mp hp)
  rw [hCU, card_union_of_disjoint hdisUF, hU, card_union_of_disjoint hdisPL, hz, hf]

#print axioms upper_cut_degree_split

private lemma upper_cut_count {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    (topOfCut C true).card ≤ 18 := by
  classical
  let P := topOfCut C true
  let U := C.filter (fun y => y 2 = true)
  let L := U \ P
  have hP : P ⊆ C := filter_subset _ _
  have hPU : P ⊆ U := fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1, (mem_filter.mp h).2.1⟩
  have hL : L ⊆ C := fun _ h => (mem_filter.mp (mem_sdiff.mp h).1).1
  have hu : U.card = 25 := by
    have h := hhalf 2
    change (U.card : ℤ) + 2 * (4 : ℤ) = 33 at h
    omega
  have hl := card_sdiff_of_subset hPU
  change L.card = U.card - P.card at hl
  have hsum (x : Q 9) (hx : x ∈ P) :
      3 = zeroDegree P x + (directions L x).card + if flip x 2 ∈ C then 1 else 0 := by
    simpa only [regular_directions C hr (hP hx)] using upper_cut_degree_split C hx
  have he := sum_congr rfl hsum
  rw [sum_const_nat (fun _ _ => rfl), sum_add_distrib, sum_add_distrib, ← card_filter] at he
  have hdown : (∑ x ∈ P, (directions L x).card) ≤ L.card * 3 := by
    rw [direction_incidence_comm P L, ← sum_const_nat (fun _ _ => rfl)]
    apply sum_le_sum
    intro x hx
    have hsub : directions P x ⊆ directions C x := by
      intro i hi
      exact (mem_directions _ _ _).mpr (hP ((mem_directions _ _ _).mp hi))
    exact (card_le_card hsub).trans_eq (regular_directions C hr (hL hx))
  have hcross : (P.filter (fun x => flip x 2 ∈ C)).card ≤ 11 := by
    have hdir := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hr hb 2
    rw [hC] at hdir
    have h11 : BalancedCriticalSpectrum.directionEdges C 2 = 11 := by omega
    rw [← h11]
    apply card_le_card_of_injOn (fun x => flip x 2)
    · intro x hx
      obtain ⟨hxP, hflip⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hflip, by simp [(mem_filter.mp hxP).2.1, hP hxP]⟩
    · intro x _ y _ h
      simpa only [BalancedCriticalSpectrum.flip_flip] using congrArg (fun v => flip v 2) h
  have hbnd := zero_degree_capacity hb hP
  change P.card ≤ 18
  omega

private lemma lower_cut_count {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    13 ≤ (topOfCut C false).card := by
  have hboth := cut_top_sum hC hr hb hhalf
  have hupper := upper_cut_count hC hr hb hhalf
  omega

#print axioms lower_cut_count

private def sixSupport (x : Q 9) : Finset (Fin 6) :=
  univ.filter fun i => x i.succ.succ.succ = true

private lemma reconstruct_false_side (x : Q 9) (hx : x 2 = false) :
    sliceVertex (x 0, x 1) ((sixSupport x).map e) = x := by
  classical
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases ?_ (fun l => ?_) k
  · change decide ((0 : Fin 7) ∈ (sixSupport x).map e) = x 2
    rw [hx]
    apply decide_eq_false
    rintro h
    obtain ⟨j, _, he⟩ := mem_map.mp h
    exact Fin.succ_ne_zero j he
  · change decide (e l ∈ (sixSupport x).map e) = x l.succ.succ.succ
    cases h : x l.succ.succ.succ <;> simp [sixSupport, h]

private lemma six_top_fiber (C : Finset (Q 9)) (b : Bool × Bool) :
    (sixTopFamily C b).card =
      ((topOfCut C false).filter fun x => (x 0, x 1) = b).card := by
  classical
  apply card_bij (fun s _ => sliceVertex b (s.map e))
  · intro s hs
    obtain ⟨h3, hC⟩ := mem_sixTopFamily.mp hs
    have h7 : lastSevenWeight (sliceVertex b (s.map e)) = 3 := by
      change (heavySupport (sliceVertex b (s.map e))).card = 3
      rw [heavySupport_sliceVertex, card_map, h3]
    have hz : sliceVertex b (s.map e) 2 = false := by
      change decide ((0 : Fin 7) ∈ s.map e) = false
      apply decide_eq_false
      rintro h
      obtain ⟨j, _, he⟩ := mem_map.mp h
      exact Fin.succ_ne_zero j he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hC, hz, h7⟩, Prod.ext rfl rfl⟩
  · intro s hs t ht he
    exact map_injective e (sliceVertex_injective b he)
  · intro x hx
    obtain ⟨hxT, hbits⟩ := mem_filter.mp hx
    obtain ⟨hxC, hx2, hxW⟩ := mem_filter.mp hxT
    have he := reconstruct_false_side x hx2
    rw [hbits] at he
    have h6 : (sixSupport x).card = 3 := by
      rw [seven_weight_formula, hx2] at hxW
      simpa [sixSupport, sixWeight] using hxW
    exact ⟨sixSupport x, mem_sixTopFamily.mpr ⟨h6, he.symm ▸ hxC⟩, he⟩

private lemma two_nonempty_slices {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    let A := (univ : Finset (Bool × Bool)).filter fun b => (sixTopFamily C b).Nonempty
    ∃ a b, a ≠ b ∧ A = {a, b} ∧
      (sixTopFamily C a).card + (sixTopFamily C b).card =
        (topOfCut C false).card ∧
      ((sixTopFamily C a).card, (sixTopFamily C b).card) ∈
        ([(6, 8), (8, 6), (8, 8)] : List (ℕ × ℕ)) := by
  classical
  dsimp only
  let A := (univ : Finset (Bool × Bool)).filter fun b => (sixTopFamily C b).Nonempty
  let L := C.filter fun x => x 2 = false
  let P := topOfCut C false
  let f (x : Q 9) := (x 0, x 1)
  have hL : L.card = 41 := by
    have hmidd := hhalf 2
    change ((C.filter fun x => x 2 = true).card : ℤ) + 2 * (4 : ℤ) = 33 at hmidd
    have h := card_filter_add_card_filter_not (s := C) (fun x => x 2 = true)
    have he : C.filter (fun x => ¬ x 2 = true) = L := by
      ext x
      cases hx : x 2 <;> simp [L, hx]
    rw [he, hC] at h
    omega
  have hsum : (∑ b ∈ A, (sixTopFamily C b).card) = P.card := by
    rw [sum_subset (subset_univ A) (fun b _ h => by
      by_contra hn
      exact h (mem_filter.mpr ⟨mem_univ _, card_pos.mp (Nat.pos_of_ne_zero hn)⟩))]
    calc
      _ = ∑ b : Bool × Bool, (P.filter (fun x => f x = b)).card :=
        sum_congr rfl fun b _ => six_top_fiber C b
      _ = _ := (card_eq_sum_card_fiberwise (f := f)
        (t := (univ : Finset (Bool × Bool))) (fun _ _ => mem_univ _)).symm
  have hsumL : (∑ b : Bool × Bool, (L.filter (fun x => f x = b)).card) = 41 := by
    rw [← card_eq_sum_card_fiberwise (f := f) (fun _ _ => mem_univ _), hL]
  have hbudget (b : Bool × Bool) :
      (sixTopFamily C b).card + (sixShadow (sixTopFamily C b)).card ≤
        (L.filter (fun x => f x = b)).card := by
    have h := (shape_of_deficit_four_slice hC hr hb hhalf b).2
    have he : C.filter (fun x => x 0 = b.1 ∧ x 1 = b.2 ∧ x 2 = false) =
        L.filter (fun x => f x = b) := by
      ext x
      rcases b with ⟨a, b⟩
      simp only [L, f, mem_filter, Prod.mk.injEq]
      tauto
    rwa [he] at h
  have hshape (b : Bool × Bool) (hbA : b ∈ A) :
      ((sixTopFamily C b).card, (sixShadow (sixTopFamily C b)).card) ∈
        ([(6, 11), (8, 12), (8, 14), (10, 15)] : List (ℕ × ℕ)) := by
    have hp := card_pos.mpr (mem_filter.mp hbA).2
    have hm := (shape_of_deficit_four_slice hC hr hb hhalf b).1.1
    rcases List.mem_cons.mp hm with he | he
    · exact (Nat.ne_of_gt hp (congrArg Prod.fst he)).elim
    · exact he
  have hcard_lb (b : Bool × Bool) (hbA : b ∈ A) :
      17 ≤ (L.filter (fun x => f x = b)).card := by
    have ht := hshape b hbA
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
    have hc := hbudget b
    rcases ht with (h | h | h | h) <;> omega
  have ha : A.card ≤ 2 := by
    have h := sum_le_sum hcard_lb
    rw [sum_const_nat (fun _ _ => rfl)] at h
    have hs := sum_le_sum_of_subset (f := fun b => (L.filter (fun x => f x = b)).card)
      (subset_univ A)
    rw [hsumL] at hs
    omega
  have hbA : 2 ≤ A.card := by
    have hp := lower_cut_count hC hr hb hhalf
    change 13 ≤ P.card at hp
    have h : (∑ b ∈ A, (sixTopFamily C b).card) ≤ ∑ _ ∈ A, (10 : ℕ) := by
      apply sum_le_sum
      intro b hb'
      have ht := hshape b hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
      rcases ht with (h | h | h | h) <;> omega
    rw [hsum, sum_const_nat (fun _ _ => rfl)] at h
    omega
  obtain ⟨a, b, hab, hab'⟩ := card_eq_two.mp (le_antisymm ha hbA)
  have haA : a ∈ A := by simp [hab']
  have hbA : b ∈ A := by simp [hab']
  have htotal := hsum
  rw [hab', sum_insert (by simp [hab]), sum_singleton] at htotal
  have hlim := sum_le_sum_of_subset (f := fun b => (L.filter (fun x => f x = b)).card)
    (subset_univ ({a, b} : Finset (Bool × Bool)))
  rw [hsumL, sum_insert (by simp [hab]), sum_singleton] at hlim
  refine ⟨a, b, hab, hab', htotal, ?_⟩
  have haS := hshape a haA
  have hbS := hshape b hbA
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at haS hbS ⊢
  have haC := hbudget a
  have hbC := hbudget b
  have hmin := lower_cut_count hC hr hb hhalf
  change 13 ≤ P.card at hmin
  rcases haS with (haS | haS | haS | haS) <;>
    rcases hbS with (hbS | hbS | hbS | hbS) <;> omega

#print axioms two_nonempty_slices

private lemma independent_false_side_bound {C U : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hL : (C.filter (fun x => x 2 = false)).card = 41)
    (hU : U ⊆ C.filter (fun x => x 2 = false))
    (hind : ∀ x ∈ U, ∀ i : Fin 9, flip x i ∉ U) : U.card ≤ 22 := by
  classical
  let L := C.filter (fun x => x 2 = false)
  let R := L \ U
  have hlen := card_sdiff_of_subset hU
  change R.card = L.card - U.card at hlen
  have hR : R ⊆ C := fun _ h => (mem_filter.mp (mem_sdiff.mp h).1).1
  have hT : U ⊆ C := hU.trans (filter_subset _ _)
  have hp (x : Q 9) (hx : x ∈ U) :
      3 ≤ (directions R x).card + (if flip x 2 ∈ C then 1 else 0) := by
    let D := ({2} : Finset (Fin 9)).filter fun _ => flip x 2 ∈ C
    have hsub : directions C x ⊆ directions R x ∪ D := by
      intro i hi
      have hz := (mem_directions _ _ _).mp hi
      by_cases he : i = 2
      · subst i
        simp [D, hz]
      · have hf : (flip x i) 2 = false := by
          rw [show (flip x i) 2 = x 2 from Function.update_of_ne (Ne.symm he) _ _]
          exact (mem_filter.mp (hU hx)).2
        exact mem_union.mpr (Or.inl ((mem_directions _ _ _).mpr
          (mem_sdiff.mpr ⟨mem_filter.mpr ⟨hz, hf⟩, hind x hx i⟩)))
    have h := (card_le_card hsub).trans (card_union_le _ _)
    rw [regular_directions C hr (hT hx)] at h
    have hd : D.card = if flip x 2 ∈ C then 1 else 0 := by
      by_cases hf : flip x 2 ∈ C <;> simp [D, hf]
    rwa [hd] at h
  have htotal := sum_le_sum hp
  rw [sum_const_nat (fun _ _ => rfl), sum_add_distrib, ← card_filter] at htotal
  have hinside : (∑ x ∈ U, (directions R x).card) ≤ R.card * 3 := by
    rw [direction_incidence_comm U R, ← sum_const_nat (fun _ _ => rfl)]
    apply sum_le_sum
    intro x hx
    have hsub : directions U x ⊆ directions C x := by
      intro i hi
      exact (mem_directions _ _ _).mpr (hT ((mem_directions _ _ _).mp hi))
    exact (card_le_card hsub).trans_eq (regular_directions C hr (hR hx))
  have houtside : (U.filter (fun x => flip x 2 ∈ C)).card ≤ 11 := by
    have hdir := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hr hb 2
    rw [hC] at hdir
    have he : BalancedCriticalSpectrum.directionEdges C 2 = 11 := by omega
    rw [← he]
    apply card_le_card
    intro x hx
    obtain ⟨hxU, hflip⟩ := mem_filter.mp hx
    obtain ⟨hxC, hx2⟩ := mem_filter.mp (hU hxU)
    exact mem_filter.mpr ⟨hxC, hx2, hflip⟩
  change L.card = 41 at hL
  have hsub := card_le_card hU
  change U.card ≤ L.card at hsub
  omega

#print axioms independent_false_side_bound

private def opposite (b : Bool × Bool) : Bool × Bool := (!b.1, !b.2)

private lemma shadow_vertices_opposite_independent {U : Finset (Q 9)} (a : Bool × Bool)
    (hU : ∀ x ∈ U, x 2 = false ∧ sixWeight x = 2 ∧
      ((x 0, x 1) = a ∨ (x 0, x 1) = opposite a)) :
    ∀ x ∈ U, ∀ i : Fin 9, flip x i ∉ U := by
  intro x hx i hf
  obtain ⟨hx2, hxw, hxbits⟩ := hU x hx
  revert hf
  refine Fin.cases (fun h => ?_) (fun j hj => ?_) i
  · rcases a with ⟨a, b⟩
    have h := (hU _ h).2.2
    cases ha : x 0 <;> cases hb : x 1 <;> cases a <;> cases b <;>
      simp [opposite, Prod.mk.injEq, BalancedCriticalSpectrum.flip, ha, hb] at hxbits h
  · refine Fin.cases (fun h => ?_) (fun k hk => ?_) j hj
    · rcases a with ⟨a, b⟩
      have h := (hU _ h).2.2
      have hbit : (flip x 1) 0 = x 0 := Function.update_of_ne
        (show (0 : Fin 9) ≠ 1 by decide) _ _
      have hbit' : (flip x 1) 1 = !x 1 :=
        BalancedCriticalSpectrum.flip_apply_same x 1
      cases ha : x 0 <;> cases hb : x 1 <;> cases a <;> cases b <;>
        simp [opposite, Prod.mk.injEq, hbit, ha, hb] at hxbits h
    · refine Fin.cases (fun h => ?_) (fun l h => ?_) k hk
      · have h2 : (flip x 2) 2 = false := (hU _ h).1
        simp [hx2] at h2
      · exact heavy_flip_changes_weight x l ((hU _ h).2.1.trans hxw.symm)

private lemma false_side_card {C : Finset (Q 9)} (hC : C.card = 66)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    (C.filter fun x => x 2 = false).card = 41 := by
  have hmidd := hhalf 2
  change ((C.filter fun x => x 2 = true).card : ℤ) + 2 * (4 : ℤ) = 33 at hmidd
  have h := card_filter_add_card_filter_not (s := C) (fun x => x 2 = true)
  have he : C.filter (fun x => ¬ x 2 = true) = C.filter (fun x => x 2 = false) := by
    ext x
    cases hx : x 2 <;> simp [hx]
  rw [he, hC] at h
  omega

private lemma sixSupport_sliceVertex (b : Bool × Bool) (s : Finset (Fin 6)) :
    sixSupport (sliceVertex b (s.map e)) = s := by
  ext i
  simp only [sixSupport, mem_filter, mem_univ, true_and]
  change (decide (e i ∈ s.map e) = true ↔ i ∈ s)
  simp

private def liftSlice (b : Bool × Bool) : Finset (Fin 6) ↪ Q 9 :=
  ⟨fun p => sliceVertex b (p.map e), fun _ _ h => map_injective e (sliceVertex_injective b h)⟩

private lemma occupied_slices_cannot_be_opposite {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (a : Bool × Bool)
    (hcounts : ((sixTopFamily C a).card, (sixTopFamily C (opposite a)).card) ∈
      ([(6, 8), (8, 6), (8, 8)] : List (ℕ × ℕ))) : False := by
  classical
  let pairVertices (b : Bool × Bool) :=
    (sixShadow (sixTopFamily C b)).map (liftSlice b)
  let U := pairVertices a ∪ pairVertices (opposite a)
  have hcard (b : Bool × Bool) : (pairVertices b).card = (sixShadow (sixTopFamily C b)).card :=
    card_map _
  have hv (b : Bool × Bool) (x : Q 9) (hx : x ∈ pairVertices b) :
      x ∈ C ∧ x 2 = false ∧ sixWeight x = 2 ∧ (x 0, x 1) = b := by
    change x ∈ (sixShadow (sixTopFamily C b)).map (liftSlice b) at hx
    obtain ⟨p, hp, he⟩ := mem_map.mp hx
    subst x
    change sliceVertex b (p.map e) ∈ C ∧ _ ∧ _ ∧ _
    have hgeo := (deficit_four_slice_geometry hC hr hb hhalf).2
    have hw : sixWeight (sliceVertex b (p.map e)) = 2 := by
      change (sixSupport (sliceVertex b (p.map e))).card = 2
      rw [sixSupport_sliceVertex]
      exact (mem_powersetCard.mp (mem_filter.mp hp).1).2
    have hz : sliceVertex b (p.map e) 2 = false := by
      change decide ((0 : Fin 7) ∈ p.map e) = false
      apply decide_eq_false
      rintro h
      obtain ⟨j, _, he⟩ := mem_map.mp h
      exact Fin.succ_ne_zero j he
    have hmem : sliceVertex b (p.map e) ∈ C :=
      shadow_selected (C := C) (b := b) (fun s hs => (hgeo b s hs).2) hp
    exact ⟨hmem, hz, hw, rfl⟩
  have hU (x : Q 9) (hx : x ∈ U) :
      x ∈ C ∧ x 2 = false ∧ sixWeight x = 2 ∧
        ((x 0, x 1) = a ∨ (x 0, x 1) = opposite a) := by
    rcases mem_union.mp hx with h | h
    · obtain ⟨hC, hz, hw, he⟩ := hv a x h
      exact ⟨hC, hz, hw, Or.inl he⟩
    · obtain ⟨hC, hz, hw, he⟩ := hv (opposite a) x h
      exact ⟨hC, hz, hw, Or.inr he⟩
  have hdis : Disjoint (pairVertices a) (pairVertices (opposite a)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have he := (hv a x hx).2.2.2.symm.trans (hv (opposite a) x hy).2.2.2
    rcases a with ⟨a, b⟩
    cases a <;> simp [opposite] at he
  have hc := independent_false_side_bound hC hr hb (false_side_card hC hhalf)
    (U := U) (fun x hx => mem_filter.mpr ⟨(hU x hx).1, (hU x hx).2.1⟩)
    (shadow_vertices_opposite_independent a fun x hx => (hU x hx).2)
  change (pairVertices a ∪ pairVertices (opposite a)).card ≤ 22 at hc
  rw [card_union_of_disjoint hdis, hcard, hcard] at hc
  have ha := (shape_of_deficit_four_slice hC hr hb hhalf a).1.1
  have hh := (shape_of_deficit_four_slice hC hr hb hhalf (opposite a)).1.1
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha hh hcounts
  rcases hcounts with (h | h | h) <;> rcases ha with (ha | ha | ha | ha | ha) <;>
    rcases hh with (hh | hh | hh | hh | hh) <;> omega

#print axioms occupied_slices_cannot_be_opposite

private def bits (x : Q 9) : Bool × Bool := (x 0, x 1)

private def zeroDistance (a b : Bool × Bool) : ℕ :=
  (if a.1 ≠ b.1 then 1 else 0) + (if a.2 ≠ b.2 then 1 else 0)

private lemma zeroDistance_cases (a b : Bool × Bool) :
    (zeroDistance a b = 0 ↔ a = b) ∧
    (zeroDistance a b = 2 ↔ b = opposite a) ∧ zeroDistance a b ≤ 2 := by
  rcases a with ⟨a₀, a₁⟩
  rcases b with ⟨b₀, b₁⟩
  cases a₀ <;> cases a₁ <;> cases b₀ <;> cases b₁ <;> decide

private lemma distance_support_relation {x y : Q 9} (hx : x 2 = false) (hy : y 2 = false) :
    hammingDist x y + 2 * ((sixSupport x) ∩ (sixSupport y)).card =
      zeroDistance (bits x) (bits y) + (sixSupport x).card + (sixSupport y).card := by
  classical
  have hi : sixSupport x ∩ sixSupport y =
      univ.filter (fun i : Fin 6 => x i.succ.succ.succ = true ∧ y i.succ.succ.succ = true) := by
    ext i
    simp [sixSupport]
  have hterm (i : Fin 6) :
      (if x i.succ.succ.succ ≠ y i.succ.succ.succ then (1 : ℕ) else 0) +
      2 * (if x i.succ.succ.succ = true ∧ y i.succ.succ.succ = true then 1 else 0) =
      (if x i.succ.succ.succ = true then 1 else 0) +
      (if y i.succ.succ.succ = true then 1 else 0) := by
    cases x i.succ.succ.succ <;> cases y i.succ.succ.succ <;> decide
  have h := sum_congr rfl (fun i (_ : i ∈ (univ : Finset (Fin 6))) => hterm i)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at h
  rw [hi]
  simp only [hammingDist, sixSupport, card_filter]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  change (if x 0 ≠ y 0 then 1 else 0) + ((if x 1 ≠ y 1 then 1 else 0) +
    ((if x 2 ≠ y 2 then 1 else 0) + _)) + _ = _
  rw [hx, hy]
  simp only [ne_self_iff_false, ite_false, zero_add]
  unfold zeroDistance bits
  by_cases h0 : x 0 = y 0 <;> by_cases h1 : x 1 = y 1 <;>
    simp only [h0, h1, not_true_eq_false, not_false_eq_true, ne_self_iff_false,
      ite_true, ite_false] <;> omega

private lemma distance_seven_false_side {x y : Q 9} (hx : x 2 = false) (hy : y 2 = false)
    (h7 : hammingDist x y = 7) (hxw : sixWeight x = 3) (hyw : sixWeight y ≤ 3) :
    Disjoint (sixSupport x) (sixSupport y) ∧
      ((sixWeight y = 2 ∧ bits y = opposite (bits x)) ∨
        (sixWeight y = 3 ∧ bits y ≠ bits x ∧ bits y ≠ opposite (bits x))) := by
  have he := distance_support_relation hx hy
  change hammingDist x y + 2 * ((sixSupport x) ∩ (sixSupport y)).card =
    zeroDistance (bits x) (bits y) + sixWeight x + sixWeight y at he
  rw [h7, hxw] at he
  have hzero := zeroDistance_cases (bits x) (bits y)
  have hin : ((sixSupport x) ∩ (sixSupport y)).card = 0 := by omega
  refine ⟨Finset.disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hin), ?_⟩
  by_cases he : sixWeight y = 2
  · exact Or.inl ⟨he, hzero.2.1.mp (by omega)⟩
  · exact Or.inr ⟨by omega, fun h => by have := hzero.1.mpr h.symm; omega,
      fun h => by have := hzero.2.1.mpr h; omega⟩

private lemma at_least_two_false_partners {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (a : Bool × Bool) {s : Finset (Fin 6)} (hs : s ∈ sixTopFamily C a) :
    2 ≤ (C.filter fun y => hammingDist (sliceVertex a (s.map e)) y = 7 ∧ y 2 = false).card := by
  classical
  let x := sliceVertex a (s.map e)
  obtain ⟨h3, hx⟩ := mem_sixTopFamily.mp hs
  have hs' : s.map e ∈ topFamily C a H := by
    rw [← map_sixTopFamily]
    exact mem_map.mpr ⟨s, hs, rfl⟩
  obtain ⟨h8, hforced⟩ := (deficit_four_slice_geometry hC hr hb hhalf).2 a _ hs'
  have he := slice_top_directions hr a (by rw [card_map, h3]) hx hforced
  have hn : flip x 2 ∉ C := by
    intro h
    have hm := (mem_directions C x 2).mpr h
    change 2 ∈ directions C (sliceVertex a (s.map e)) at hm
    rw [he] at hm
    obtain ⟨i, hi, hei⟩ := mem_map.mp hm
    obtain ⟨j, _, rfl⟩ := mem_map.mp hi
    exact Fin.succ_ne_zero j (Fin.succ_inj.mp (Fin.succ_inj.mp hei))
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hr hb
  have hag := (cube_lifted_agreement_capacity hr hb hd x 2).2 h8
  have hxC : x ∈ C := hx
  simp only [cubePairMembership, show cubeMembership C x = 1 by simp [cubeMembership, hxC],
    show cubeMembership C (flip x 2) = 0 by simp [cubeMembership, hn], mul_zero, sub_zero,
    mul_one, one_mul, sum_cube_membership_property] at hag
  have hx2 : x 2 = false := by
    change decide ((0 : Fin 7) ∈ s.map e) = false
    apply decide_eq_false
    rintro h
    obtain ⟨j, _, he⟩ := mem_map.mp h
    exact Fin.succ_ne_zero j he
  simp only [hx2, eq_comm (a := false)] at hag
  exact_mod_cast hag

#print axioms at_least_two_false_partners

private noncomputable def selectedPairs (C : Finset (Q 9)) (b : Bool × Bool) :
    Finset (Finset (Fin 6)) :=
  ((univ : Finset (Fin 6)).powersetCard 2).filter fun p => liftSlice b p ∈ C

private lemma opposite_pairs_cover {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (a b : Bool × Bool)
    (hslots : ∀ c, (sixTopFamily C c).Nonempty → c = a ∨ c = b) :
    ∀ t ∈ sixTopFamily C a, ∃ p ∈ selectedPairs C (opposite a), Disjoint t p := by
  classical
  intro t ht
  let x := liftSlice a t
  let F := C.filter fun y => hammingDist x y = 7 ∧ y 2 = false
  have hF : 2 ≤ F.card := at_least_two_false_partners hC hr hb hhalf a ht
  have hx2 : x 2 = false := by
    change decide ((0 : Fin 7) ∈ t.map e) = false
    apply decide_eq_false
    rintro h
    obtain ⟨j, _, he⟩ := mem_map.mp h
    exact Fin.succ_ne_zero j he
  have hxa : bits x = a := rfl
  have hxt : sixSupport x = t := sixSupport_sliceVertex a t
  have hxw : sixWeight x = 3 := (congrArg card hxt).trans (mem_sixTopFamily.mp ht).1
  have hcap := (deficit_four_slice_geometry hC hr hb hhalf).1
  have hpartner (y : Q 9) (hy : y ∈ F) :
      Disjoint t (sixSupport y) ∧
        ((sixWeight y = 2 ∧ bits y = opposite a) ∨ (sixWeight y = 3 ∧ bits y = b)) := by
    obtain ⟨hyC, hyD, hy2⟩ := mem_filter.mp hy
    have hw := hcap y hyC
    rw [seven_weight_formula, hy2] at hw
    have hw' : sixWeight y ≤ 3 := by simpa using hw
    have he := distance_seven_false_side hx2 hy2 hyD hxw hw'
    rw [hxt, hxa] at he
    refine ⟨he.1, he.2.imp id (fun h => ⟨h.1, ?_⟩)⟩
    have hry : liftSlice (bits y) (sixSupport y) = y := reconstruct_false_side y hy2
    have hyT : sixSupport y ∈ sixTopFamily C (bits y) :=
      mem_sixTopFamily.mpr ⟨h.1, by
        change liftSlice (bits y) (sixSupport y) ∈ C
        rwa [hry]⟩
    exact (hslots _ ⟨_, hyT⟩).resolve_left h.2.1
  have hpair (y : Q 9) (hy : y ∈ F) (hp : sixWeight y = 2 ∧ bits y = opposite a) :
      ∃ p ∈ selectedPairs C (opposite a), Disjoint t p := by
    obtain ⟨hyC, _, hy2⟩ := mem_filter.mp hy
    have he : liftSlice (bits y) (sixSupport y) = y := reconstruct_false_side y hy2
    rw [hp.2] at he
    have hm : liftSlice (opposite a) (sixSupport y) ∈ C := by rwa [he]
    refine ⟨sixSupport y, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hp.1⟩, hm⟩, ?_⟩
    exact (hpartner y hy).1
  obtain ⟨y, hy, z, hz, hyz⟩ := one_lt_card.mp (by omega : 1 < F.card)
  rcases (hpartner y hy).2 with hp | hyT
  · exact hpair y hy hp
  rcases (hpartner z hz).2 with hp | hzT
  · exact hpair z hz hp
  exfalso
  have hcomp (w : Q 9) (hw : w ∈ F) (h3 : sixWeight w = 3) :
      sixSupport w = univ \ t := by
    apply eq_of_subset_of_card_le
    · intro i hi
      exact mem_sdiff.mpr ⟨mem_univ _, fun hit =>
        (Finset.disjoint_left.mp (hpartner w hw).1) hit hi⟩
    · rw [card_sdiff_of_subset (subset_univ t), card_univ, Fintype.card_fin,
        (mem_sixTopFamily.mp ht).1]
      change 6 - 3 ≤ sixWeight w
      omega
  have hys : liftSlice b (sixSupport y) = y := by
    have he : liftSlice (bits y) (sixSupport y) = y :=
      reconstruct_false_side y (mem_filter.mp hy).2.2
    rwa [hyT.2] at he
  have hzs : liftSlice b (sixSupport z) = z := by
    have he : liftSlice (bits z) (sixSupport z) = z :=
      reconstruct_false_side z (mem_filter.mp hz).2.2
    rwa [hzT.2] at he
  apply hyz
  rw [← hys, ← hzs, hcomp y hy hyT.1, hcomp z hz hzT.1]

private lemma opposite_pair_count {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (a b : Bool × Bool)
    (hslots : ∀ c, (sixTopFamily C c).Nonempty → c = a ∨ c = b) :
    (sixTopFamily C a).card ≤ 2 * (selectedPairs C (opposite a)).card := by
  classical
  let T := sixTopFamily C a
  let P := selectedPairs C (opposite a)
  have hsub : T ⊆ P.biUnion (fun p => T.filter (Disjoint p ·)) := by
    intro t ht
    obtain ⟨p, hp, htp⟩ := opposite_pairs_cover hC hr hb hhalf a b hslots t ht
    exact mem_biUnion.mpr ⟨p, hp, mem_filter.mpr ⟨ht, htp.symm⟩⟩
  have hdeg (p : Finset (Fin 6)) (hp : p ∈ P) : (T.filter (Disjoint p ·)).card ≤ 2 := by
    let s := (univ : Finset (Fin 6)) \ p
    have h2 := (mem_powersetCard.mp (mem_filter.mp hp).1).2
    have hs : s.card = 4 := by
      change (univ \ p).card = 4
      rw [card_sdiff_of_subset (subset_univ p), card_univ, Fintype.card_fin, h2]
    obtain ⟨hcap, hgeo⟩ := deficit_four_slice_geometry hC hr hb hhalf
    have h := (topFamily_four hr hb hcap a H (fun t ht => (hgeo a t ht).2)
      (s.map e) (by rw [card_map, hs]) (map_subset_map.mpr (subset_univ _))).2
    rw [← map_sixTopFamily C a, filter_map, card_map] at h
    change ((sixTopFamily C a).filter (fun t => t.map e ⊆ s.map e)).card ≤ 2 at h
    simp only [map_subset_map] at h
    have he : T.filter (Disjoint p ·) = T.filter (· ⊆ s) := by
      ext t
      simp only [mem_filter]
      refine and_congr_right (fun _ => ⟨?_, ?_⟩)
      · intro ht i hi
        exact mem_sdiff.mpr ⟨mem_univ _, fun hp => (Finset.disjoint_left.mp ht) hp hi⟩
      · intro ht
        exact Finset.disjoint_left.mpr (fun i hp hi => (mem_sdiff.mp (ht hi)).2 hp)
    rwa [he]
  have h := (card_le_card hsub).trans (card_biUnion_le (s := P))
  have hh := sum_le_sum hdeg
  rw [sum_const_nat (fun _ _ => rfl)] at hh
  exact h.trans (hh.trans_eq (Nat.mul_comm _ _))

#print axioms opposite_pair_count

private lemma selected_pair_fiber_le (C : Finset (Q 9)) (b : Bool × Bool) :
    (selectedPairs C b).card ≤
      (C.filter fun x => x 2 = false ∧ bits x = b).card := by
  classical
  apply card_le_card_of_injOn (liftSlice b) _ (liftSlice b).injective.injOn
  intro p hp
  have hm := (mem_filter.mp hp).2
  have hz : (liftSlice b p) 2 = false := by
    change decide ((0 : Fin 7) ∈ p.map e) = false
    apply decide_eq_false
    rintro h
    obtain ⟨j, _, he⟩ := mem_map.mp h
    exact Fin.succ_ne_zero j he
  exact mem_filter.mpr ⟨hm, hz, rfl⟩

private lemma adjacent_slices_excluded {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (a b : Bool × Bool) (hne : a ≠ b) (hnopp : b ≠ opposite a)
    (hslots : ∀ c, (sixTopFamily C c).Nonempty → c = a ∨ c = b)
    (hcounts : ((sixTopFamily C a).card, (sixTopFamily C b).card) ∈
      ([(6, 8), (8, 6), (8, 8)] : List (ℕ × ℕ))) : False := by
  classical
  let L := C.filter fun x => x 2 = false
  let n (c : Bool × Bool) := (L.filter fun x => bits x = c).card
  have hcost (c : Bool × Bool) :
      (sixTopFamily C c).card + (sixShadow (sixTopFamily C c)).card ≤ n c := by
    have h := (shape_of_deficit_four_slice hC hr hb hhalf c).2
    have he : C.filter (fun x => x 0 = c.1 ∧ x 1 = c.2 ∧ x 2 = false) =
        L.filter (fun x => bits x = c) := by
      ext x
      rcases c with ⟨c₀, c₁⟩
      simp only [L, bits, mem_filter, Prod.mk.injEq]
      tauto
    rwa [he] at h
  have hcost_a := hcost a
  have hcost_b := hcost b
  have ha := (shape_of_deficit_four_slice hC hr hb hhalf a).1.1
  have hB := (shape_of_deficit_four_slice hC hr hb hhalf b).1.1
  have hpair_a := opposite_pair_count hC hr hb hhalf a b hslots
  have hpair_b := opposite_pair_count hC hr hb hhalf b a (fun c hc => (hslots c hc).symm)
  have hna : (selectedPairs C (opposite a)).card ≤ n (opposite a) := by
    simpa only [n, L, filter_filter] using selected_pair_fiber_le C (opposite a)
  have hnb : (selectedPairs C (opposite b)).card ≤ n (opposite b) := by
    simpa only [n, L, filter_filter] using selected_pair_fiber_le C (opposite b)
  have inv : Function.Involutive opposite := by
    intro c
    rcases c with ⟨c₀, c₁⟩
    simp [opposite]
  have diff (c : Bool × Bool) : c ≠ opposite c := by
    rcases c with ⟨c₀, c₁⟩
    cases c₀ <;> simp [opposite]
  have haob : a ≠ opposite b := fun h => hnopp (((congrArg opposite h).trans (inv b)).symm)
  have hoab : opposite a ≠ opposite b := fun h => hne (inv.injective h)
  have hsum : (∑ c ∈ (univ : Finset (Bool × Bool)), n c) = 41 := by
    change (∑ c ∈ (univ : Finset (Bool × Bool)), (L.filter fun x => bits x = c).card) = 41
    rw [← card_eq_sum_card_fiberwise (f := bits) (fun _ _ => mem_univ _)]
    exact false_side_card hC hhalf
  have hfour := sum_le_sum_of_subset (f := n)
    (subset_univ ({a, b, opposite a, opposite b} : Finset (Bool × Bool)))
  rw [hsum, sum_insert (by simp [hne, diff a, haob]),
    sum_insert (by simp [hnopp, diff b]),
    sum_insert (fun h => hoab (mem_singleton.mp h)), sum_singleton] at hfour
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha hB hcounts
  rcases hcounts with (h | h | h) <;> rcases ha with (ha | ha | ha | ha | ha) <;>
    rcases hB with (hc | hc | hc | hc | hc) <;> omega

/-- The deficit-four profile with two zero deficits and six deficit-five
coordinates is impossible for a balanced cubic support of size 66. -/
theorem q9_sixty_six_excludes_004555555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![0, 0, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  classical
  have hre : deficit = ![0, 0, 4, 5, 5, 5, 5, 5, 5] := by decide +kernel
  rw [← hre] at hhalf
  obtain ⟨a, b, hne, hslots, _, hcounts⟩ := two_nonempty_slices hC hr hb hhalf
  by_cases h : b = opposite a
  · subst b
    exact occupied_slices_cannot_be_opposite hC hr hb hhalf a hcounts
  · apply adjacent_slices_excluded hC hr hb hhalf a b hne h _ hcounts
    intro c hc
    have hm : c ∈ (univ : Finset (Bool × Bool)).filter (fun c => (sixTopFamily C c).Nonempty) :=
      mem_filter.mpr ⟨mem_univ _, hc⟩
    simpa [hslots] using hm

#print axioms q9_sixty_six_excludes_004555555

def sixtySixProfilesAfterSixCoordinateSlices : List (List ℤ) :=
  sixtySixProfilesAfterTopTriples.filter (· != [0, 0, 4, 5, 5, 5, 5, 5, 5])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
-- Kernel reduction also evaluates the preceding profile filters.
theorem sixtySixProfilesAfterSixCoordinateSlices_length :
    sixtySixProfilesAfterSixCoordinateSlices.length = 36 := by
  decide +kernel

theorem q9_sixty_six_mem_profiles_after_six_coordinate_slices
    {C : Finset (Q 9)} (hC : C.card = 66)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∃ (S : Finset (Q 9)) (r : Fin 9 → ℤ),
      S.card = 66 ∧ ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced S ∧ (∀ i, ((S.filter (fun x => x i = true)).card : ℤ) + 2 * r i = 33) ∧
      List.ofFn r ∈ sixtySixProfilesAfterSixCoordinateSlices := by
  obtain ⟨S, r, hS, hregS, hbS, hhalf, hp⟩ := q9_sixty_six_mem_profiles_after_top_triples hC hr hb
  refine ⟨S, r, hS, hregS, hbS, hhalf, ?_⟩
  rw [sixtySixProfilesAfterSixCoordinateSlices, List.mem_filter]
  refine ⟨hp, bne_iff_ne.mpr ?_⟩
  intro he
  have hv : List.ofFn (![0, 0, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) =
      [0, 0, 4, 5, 5, 5, 5, 5, 5] := by decide +kernel
  have hvec := List.ofFn_inj.mp (he.trans hv.symm)
  subst r
  exact q9_sixty_six_excludes_004555555 hS hregS hbS hhalf

#print axioms q9_sixty_six_mem_profiles_after_six_coordinate_slices

end D5.S3.Combinatorics.Graph.HypercubeCritical

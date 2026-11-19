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
  sliceVertex_injective topFamily mem_topFamily topFamily_four topFamily_pair
  one_more_coordinate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySix015555555Probe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe

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

end D5.S3.Combinatorics.Graph.HypercubeCritical

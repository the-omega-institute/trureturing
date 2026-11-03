/- GID: D5/S3/Combinatorics/BinomialBases/MazorchukXuNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/BinomialBases/MazorchukXuNormalization
   mirror-E: none(waiver:prescribed-support-coordinate-bijections)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Prescribed positive coordinate supports have size-independent admissible fibers. -/

import D5.S3.Combinatorics.BinomialBases.MazorchukXuReconstruction

/-! Normalization uses the increasing isomorphism onto a prescribed finite support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MazorchukXu

/-- All positive values used by either coordinate array, retaining zero as a separate anchor. -/
def coordinateDataSupport {M i : ℕ} (d : CoordinateDataCarrier M i) : Finset (Fin (M + 1)) :=
  ((Finset.univ.image d.1) ∪ (Finset.univ.image d.2.1)).erase 0

private theorem coordinateDataSupport_subset {M i : ℕ} (d : CoordinateDataCarrier M i) :
    coordinateDataSupport d ⊆ Finset.univ.erase 0 := by
  intro a ha
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, Finset.mem_univ _⟩

private theorem coordinateDataSupport_card_le {M i : ℕ} (d : CoordinateDataCarrier M i) :
    (coordinateDataSupport d).card ≤ 2 * i := by
  have h₀ : (((Finset.univ.image d.1) ∪ (Finset.univ.image d.2.1)).erase 0).card ≤
      ((Finset.univ.image d.1) ∪ (Finset.univ.image d.2.1)).card := Finset.card_erase_le
  have h₁ := Finset.card_union_le (Finset.univ.image d.1) (Finset.univ.image d.2.1)
  have hp : (Finset.univ.image d.1).card ≤ i := by
    exact Finset.card_image_le.trans (by simp)
  have hc : (Finset.univ.image d.2.1).card ≤ i := by
    exact Finset.card_image_le.trans (by simp)
  unfold coordinateDataSupport
  omega

private def mapCoordinateData {M K i : ℕ} (e : Fin (K + 1) ↪o Fin (M + 1))
    (d : CoordinateDataCarrier K i) : CoordinateDataCarrier M i :=
  (e ∘ d.1, e ∘ d.2.1, d.2.2)

private theorem mapCoordinateData_injective {M K i : ℕ} (e : Fin (K + 1) ↪o Fin (M + 1)) :
    Function.Injective (mapCoordinateData (i := i) e) := by
  intro x y h
  apply Prod.ext
  · funext j
    exact e.injective (congrFun (congrArg Prod.fst h) j)
  · apply Prod.ext
    · funext j
      exact e.injective (congrFun (congrArg (fun d => d.2.1) h) j)
    · exact congrArg (fun d => d.2.2) h

private theorem coordinateDataSupport_map {M K i : ℕ}
    (e : Fin (K + 1) ↪o Fin (M + 1)) (he0 : e 0 = 0) (d : CoordinateDataCarrier K i) :
    coordinateDataSupport (mapCoordinateData e d) = (coordinateDataSupport d).image e := by
  unfold coordinateDataSupport mapCoordinateData
  rw [Finset.image_erase e.injective, he0, Finset.image_union]
  simp only [Finset.image_image, Function.comp_def]

private def extendRankEmbedding {M K : ℕ} (e : Fin (K + 1) ↪o Fin (M + 1)) (r : ℕ) : ℕ :=
  if hr : r ≤ K then (e ⟨r, by omega⟩).val else (e ⟨K, by omega⟩).val + (r - K)

private theorem extendRankEmbedding_apply {M K : ℕ}
    (e : Fin (K + 1) ↪o Fin (M + 1)) (r : Fin (K + 1)) :
    extendRankEmbedding e r.val = (e r).val := by
  simp only [extendRankEmbedding, dite_eq_left (Nat.le_of_lt_succ r.isLt)]

private theorem extendRankEmbedding_strictMono {M K : ℕ}
    (e : Fin (K + 1) ↪o Fin (M + 1)) : StrictMono (extendRankEmbedding e) := by
  intro r s hrs
  by_cases hr : r ≤ K
  · by_cases hs : s ≤ K
    · simp only [extendRankEmbedding, dite_eq_left hr, dite_eq_left hs]
      exact e.strictMono (show (⟨r, by omega⟩ : Fin (K + 1)) < ⟨s, by omega⟩ from hrs)
    · simp only [extendRankEmbedding, dite_eq_left hr, dite_eq_right hs]
      have hh : (e ⟨r, by omega⟩).val ≤ (e ⟨K, by omega⟩).val := e.monotone hr
      omega
  · have hs : ¬ s ≤ K := by omega
    simp only [extendRankEmbedding, dite_eq_right hr, dite_eq_right hs]
    omega

private theorem mapCoordinateData_mem_iff {M K i : ℕ}
    (e : Fin (K + 1) ↪o Fin (M + 1)) (he0 : e 0 = 0) (d : CoordinateDataCarrier K i) :
    mapCoordinateData e d ∈ coordinateDataFamily M i ↔ d ∈ coordinateDataFamily K i := by
  classical
  let p : Fin i → ℕ := fun j => (d.1 j).val
  let c : Fin i → ℕ := fun j => (d.2.1 j).val
  let B := fun j k => (j, k) ∈ d.2.2
  have hext0 : extendRankEmbedding e 0 = 0 := by
    have h := extendRankEmbedding_apply e (0 : Fin (K + 1))
    simpa only [he0, Fin.val_zero] using h
  have hpm : Monotone (fun j => (e (d.1 j)).val) ↔ Monotone p := by
    constructor
    · intro h j k hjk
      exact e.le_iff_le.mp (h hjk)
    · intro h j k hjk
      exact e.monotone (h hjk)
  have hR : Rules (boundedCoordinateEdges M (fun j => (e (d.1 j)).val)
      (fun j => (e (d.2.1 j)).val) B) ↔ Rules (boundedCoordinateEdges K p c B) := by
    rw [coordinate_rules_bounded_iff M _ _ B
      (fun j => Nat.le_of_lt_succ (e (d.1 j)).isLt)
      (fun j => Nat.le_of_lt_succ (e (d.2.1 j)).isLt),
      coordinate_rules_bounded_iff K p c B
      (fun j => Nat.le_of_lt_succ (d.1 j).isLt)
      (fun j => Nat.le_of_lt_succ (d.2.1 j).isLt)]
    have h := coordinate_rules_refinement_iff p c B (extendRankEmbedding e)
      (extendRankEmbedding_strictMono e) hext0
    have hpe : extendRankEmbedding e ∘ p = (fun j => (e (d.1 j)).val) := by
      funext j
      exact extendRankEmbedding_apply e (d.1 j)
    have hce : extendRankEmbedding e ∘ c = (fun j => (e (d.2.1 j)).val) := by
      funext j
      exact extendRankEmbedding_apply e (d.2.1 j)
    rw [← hpe, ← hce]
    exact h
  simp only [coordinateDataFamily, Finset.mem_filter, Finset.mem_univ, true_and]
  change (Monotone (fun j => (e (d.1 j)).val) ∧ (∀ j k, B j k → j < k) ∧
      Rules (boundedCoordinateEdges M (fun j => (e (d.1 j)).val)
        (fun j => (e (d.2.1 j)).val) B)) ↔
    (Monotone p ∧ (∀ j k, B j k → j < k) ∧ Rules (boundedCoordinateEdges K p c B))
  rw [hpm, hR]

/-- The number of admissible patterns using every positive coordinate from 1 through k. -/
noncomputable def patternCoefficient (i k : ℕ) : ℕ :=
  ((coordinateDataFamily k i).filter (fun d => coordinateDataSupport d = Finset.univ.erase 0)).card

/-- For any prescribed positive support S, its admissible coordinate fiber is counted
by the same coefficient depending only on i and the cardinality of S. -/
theorem coordinateDataSupport_fiber_card {M i : ℕ} (S : Finset (Fin (M + 1)))
    (hS : S ⊆ Finset.univ.erase 0) :
    ((coordinateDataFamily M i).filter (fun d => coordinateDataSupport d = S)).card =
      patternCoefficient i S.card := by
  classical
  have h0S : (0 : Fin (M + 1)) ∉ S := by
    intro h
    exact (Finset.mem_erase.mp (hS h)).1 rfl
  let T := insert 0 S
  have hT : T.card = S.card + 1 := by simp [T, h0S]
  let e : Fin (S.card + 1) ↪o Fin (M + 1) := T.orderEmbOfFin hT
  have hemem : ∀ r, e r ∈ T := T.orderEmbOfFin_mem hT
  have herange : ∀ a ∈ T, ∃ r, e r = a := by
    intro a ha
    obtain ⟨r, hr⟩ := (T.orderIsoOfFin hT).surjective ⟨a, ha⟩
    exact ⟨r, congrArg Subtype.val hr⟩
  have he0 : e 0 = 0 := by
    obtain ⟨r, hr⟩ := herange 0 (Finset.mem_insert_self _ _)
    apply le_antisymm
    · simpa only [hr] using e.monotone (Fin.zero_le r)
    · exact Fin.zero_le _
  have heimage : (Finset.univ.erase 0).image e = S := by
    ext a
    constructor
    · intro ha
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
      have hne : e r ≠ 0 := by
        intro h
        exact (Finset.mem_erase.mp hr).1 (e.injective (h.trans he0.symm))
      exact (Finset.mem_insert.mp (hemem r)).resolve_left hne
    · intro ha
      obtain ⟨r, hr⟩ := herange a (Finset.mem_insert_of_mem ha)
      refine Finset.mem_image.mpr ⟨r, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hr⟩
      intro h
      subst r
      have ha0 : a = 0 := hr.symm.trans he0
      exact h0S (by simpa only [ha0] using ha)
  unfold patternCoefficient
  symm
  apply Finset.card_bij (fun d _ => mapCoordinateData e d)
  · intro d hd
    obtain ⟨hd, hs⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    exact ⟨(mapCoordinateData_mem_iff e he0 d).mpr hd,
      by rw [coordinateDataSupport_map e he0, hs, heimage]⟩
  · intro d hd f hf hdf
    exact mapCoordinateData_injective e hdf
  · intro d hd
    obtain ⟨hd, hds⟩ := Finset.mem_filter.mp hd
    have hvalues : ∀ a, a ∈ Finset.univ.image d.1 ∪ Finset.univ.image d.2.1 → a ∈ T := by
      intro a ha
      by_cases hzero : a = 0
      · simpa only [hzero] using Finset.mem_insert_self (0 : Fin (M + 1)) S
      · apply Finset.mem_insert_of_mem
        rw [← hds]
        exact Finset.mem_erase.mpr ⟨hzero, ha⟩
    let pp : Fin i → Fin (S.card + 1) := fun j => (T.orderIsoOfFin hT).symm
      ⟨d.1 j, hvalues _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    let cc : Fin i → Fin (S.card + 1) := fun j => (T.orderIsoOfFin hT).symm
      ⟨d.2.1 j, hvalues _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    let q : CoordinateDataCarrier S.card i := (pp, cc, d.2.2)
    have hback : mapCoordinateData e q = d := by
      apply Prod.ext
      · funext j
        exact congrArg Subtype.val ((T.orderIsoOfFin hT).apply_symm_apply _)
      · apply Prod.ext
        · funext j
          exact congrArg Subtype.val ((T.orderIsoOfFin hT).apply_symm_apply _)
        · rfl
    refine ⟨q, Finset.mem_filter.mpr ⟨?_, ?_⟩, hback⟩
    · exact (mapCoordinateData_mem_iff e he0 q).mp (hback.symm ▸ hd)
    · apply Finset.image_injective e.injective
      rw [← coordinateDataSupport_map e he0, hback, hds, heimage]

private theorem coordinateDataFamily_card_eq_sum (M i : ℕ) :
    (coordinateDataFamily M i).card =
      ∑ k ∈ Finset.range (2 * i + 1), patternCoefficient i k * M.choose k := by
  classical
  let D := coordinateDataFamily M i
  let U : Finset (Fin (M + 1)) := Finset.univ.erase 0
  have hU : U.card = M := by simp [U]
  have hgroup (k : ℕ) :
      (D.filter (fun d => (coordinateDataSupport d).card = k)).card =
        patternCoefficient i k * M.choose k := by
    have hmap : (↑(D.filter (fun d => (coordinateDataSupport d).card = k)) :
        Set (CoordinateDataCarrier M i)).MapsTo coordinateDataSupport (U.powersetCard k) := by
      intro d hd
      exact Finset.mem_powersetCard.mpr ⟨coordinateDataSupport_subset d,
        (Finset.mem_filter.mp hd).2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    calc
      (∑ S ∈ U.powersetCard k,
        ((D.filter (fun d => (coordinateDataSupport d).card = k)).filter
          (fun d => coordinateDataSupport d = S)).card) =
          ∑ S ∈ U.powersetCard k, patternCoefficient i k := by
        apply Finset.sum_congr rfl
        intro S hS
        obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
        have hfilter : (D.filter (fun d => (coordinateDataSupport d).card = k)).filter
            (fun d => coordinateDataSupport d = S) = D.filter (fun d => coordinateDataSupport d = S) := by
          ext d
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hd, _⟩, hs⟩
            exact ⟨hd, hs⟩
          · rintro ⟨hd, hs⟩
            exact ⟨⟨hd, by rw [hs, hcard]⟩, hs⟩
        rw [hfilter]
        simpa only [hcard] using coordinateDataSupport_fiber_card S hsub
      _ = patternCoefficient i k * M.choose k := by
        simp only [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, hU]
        exact Nat.mul_comm _ _
  have hmap : (↑D : Set (CoordinateDataCarrier M i)).MapsTo
      (fun d => (coordinateDataSupport d).card) (Finset.range (2 * i + 1)) := by
    intro d hd
    apply Finset.mem_range.mpr
    change (coordinateDataSupport d).card < 2 * i + 1
    have := coordinateDataSupport_card_le d
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  exact Finset.sum_congr rfl (fun k _ => hgroup k)

/-- The exact binomial-basis identity for the literal count, including every zero/tie
pattern and every original valid n, with coefficients independent of n. -/
theorem count_eq_binomial_sum {n i : ℕ} (hi : i ≤ n + 1) :
    count n (n + 1 - i) = ∑ k ∈ Finset.range (2 * i + 1),
      patternCoefficient i k * (n + 1 - i).choose k := by
  rw [count_eq_coordinateDataFamily_card hi]
  exact coordinateDataFamily_card_eq_sum _ _

end D5.S3.Combinatorics.MazorchukXu

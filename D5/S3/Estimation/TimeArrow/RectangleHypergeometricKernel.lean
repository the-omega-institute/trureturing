/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricKernel
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform labelled four-cell tables have the exact hypergeometric intersection kernel. -/

import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
noncomputable section

/-- A fixed first margin, and a uniformly chosen second margin of size U.
The A cell is the intersection of the two labelled margins. -/
def intersectionEvent {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ) :
    Finset (Finset α) := (V.powersetCard U).filter fun B => (B ∩ R).card = t

/-- Split a table's second margin into its portions inside and outside the
first margin, retaining the original labels. -/
def intersectionSplit {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ)
    (hR : R ⊆ V) (ht : t ≤ U) :
    {B : Finset α // B ∈ intersectionEvent V R U t} ≃
      {A : Finset α // A ∈ R.powersetCard t} ×
      {D : Finset α // D ∈ (V \ R).powersetCard (U - t)} where
  toFun B := by
    have hB := mem_filter.mp B.property
    have hBV := (mem_powersetCard.mp hB.1).1
    have hBU := (mem_powersetCard.mp hB.1).2
    refine (⟨B.val ∩ R, mem_powersetCard.mpr ⟨inter_subset_right, hB.2⟩⟩,
      ⟨B.val \ R, mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff_left R hBV, ?_⟩⟩)
    rw [card_sdiff, hBU, inter_comm R, hB.2]
  invFun P := by
    have hA := mem_powersetCard.mp P.1.property
    have hD := mem_powersetCard.mp P.2.property
    have hd : Disjoint P.1.val P.2.val := disjoint_left.mpr fun x hxA hxD =>
      (mem_sdiff.mp (hD.1 hxD)).2 (hA.1 hxA)
    refine ⟨P.1.val ∪ P.2.val, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · exact union_subset (hA.1.trans hR) (hD.1.trans sdiff_subset)
    · rw [card_union_of_disjoint hd, hA.2, hD.2, Nat.add_sub_of_le ht]
    · have hi : (P.1.val ∪ P.2.val) ∩ R = P.1.val := by
        have hdR : Disjoint P.2.val R :=
          disjoint_of_subset_left hD.1 disjoint_sdiff_self_left
        rw [union_inter_distrib_right, Finset.inter_eq_left.mpr hA.1,
          disjoint_iff_inter_eq_empty.mp hdR, union_empty]
      rw [hi, hA.2]
  left_inv B := by
    apply Subtype.ext
    change (B.val ∩ R) ∪ (B.val \ R) = B.val
    rw [union_comm, sdiff_union_inter]
  right_inv P := by
    apply Prod.ext <;> apply Subtype.ext
    · ext x
      have hA := (mem_powersetCard.mp P.1.property).1
      have hD := (mem_powersetCard.mp P.2.property).1
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx | hx, hr⟩
        · exact hx
        · exact False.elim ((mem_sdiff.mp (hD hx)).2 hr)
      · intro hx; exact ⟨Or.inl hx, hA hx⟩
    · ext x
      have hA := (mem_powersetCard.mp P.1.property).1
      have hD := (mem_powersetCard.mp P.2.property).1
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hr⟩
        · exact False.elim (hr (hA hx))
        · exact hx
      · intro hx; exact ⟨Or.inr hx, (mem_sdiff.mp (hD hx)).2⟩

/-- Exact counting law before normalization; the two margins refer to the
same labelled table. -/
theorem rectangle_intersection_card {α : Type*} [DecidableEq α]
    (V R : Finset α) (U t : ℕ) (hR : R ⊆ V) (ht : t ≤ U) :
    (intersectionEvent V R U t).card = R.card.choose t * (V.card - R.card).choose (U - t) := by
  have hc := Fintype.card_congr (intersectionSplit V R U t hR ht)
  simpa only [Fintype.card_coe, Fintype.card_prod, card_powersetCard,
    card_sdiff_of_subset hR] using hc

/-- The mass of the A-cell count, under the uniform second-margin law. -/
def rectangleMass {α : Type*} [DecidableEq α] (V R : Finset α) (U t : ℕ) : ℝ :=
  (intersectionEvent V R U t).card / (V.powersetCard U).card

/-- The exact hypergeometric formula for the finite labelled table law. -/
theorem rectangle_hypergeometric_mass {α : Type*} [DecidableEq α]
    (V R : Finset α) (U t : ℕ) (hR : R ⊆ V) (ht : t ≤ U) :
    rectangleMass V R U t =
      ((R.card.choose t : ℝ) * ((V.card - R.card).choose (U - t) : ℝ)) /
        (V.card.choose U : ℝ) := by
  simp only [rectangleMass, rectangle_intersection_card V R U t hR ht,
    card_powersetCard, Nat.cast_mul]

/-- The negative counts in the rectangle take the two adjacent values.
Outside rows retain their full labelled count array. -/
def rectangleNegativeCounts {α : Type*} [DecidableEq α]
    (V B : Finset α) (outside : α → ℕ) (l : ℕ) (i : α) : ℕ :=
  if i ∈ V then if i ∈ B then l else l + 1 else outside i

private theorem rectangle_counts_sum {α : Type*} [Fintype α] [DecidableEq α]
    (V B : Finset α) (outside : α → ℕ) (l U : ℕ) (hB : B ∈ V.powersetCard U) :
    (∑ i, rectangleNegativeCounts V B outside l i) =
      (∑ i ∈ univ \ V, outside i) + U * l + (V.card - U) * (l + 1) := by
  have hBV := (mem_powersetCard.mp hB).1
  have hBU := (mem_powersetCard.mp hB).2
  have hsplit := (sum_filter_add_sum_filter_not univ (fun i => i ∈ V)
    (rectangleNegativeCounts V B outside l)).symm
  simp only [filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff] at hsplit
  rw [hsplit]
  have hin : (∑ i ∈ V, rectangleNegativeCounts V B outside l i) =
      U * l + (V.card - U) * (l + 1) := by
    calc
      _ = ∑ i ∈ V, if i ∈ B then l else l + 1 := by
        apply sum_congr rfl
        intro i hi
        simp only [rectangleNegativeCounts, if_pos hi]
      _ = _ := by
        rw [sum_ite]
        simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff,
          inter_eq_right.mpr hBV, sum_const, nsmul_eq_mul,
          card_sdiff_of_subset hBV, hBU, Nat.cast_id]
  have hout : (∑ i ∈ univ \ V, rectangleNegativeCounts V B outside l i) =
      ∑ i ∈ univ \ V, outside i := by
    apply sum_congr rfl
    intro i hi
    simp only [rectangleNegativeCounts, if_neg (mem_sdiff.mp hi).2]
  rw [hin, hout]
  omega

private theorem rectangle_counts_factorials {α : Type*} [Fintype α] [DecidableEq α]
    (V B : Finset α) (outside : α → ℕ) (l U : ℕ) (hB : B ∈ V.powersetCard U) :
    (∏ i, (rectangleNegativeCounts V B outside l i).factorial) =
      (∏ i ∈ univ \ V, (outside i).factorial) *
        l.factorial ^ U * (l + 1).factorial ^ (V.card - U) := by
  have hBV := (mem_powersetCard.mp hB).1
  have hBU := (mem_powersetCard.mp hB).2
  have hsplit := (prod_filter_mul_prod_filter_not univ (fun i => i ∈ V)
    (fun i => (rectangleNegativeCounts V B outside l i).factorial)).symm
  simp only [filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff] at hsplit
  rw [hsplit]
  have hin : (∏ i ∈ V, (rectangleNegativeCounts V B outside l i).factorial) =
      l.factorial ^ U * (l + 1).factorial ^ (V.card - U) := by
    calc
      _ = ∏ i ∈ V, if i ∈ B then l.factorial else (l + 1).factorial := by
        apply prod_congr rfl
        intro i hi
        simp only [rectangleNegativeCounts, if_pos hi, apply_ite Nat.factorial]
      _ = _ := by
        rw [prod_ite]
        simp only [filter_mem_eq_inter, filter_notMem_eq_sdiff,
          inter_eq_right.mpr hBV, prod_const, card_sdiff_of_subset hBV, hBU]
  have hout : (∏ i ∈ univ \ V, (rectangleNegativeCounts V B outside l i).factorial) =
      ∏ i ∈ univ \ V, (outside i).factorial := by
    apply prod_congr rfl
    intro i hi
    simp only [rectangleNegativeCounts, if_neg (mem_sdiff.mp hi).2]
  rw [hin, hout]
  ac_rfl

private theorem rectangle_multinomial_constant {α : Type*} [Fintype α] [DecidableEq α]
    (V B C : Finset α) (outside : α → ℕ) (l U : ℕ)
    (hB : B ∈ V.powersetCard U) (hC : C ∈ V.powersetCard U) :
    Nat.multinomial univ (rectangleNegativeCounts V B outside l) =
      Nat.multinomial univ (rectangleNegativeCounts V C outside l) := by
  unfold Nat.multinomial
  rw [rectangle_counts_sum V B outside l U hB,
    rectangle_counts_sum V C outside l U hC,
    rectangle_counts_factorials V B outside l U hB,
    rectangle_counts_factorials V C outside l U hC]


open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber

/-- Native joint-histogram events compatible with fixed outside rows,
fixed positive counts, and a fixed negative margin within the rectangle. -/
def nativeRectangleEvent {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (ap : Multiset {i : Fin M // i ∈ S.val})
    (V : Finset {i : Fin M // i ∈ S.val}) (outside : {i : Fin M // i ∈ S.val} → ℕ)
    (l : ℕ) (Bs : Finset (Finset {i : Fin M // i ∈ S.val})) : Finset (Fiber S e o) := by
  classical
  exact Bs.biUnion fun B => jointRowHistogramEvent S e o ap
    (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset

private theorem rectangle_histogram_disjoint {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (ap : Multiset {i : Fin M // i ∈ S.val})
    (V : Finset {i : Fin M // i ∈ S.val}) (outside : {i : Fin M // i ∈ S.val} → ℕ)
    (l U : ℕ) : Set.PairwiseDisjoint (↑(V.powersetCard U))
      (fun B => jointRowHistogramEvent S e o ap
        (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset) := by
  classical
  intro B hB C hC hBC
  apply disjoint_left.mpr
  intro y hyB hyC
  have hBval := (mem_powersetCard.mp hB).1
  have hCval := (mem_powersetCard.mp hC).1
  have hy (D : Finset {i : Fin M // i ∈ S.val})
      (h : y ∈ jointRowHistogramEvent S e o ap
        (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V D outside l)).toMultiset)
      (i : {i : Fin M // i ∈ S.val}) :
      count e y.val i.val (-1) = rectangleNegativeCounts V D outside l i := by
    have hd := ((mem_filter.mp h).2 i).2
    simpa only [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm] using hd
  apply hBC
  ext i
  by_cases hiV : i ∈ V
  · have hi := (hy B hyB i).symm.trans (hy C hyC i)
    dsimp only [rectangleNegativeCounts] at hi
    simp only [if_pos hiV] at hi
    by_cases hiB : i ∈ B <;> by_cases hiC : i ∈ C <;>
      simp only [hiB, hiC, if_true, if_false] at hi ⊢ <;> omega
  · exact ⟨fun hi => False.elim (hiV (hBval hi)),
      fun hi => False.elim (hiV (hCval hi))⟩

/-- Conditional mass on the original native histories after fixing the
complete outside-row array and both rectangle margins. -/
def nativeRectangleConditionalMass {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e) (ap : Multiset {i : Fin M // i ∈ S.val})
    (V R : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (l U t : ℕ) : ℝ :=
  conditionalFiberMass S r e o
      (nativeRectangleEvent S e o ap V outside l (intersectionEvent V R U t)) /
    conditionalFiberMass S r e o
      (nativeRectangleEvent S e o ap V outside l (V.powersetCard U))

/-- Exact pair/path conditional hypergeometric law obtained from the
native joint-row histogram pushforward. No independent-row assumption is used. -/
theorem native_rectangle_hypergeometric_law {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (ap : Multiset {i : Fin M // i ∈ S.val})
    (V R : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (l U t : ℕ)
    (hap : ap.card = (signedDepartureBlocks S e o 0).card)
    (hneg : (∑ i ∈ univ \ V, outside i) + U * l + (V.card - U) * (l + 1) =
      (signedDepartureBlocks S e o 1).card)
    (hU : U ≤ V.card) (hR : R ⊆ V) (ht : t ≤ U) :
    nativeRectangleConditionalMass S r e o ap V R outside l U t =
      ((R.card.choose t : ℝ) * ((V.card - R.card).choose (U - t) : ℝ)) /
        (V.card.choose U : ℝ) := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  obtain ⟨B0, hB0⟩ := powersetCard_nonempty.mpr hU
  let c : ℝ := ((Nat.multinomial univ ap.count : ℝ) *
      (Nat.multinomial univ (rectangleNegativeCounts V B0 outside l) : ℝ)) /
    (q : ℝ) ^ ((signedDepartureBlocks S e o 0).card + (signedDepartureBlocks S e o 1).card)
  have hc : 0 < c := by
    dsimp [c]
    apply div_pos
    · apply mul_pos <;> exact_mod_cast Nat.multinomial_pos _ _
    · exact pow_pos (by exact_mod_cast (by omega : 0 < q)) _
  have hmass (B : Finset {i : Fin M // i ∈ S.val}) (hB : B ∈ V.powersetCard U) :
      conditionalFiberMass S r e o (jointRowHistogramEvent S e o ap
        (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset) = c := by
    have hcard : (Finsupp.equivFunOnFinite.symm
        (rectangleNegativeCounts V B outside l)).toMultiset.card =
          (signedDepartureBlocks S e o 1).card := by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype]
      · exact (rectangle_counts_sum V B outside l U hB).trans hneg
      · intro; rfl
    rw [native_joint_row_histogram_law S r e o hq hqm hr hr1 ha ha1 _ _ hap hcard]
    simp only [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm]
    rw [rectangle_multinomial_constant V B B0 outside l U hB hB0]
  have hsum (Bs : Finset (Finset {i : Fin M // i ∈ S.val}))
      (hBs : Bs ⊆ V.powersetCard U) :
      conditionalFiberMass S r e o (nativeRectangleEvent S e o ap V outside l Bs) =
        (Bs.card : ℝ) * c := by
    have hd : Set.PairwiseDisjoint (↑Bs)
        (fun B => jointRowHistogramEvent S e o ap
          (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset) := by
      intro B hB C hC hBC
      exact rectangle_histogram_disjoint S e o ap V outside l U (hBs hB) (hBs hC) hBC
    unfold conditionalFiberMass nativeRectangleEvent
    rw [sum_biUnion hd, sum_div]
    change (∑ B ∈ Bs, conditionalFiberMass S r e o (jointRowHistogramEvent S e o ap
      (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset)) = _
    rw [sum_congr rfl (fun B hB => hmass B (hBs hB))]
    simp only [sum_const, nsmul_eq_mul]
  unfold nativeRectangleConditionalMass
  rw [hsum (intersectionEvent V R U t) (filter_subset _ _),
    hsum (V.powersetCard U) (Subset.refl _)]
  rw [mul_div_mul_right _ _ (ne_of_gt hc)]
  exact rectangle_hypergeometric_mass V R U t hR ht

/-- The actual signal rows whose count pair lies in the four adjacent cells. -/
def nativeRectangleRows {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (y : Fiber S e o) : Finset {i : Fin M // i ∈ S.val} := by
  classical
  exact univ.filter fun i =>
    (count e y.val i.val 1 = k ∨ count e y.val i.val 1 = k + 1) ∧
    (count e y.val i.val (-1) = l ∨ count e y.val i.val (-1) = l + 1)

/-- This finite conditioning readout keeps the complete positive histogram,
rectangle membership, every negative count outside it, and its negative margin.
The full positive histogram determines its labelled first margin. -/
def nativeRectangleReadout {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (y : Fiber S e o) :
    ({i : Fin M // i ∈ S.val} → ℕ) × Finset {i : Fin M // i ∈ S.val} ×
      ({i : Fin M // i ∈ S.val} → Option ℕ) × ℕ := by
  classical
  let V := nativeRectangleRows S e o k l y
  exact (fun i => count e y.val i.val 1, V,
    (fun i => if i ∈ V then none else some (count e y.val i.val (-1))),
    (V.filter fun i => count e y.val i.val (-1) = l).card)

/-- The sigma-algebra generated by this complete rectangle environment,
inside the already fixed complete collapsed-history fiber. -/
def nativeRectangleSigma {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) : MeasurableSpace (Fiber S e o) :=
  MeasurableSpace.comap (nativeRectangleReadout S e o k l) ⊤

/-- The exact finite environment data matching the conditional event. -/
def rectangleEnvironmentData {α : Type*} [DecidableEq α]
    (ap : Multiset α) (V : Finset α) (outside : α → ℕ) (U : ℕ) :
    (α → ℕ) × Finset α × (α → Option ℕ) × ℕ :=
  (ap.count, V, (fun i => if i ∈ V then none else some (outside i)), U)

/-- The conditioning event is precisely a fiber of the native readout,
with actual rectangle membership and all labelled outside counts retained. -/
theorem native_rectangle_readout_fiber {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) [Fintype (Fiber S e o)]
    (ap : Multiset {i : Fin M // i ∈ S.val})
    (V : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (k l U : ℕ)
    (hin : ∀ i ∈ V, ap.count i = k ∨ ap.count i = k + 1)
    (hout : ∀ i ∉ V, ¬ ((ap.count i = k ∨ ap.count i = k + 1) ∧
      (outside i = l ∨ outside i = l + 1))) :
    nativeRectangleEvent S e o ap V outside l (V.powersetCard U) =
      (univ.filter fun y : Fiber S e o =>
        nativeRectangleReadout S e o k l y = rectangleEnvironmentData ap V outside U) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨B, hB, hyB⟩ := mem_biUnion.mp hy
    have hBV := (mem_powersetCard.mp hB).1
    have hBU := (mem_powersetCard.mp hB).2
    have hrow (i : {i : Fin M // i ∈ S.val}) :
        count e y.val i.val 1 = ap.count i ∧
        count e y.val i.val (-1) = rectangleNegativeCounts V B outside l i := by
      have h := (mem_filter.mp hyB).2 i
      simpa only [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm] using h
    have hV : nativeRectangleRows S e o k l y = V := by
      ext i
      simp only [nativeRectangleRows, mem_filter, mem_univ, true_and, (hrow i).1, (hrow i).2]
      by_cases hi : i ∈ V
      · simp only [rectangleNegativeCounts, if_pos hi]
        exact ⟨fun _ => hi, fun _ => ⟨hin i hi, by split_ifs <;> simp⟩⟩
      · simp only [rectangleNegativeCounts, if_neg hi]
        exact ⟨fun h => False.elim (hout i hi h), fun h => False.elim (hi h)⟩
    have hlow : (V.filter fun i => count e y.val i.val (-1) = l) = B := by
      ext i
      simp only [mem_filter, (hrow i).2, rectangleNegativeCounts]
      by_cases hi : i ∈ V
      · by_cases hiB : i ∈ B <;> simp [hi, hiB]
      · have hiB : i ∉ B := fun h => hi (hBV h)
        simp [hi, hiB]
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    apply Prod.ext
    · exact funext fun i => (hrow i).1
    · apply Prod.ext
      · exact hV
      · apply Prod.ext
        · funext i
          change (if i ∈ nativeRectangleRows S e o k l y then none
            else some (count e y.val i.val (-1))) = if i ∈ V then none else some (outside i)
          rw [hV]
          by_cases hi : i ∈ V
          · simp [hi]
          · simp [hi, (hrow i).2, rectangleNegativeCounts]
        · change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val (-1) = l).card = U
          rw [hV, hlow, hBU]
  · intro hy
    have he := (mem_filter.mp hy).2
    have hp : ∀ i : {i : Fin M // i ∈ S.val}, count e y.val i.val 1 = ap.count i :=
      fun i => congrFun (congrArg Prod.fst he) i
    have hV : nativeRectangleRows S e o k l y = V := congrArg (fun x => x.2.1) he
    have ho : ∀ i ∉ V, count e y.val i.val (-1) = outside i := by
      intro i hi
      have h := congrFun (congrArg (fun x => x.2.2.1) he) i
      change (if i ∈ nativeRectangleRows S e o k l y then none
        else some (count e y.val i.val (-1))) = if i ∈ V then none else some (outside i) at h
      simpa only [hV, if_neg hi, Option.some.injEq] using h
    let B := V.filter fun i => count e y.val i.val (-1) = l
    have hB : B ∈ V.powersetCard U := mem_powersetCard.mpr ⟨filter_subset _ _, by
      have hu := congrArg (fun x => x.2.2.2) he
      change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val (-1) = l).card = U at hu
      simpa only [hV] using hu⟩
    apply mem_biUnion.mpr
    refine ⟨B, hB, ?_⟩
    simp only [jointRowHistogramEvent, mem_filter, mem_univ, true_and]
    intro i
    refine ⟨hp i, ?_⟩
    simp only [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm]
    by_cases hi : i ∈ V
    · have hm : count e y.val i.val (-1) = l ∨ count e y.val i.val (-1) = l + 1 :=
        (mem_filter.mp (hV.symm ▸ hi)).2.2
      dsimp only [rectangleNegativeCounts]
      simp only [if_pos hi]
      by_cases hiB : i ∈ B
      · simp only [if_pos hiB]
        exact (mem_filter.mp hiB).2
      · simp only [if_neg hiB]
        exact hm.resolve_left fun h => hiB (mem_filter.mpr ⟨hi, h⟩)
    · simp only [rectangleNegativeCounts, if_neg hi]
      exact ho i hi

/-- The A-cell count is measured on the actual true-support rows. -/
def nativeRectangleACount {M q s : ℕ} (S : Support M q) (e : Experiment)
    (o : Obs M s e) (k l : ℕ) (y : Fiber S e o) : ℕ := by
  classical
  exact (univ.filter fun i : {i : Fin M // i ∈ S.val} =>
    count e y.val i.val 1 = k ∧ count e y.val i.val (-1) = l).card

private theorem native_a_count_intersection {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (ap : Multiset {i : Fin M // i ∈ S.val})
    (V B : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (k l : ℕ)
    (hBV : B ⊆ V)
    (hout : ∀ i ∉ V, ¬ ((ap.count i = k ∨ ap.count i = k + 1) ∧
      (outside i = l ∨ outside i = l + 1)))
    (y : Fiber S e o) (hy : y ∈ jointRowHistogramEvent S e o ap
      (Finsupp.equivFunOnFinite.symm (rectangleNegativeCounts V B outside l)).toMultiset) :
    nativeRectangleACount S e o k l y = (B ∩ V.filter (fun i => ap.count i = k)).card := by
  classical
  have hrow (i : {i : Fin M // i ∈ S.val}) :
      count e y.val i.val 1 = ap.count i ∧
      count e y.val i.val (-1) = rectangleNegativeCounts V B outside l i := by
    have h := (mem_filter.mp hy).2 i
    simpa only [Finsupp.count_toMultiset, Finsupp.coe_equivFunOnFinite_symm] using h
  unfold nativeRectangleACount
  apply congrArg Finset.card
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_inter, (hrow i).1, (hrow i).2]
  by_cases hi : i ∈ V
  · simp only [rectangleNegativeCounts, if_pos hi, hi, true_and]
    by_cases hiB : i ∈ B <;> simp [hiB]
  · simp only [rectangleNegativeCounts, if_neg hi, hi, false_and, and_false]
    exact ⟨fun h => False.elim (hout i hi ⟨Or.inl h.1, Or.inl h.2⟩), False.elim⟩

private theorem native_a_event_eq {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (ap : Multiset {i : Fin M // i ∈ S.val})
    (V : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (k l U t : ℕ)
    (hout : ∀ i ∉ V, ¬ ((ap.count i = k ∨ ap.count i = k + 1) ∧
      (outside i = l ∨ outside i = l + 1))) :
    (nativeRectangleEvent S e o ap V outside l (V.powersetCard U)).filter
        (fun y => nativeRectangleACount S e o k l y = t) =
      nativeRectangleEvent S e o ap V outside l
        (intersectionEvent V (V.filter fun i => ap.count i = k) U t) := by
  classical
  ext y
  constructor
  · intro hy
    have hc := (mem_filter.mp hy).2
    obtain ⟨B, hB, hyB⟩ := mem_biUnion.mp (mem_filter.mp hy).1
    refine mem_biUnion.mpr ⟨B, mem_filter.mpr ⟨hB, ?_⟩, hyB⟩
    exact (native_a_count_intersection S e o ap V B outside k l
      (mem_powersetCard.mp hB).1 hout y hyB).symm.trans hc
  · intro hy
    obtain ⟨B, hB, hyB⟩ := mem_biUnion.mp hy
    have hBc := mem_filter.mp hB
    exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨B, hBc.1, hyB⟩,
      (native_a_count_intersection S e o ap V B outside k l
        (mem_powersetCard.mp hBc.1).1 hout y hyB).trans hBc.2⟩

/-- The exact native A-cell law on the explicit complete rectangle environment
for both the pair and continuous path experiments. -/
theorem native_conditioned_four_cell_law {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (ap : Multiset {i : Fin M // i ∈ S.val})
    (V : Finset {i : Fin M // i ∈ S.val})
    (outside : {i : Fin M // i ∈ S.val} → ℕ) (k l U t : ℕ)
    (hap : ap.card = (signedDepartureBlocks S e o 0).card)
    (hneg : (∑ i ∈ univ \ V, outside i) + U * l + (V.card - U) * (l + 1) =
      (signedDepartureBlocks S e o 1).card)
    (hU : U ≤ V.card) (ht : t ≤ U)
    (hin : ∀ i ∈ V, ap.count i = k ∨ ap.count i = k + 1)
    (hout : ∀ i ∉ V, ¬ ((ap.count i = k ∨ ap.count i = k + 1) ∧
      (outside i = l ∨ outside i = l + 1))) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let Env := univ.filter fun y : Fiber S e o =>
      nativeRectangleReadout S e o k l y = rectangleEnvironmentData ap V outside U
    let R := V.filter fun i => ap.count i = k
    conditionalFiberMass S r e o (Env.filter fun y => nativeRectangleACount S e o k l y = t) /
        conditionalFiberMass S r e o Env =
      ((R.card.choose t : ℝ) * ((V.card - R.card).choose (U - t) : ℝ)) /
        (V.card.choose U : ℝ) ∧
    (∀ A : Set (Fiber S e o), @MeasurableSet (Fiber S e o)
      (nativeRectangleSigma S e o k l) A ↔
        ∃ B, (nativeRectangleReadout S e o k l) ⁻¹' B = A) := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  constructor
  · rw [← native_rectangle_readout_fiber S e o ap V outside k l U hin hout,
      native_a_event_eq S e o ap V outside k l U t hout]
    exact native_rectangle_hypergeometric_law S r e o hq hqm hr hr1 ha ha1 ap V _ outside l U t
      hap hneg hU (filter_subset _ _) ht
  · intro A
    exact ⟨fun ⟨B, _, hB⟩ => ⟨B, hB⟩,
      fun ⟨B, hB⟩ => ⟨B, MeasurableSpace.measurableSet_top, hB⟩⟩

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel

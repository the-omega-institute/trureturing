/- GID: D5/S3/Analytic/Probability/ChenFixedOrderSampling
   generality: I
   mirror-B: D5/B/S3/Analytic/Probability/ChenFixedOrderSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform fixed-size sampling and the stratum inclusion identities for Chen's fixed-order problem. -/

import Mathlib.Probability.UniformOn
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace ChenFixedOrderSampling

open MeasureTheory ProbabilityTheory
open scoped ENNReal

abbrev sampleSize (m : ℕ) : ℕ := (m + 1)^2
abbrev stratumSize (m : ℕ) : ℕ := (sampleSize m)^3
abbrev Population (m : ℕ) := Fin 2 × Fin (stratumSize m)
abbrev Sample (m : ℕ) := {S : Finset (Population m) // S.card = sampleSize m}

def populationValue (m : ℕ) (j : Population m) : ℝ :=
  if j.1 = 0 then 1 else -1

noncomputable def populationMean (m : ℕ) : ℝ :=
  (∑ j : Population m, populationValue m j) / (Fintype.card (Population m) : ℝ)

noncomputable def estimator (m : ℕ) (S : Sample m) : ℝ :=
  Real.sqrt (sampleSize m : ℝ) *
    ((∑ j ∈ S.val, populationValue m j) / (sampleSize m : ℝ) - populationMean m)

def inclusion (m : ℕ) (A : Finset (Population m)) : Set (Sample m) :=
  {S | A ⊆ S.val}

private theorem sampleSize_pos (m : ℕ) : 0 < sampleSize m := by
  positivity

private theorem sampleSize_le_stratumSize (m : ℕ) : sampleSize m ≤ stratumSize m := by
  simpa using (Nat.le_pow (a := sampleSize m) (b := 3) (by decide : 0 < 3))

instance (m : ℕ) : Nonempty (Sample m) := by
  classical
  have h : sampleSize m ≤ (Finset.univ : Finset (Population m)).card := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    have := sampleSize_le_stratumSize m
    omega
  obtain ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr h
  exact ⟨⟨S, (Finset.mem_powersetCard.mp hS).2⟩⟩

theorem populationMean_eq_zero (m : ℕ) : populationMean m = 0 := by
  simp [populationMean, Fintype.sum_prod_type, Fin.sum_univ_two, populationValue]

/-- A draw with replacement is indexed by the same sample size as the unordered sample. -/
abbrev Draw (m : ℕ) := Fin (sampleSize m) → Population m

/-- The conditioning event for sampling without replacement. -/
def distinct (m : ℕ) : Set (Draw m) := {d | Function.Injective d}

private def eraseDistinct (m : ℕ) (d : distinct m) : Sample m :=
  ⟨Finset.univ.image d.val, by
    rw [Finset.card_image_of_injective _ d.property, Finset.card_univ, Fintype.card_fin]⟩

/-- Erase order on distinct draws. The value off the conditioning event is immaterial. -/
noncomputable def eraseOrder (m : ℕ) (d : Draw m) : Sample m := by
  classical
  exact if hd : d ∈ distinct m then eraseDistinct m ⟨d, hd⟩ else Classical.choice inferInstance

theorem eraseOrder_val (m : ℕ) (d : Draw m) (hd : d ∈ distinct m) :
    (eraseOrder m d).val = Finset.univ.image d := by
  simp [eraseOrder, dite_eq_left hd, eraseDistinct]

private noncomputable def drawFiberEquiv (m : ℕ) (S : Sample m) :
    ↥(distinct m ∩ (eraseOrder m) ⁻¹' {S}) ≃ (Fin (sampleSize m) ≃ ↥S.val) := by
  classical
  have image_eq (d : ↥(distinct m ∩ (eraseOrder m) ⁻¹' {S})) :
      Finset.univ.image d.val = S.val :=
    (eraseOrder_val m d.val d.property.1).symm.trans (congrArg Subtype.val d.property.2)
  let order (d : ↥(distinct m ∩ (eraseOrder m) ⁻¹' {S})) :
      Fin (sampleSize m) ≃ ↥S.val :=
    Equiv.ofBijective (fun i => ⟨d.val i, by rw [← image_eq d]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
      ⟨fun _ _ hij => d.property.1 (congrArg Subtype.val hij), by
        intro x
        have hx : x.val ∈ Finset.univ.image d.val := by rw [image_eq d]; exact x.property
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
        exact ⟨i, Subtype.ext hi⟩⟩
  let draw (e : Fin (sampleSize m) ≃ ↥S.val) :
      ↥(distinct m ∩ (eraseOrder m) ⁻¹' {S}) := by
    let d : Draw m := fun i => (e i).val
    have hd : d ∈ distinct m := fun _ _ h => e.injective (Subtype.ext h)
    refine ⟨d, hd, Subtype.ext ?_⟩
    rw [eraseOrder_val m d hd]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (e i).property,
      fun hx => ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩⟩
  exact ⟨order, draw, fun _ => Subtype.ext rfl, fun _ => Equiv.ext fun _ => Subtype.ext rfl⟩

private theorem card_drawFiber (m : ℕ) (S : Sample m) :
    (distinct m ∩ (eraseOrder m) ⁻¹' {S}).ncard = (sampleSize m).factorial := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, Fintype.card_congr (drawFiberEquiv m S),
    Fintype.card_equiv (S.val.equivFinOfCardEq S.property).symm, Fintype.card_fin]

private theorem uniformOn_apply_ncard {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (D E : Set α) :
    uniformOn D E = ((D ∩ E).ncard : ℝ≥0∞) / D.ncard := by
  classical
  have h : (D ∩ E).toFinset = D.toFinset ∩ E.toFinset := by ext x; simp
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card' D, h]
  simpa only [Set.coe_toFinset] using (uniformOn_apply_finset (s := D.toFinset) (t := E.toFinset))

/-- Conditioning the ordered uniform draw on distinctness and erasing order gives the uniform
law on the fixed-size subsets. -/
theorem map_eraseOrder_cond_uniform (m : ℕ) :
    (ProbabilityTheory.cond (uniformOn (Set.univ : Set (Draw m))) (distinct m)).map
      (eraseOrder m) = uniformOn (Set.univ : Set (Sample m)) := by
  classical
  have hD : MeasurableSet (distinct m) := (distinct m).toFinite.measurableSet
  have hDne : (distinct m).Nonempty := by
    let S : Sample m := Classical.choice inferInstance
    let e : Fin (sampleSize m) ≃ ↥S.val := (S.val.equivFinOfCardEq S.property).symm
    exact ⟨(drawFiberEquiv m S).symm e |>.val, ((drawFiberEquiv m S).symm e).property.1⟩
  have hc : ProbabilityTheory.cond (uniformOn (Set.univ : Set (Draw m))) (distinct m) =
      uniformOn (distinct m) := by
    unfold uniformOn
    rw [cond_cond_eq_cond_inter MeasurableSet.univ hD, Set.univ_inter]
  rw [hc]
  let μ := (uniformOn (distinct m)).map (eraseOrder m)
  have he : Measurable (eraseOrder m) := measurable_of_finite _
  let : IsProbabilityMeasure (uniformOn (distinct m)) :=
    isProbabilityMeasure_uniformOn (distinct m).toFinite hDne
  let : IsProbabilityMeasure μ := ⟨by
    change ((uniformOn (distinct m)).map (eraseOrder m)) Set.univ = 1
    rw [Measure.map_apply he MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  have hmass (S : Sample m) :
      μ {S} = ((sampleSize m).factorial : ℝ≥0∞) / (distinct m).ncard := by
    change ((uniformOn (distinct m)).map (eraseOrder m)) {S} = _
    rw [Measure.map_apply he (measurableSet_singleton S), uniformOn_apply_ncard, card_drawFiber]
  have htotal : (((sampleSize m).factorial : ℝ≥0∞) / (distinct m).ncard) *
      (Fintype.card (Sample m) : ℝ≥0∞) = 1 := by
    calc
      _ = ∑ _ : Sample m, (((sampleSize m).factorial : ℝ≥0∞) / (distinct m).ncard) := by
        simp [nsmul_eq_mul, mul_comm]
      _ = ∑ S : Sample m, μ {S} := by simp_rw [hmass]
      _ = 1 := by simp
  change μ = _
  apply Measure.ext_of_singleton
  intro S
  rw [hmass, ENNReal.eq_inv_of_mul_eq_one_left htotal, uniformOn_univ]
  simp

open Finset

private theorem card_split_cell {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] (A : Finset α) (n k l : ℕ) (hkl : k + l = n) :
    ((univ : Finset {S : Finset α // S.card = n}).filter
        (fun S => (S.val.filter p).card = k ∧ A ⊆ S.val)).card =
      (((univ.filter p).powersetCard k).filter (A.filter p ⊆ ·)).card *
        (((univ.filter fun x => ¬p x).powersetCard l).filter
          ((A.filter fun x => ¬p x) ⊆ ·)).card := by
  classical
  rw [← card_product]
  refine card_bij (fun S _ => (S.val.filter p, S.val.filter fun x => ¬p x)) ?_ ?_ ?_
  · intro S hS
    obtain ⟨h₁, hA⟩ := (mem_filter.mp hS).2
    have h₂ : (S.val.filter fun x => ¬p x).card = l := by
      have h := card_filter_add_card_filter_not (s := S.val) p
      have hs := S.property
      omega
    simp only [mem_product, mem_filter, mem_powersetCard]
    exact ⟨⟨⟨filter_subset_filter _ (subset_univ _), h₁⟩, filter_subset_filter _ hA⟩,
      ⟨⟨filter_subset_filter _ (subset_univ _), h₂⟩, filter_subset_filter _ hA⟩⟩
  · intro S _ T _ h
    apply Subtype.ext
    rw [← filter_union_filter_not_eq p S.val, ← filter_union_filter_not_eq p T.val]
    exact congrArg₂ (· ∪ ·) (congrArg Prod.fst h) (congrArg Prod.snd h)
  · intro T hT
    simp only [mem_product, mem_filter, mem_powersetCard] at hT
    obtain ⟨⟨⟨ht₁, hk⟩, ha₁⟩, ⟨⟨ht₂, hl⟩, ha₂⟩⟩ := hT
    have hpos x (hx : x ∈ T.1) : p x := (mem_filter.mp (ht₁ hx)).2
    have hneg x (hx : x ∈ T.2) : ¬p x := (mem_filter.mp (ht₂ hx)).2
    have hdis : Disjoint T.1 T.2 := disjoint_left.mpr fun x hx hy => hneg x hy (hpos x hx)
    have hcard : (T.1 ∪ T.2).card = n := by rw [card_union_of_disjoint hdis, hk, hl, hkl]
    have hfp : (T.1 ∪ T.2).filter p = T.1 := by
      rw [filter_union, filter_true_of_mem hpos, filter_false_of_mem hneg, union_empty]
    have hfn : (T.1 ∪ T.2).filter (fun x => ¬p x) = T.2 := by
      rw [filter_union, filter_false_of_mem (fun x hx h => h (hpos x hx)),
        filter_true_of_mem hneg, empty_union]
    refine ⟨⟨T.1 ∪ T.2, hcard⟩, mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩, ?_⟩
    · simpa only [hfp] using hk
    · rw [← filter_union_filter_not_eq p A]
      exact union_subset_union ha₁ ha₂
    · exact Prod.ext hfp hfn

private theorem card_supersets_mul_choose {α : Type*} [DecidableEq α]
    (U A : Finset α) (hA : A ⊆ U) (k : ℕ) :
    ((U.powersetCard k).filter (A ⊆ ·)).card * U.card.choose A.card =
      U.card.choose k * k.choose A.card := by
  by_cases h : A.card ≤ k
  · rw [card_filter_powersetCard_subset _ _ _ hA h, Nat.choose_mul h, mul_comm]
  · have he : (U.powersetCard k).filter (A ⊆ ·) = ∅ :=
      filter_eq_empty_iff.mpr fun S hS hAS => h ((card_le_card hAS).trans_eq (mem_powersetCard.mp hS).2)
    simp [he, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

private def positiveLabel {m : ℕ} (j : Population m) : Prop := j.1 = 0
private instance {m : ℕ} : DecidablePred (positiveLabel (m := m)) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

private def positiveCount {m : ℕ} (S : Finset (Population m)) : ℕ :=
  (S.filter positiveLabel).card

private def negativeCount {m : ℕ} (S : Finset (Population m)) : ℕ :=
  (S.filter fun j => ¬positiveLabel j).card

private theorem counts_add {m : ℕ} (S : Finset (Population m)) :
    positiveCount S + negativeCount S = S.card :=
  card_filter_add_card_filter_not (s := S) positiveLabel

private theorem positiveCount_univ (m : ℕ) :
    positiveCount (univ : Finset (Population m)) = stratumSize m := by
  have h : (univ : Finset (Fin 2)).filter (· = 0) = {0} := by ext i; simp
  rw [positiveCount, ← univ_product_univ]
  change ((univ ×ˢ univ).filter fun j : Population m => j.1 = 0).card = _
  rw [filter_product_left (· = (0 : Fin 2)), h, card_product]
  simp

private theorem negativeCount_univ (m : ℕ) :
    negativeCount (univ : Finset (Population m)) = stratumSize m := by
  have h := counts_add (univ : Finset (Population m))
  rw [positiveCount_univ] at h
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin] at h
  omega

private theorem estimator_eq_count (m : ℕ) (S : Sample m) :
    estimator m S = (2 * (positiveCount S.val : ℝ) - (sampleSize m : ℝ)) /
      Real.sqrt (sampleSize m : ℝ) := by
  have hsum : ∑ j ∈ S.val, populationValue m j =
      (positiveCount S.val : ℝ) - (negativeCount S.val : ℝ) := by
    change (∑ j ∈ S.val, if positiveLabel j then (1 : ℝ) else -1) = _
    simp [sum_ite, positiveCount, negativeCount, sub_eq_add_neg]
  have hc : (positiveCount S.val : ℝ) + (negativeCount S.val : ℝ) = sampleSize m := by
    exact_mod_cast (counts_add S.val).trans S.property
  have hn : 0 < (sampleSize m : ℝ) := by exact_mod_cast sampleSize_pos m
  have hs := Real.sq_sqrt hn.le
  rw [estimator, populationMean_eq_zero, sub_zero, hsum]
  field_simp
  nlinarith

private theorem cell_count_mul_choose (m : ℕ) (A : Finset (Population m))
    (k : ℕ) (hk : k ≤ sampleSize m) :
    ((univ : Finset (Sample m)).filter
        (fun S => positiveCount S.val = k ∧ A ⊆ S.val)).card *
      ((stratumSize m).choose (positiveCount A) * (stratumSize m).choose (negativeCount A)) =
    ((univ : Finset (Sample m)).filter (fun S => positiveCount S.val = k)).card *
      (k.choose (positiveCount A) * (sampleSize m - k).choose (negativeCount A)) := by
  let U := (univ : Finset (Population m)).filter positiveLabel
  let V := (univ : Finset (Population m)).filter fun j => ¬positiveLabel j
  let a := A.filter positiveLabel
  let b := A.filter fun j => ¬positiveLabel j
  let l := sampleSize m - k
  have hkl : k + l = sampleSize m := Nat.add_sub_of_le hk
  have hA := card_split_cell positiveLabel A (sampleSize m) k l hkl
  have h0 := card_split_cell (positiveLabel (m := m)) ∅ (sampleSize m) k l hkl
  simp only [filter_empty, empty_subset, and_true, filter_true, card_powersetCard] at h0
  change ((univ : Finset (Sample m)).filter
      (fun S => positiveCount S.val = k ∧ A ⊆ S.val)).card =
    ((U.powersetCard k).filter (a ⊆ ·)).card *
      ((V.powersetCard l).filter (b ⊆ ·)).card at hA
  change ((univ : Finset (Sample m)).filter (fun S => positiveCount S.val = k)).card =
    U.card.choose k * V.card.choose l at h0
  have hU : U.card = stratumSize m := positiveCount_univ m
  have hV : V.card = stratumSize m := negativeCount_univ m
  suffices
      ((univ : Finset (Sample m)).filter
          (fun S => positiveCount S.val = k ∧ A ⊆ S.val)).card *
        (U.card.choose a.card * V.card.choose b.card) =
      ((univ : Finset (Sample m)).filter (fun S => positiveCount S.val = k)).card *
        (k.choose a.card * l.choose b.card) by
      simpa only [hU, hV, a, b, l, positiveCount, negativeCount] using this
  rw [hA, h0]
  calc
    _ = (((U.powersetCard k).filter (a ⊆ ·)).card * U.card.choose a.card) *
        (((V.powersetCard l).filter (b ⊆ ·)).card * V.card.choose b.card) := by ac_rfl
    _ = (U.card.choose k * k.choose a.card) * (V.card.choose l * l.choose b.card) := by
      rw [card_supersets_mul_choose U a (filter_subset_filter _ (subset_univ _)),
        card_supersets_mul_choose V b (filter_subset_filter _ (subset_univ _))]
    _ = _ := by ac_rfl

open Polynomial

private noncomputable def stratumCountPolynomial (m : ℕ) (sign : ℝ) : ℝ[X] :=
  C (Real.sqrt (sampleSize m : ℝ) * sign / 2) * X + C ((sampleSize m : ℝ) / 2)

private noncomputable def inclusionFactor (m : ℕ) (sign : ℝ) (a : ℕ) : ℝ[X] :=
  C (((a.factorial : ℝ) * ((stratumSize m).choose a : ℝ))⁻¹) *
    (descPochhammer ℝ a).comp (stratumCountPolynomial m sign)

private theorem inclusionFactor_natDegree_le (m : ℕ) (sign : ℝ) (a : ℕ) :
    (inclusionFactor m sign a).natDegree ≤ a := by
  have h : (stratumCountPolynomial m sign).natDegree ≤ 1 := by
    simpa [stratumCountPolynomial] using (natDegree_C_mul_le
      (Real.sqrt (sampleSize m : ℝ) * sign / 2) X)
  unfold inclusionFactor
  refine (natDegree_C_mul_le _ _).trans (natDegree_comp_le.trans ?_)
  simpa [descPochhammer_natDegree] using Nat.mul_le_mul_left a h

private theorem inclusionFactor_eval (m : ℕ) (sign : ℝ) (k a : ℕ) (x : ℝ)
    (hx : (stratumCountPolynomial m sign).eval x = (k : ℝ)) :
    (inclusionFactor m sign a).eval x = (k.choose a : ℝ) / ((stratumSize m).choose a : ℝ) := by
  rw [inclusionFactor, eval_C_mul, eval_comp, hx, Nat.cast_choose_eq_descPochhammer_div ℝ k a]
  simp only [mul_inv, div_eq_mul_inv]
  ring

private noncomputable def estimatorAtCount (m k : ℕ) : ℝ :=
  (2 * (k : ℝ) - (sampleSize m : ℝ)) / Real.sqrt (sampleSize m : ℝ)

private theorem polynomial_eval_at_cell (m : ℕ) (A : Finset (Population m))
    (k : ℕ) (hk : k ≤ sampleSize m) :
    (inclusionFactor m 1 (positiveCount A) * inclusionFactor m (-1) (negativeCount A)).eval
          (estimatorAtCount m k) =
      ((k.choose (positiveCount A) : ℕ) : ℝ) / ((stratumSize m).choose (positiveCount A) : ℝ) *
      (((sampleSize m - k).choose (negativeCount A) : ℕ) : ℝ) /
        ((stratumSize m).choose (negativeCount A) : ℝ) := by
  have hs : Real.sqrt (sampleSize m : ℝ) ≠ 0 := by
    apply Real.sqrt_ne_zero'.mpr
    exact_mod_cast sampleSize_pos m
  have hpos : (stratumCountPolynomial m 1).eval (estimatorAtCount m k) = (k : ℝ) := by
    simp [stratumCountPolynomial, estimatorAtCount]
    field_simp
    ring
  have hneg : (stratumCountPolynomial m (-1)).eval (estimatorAtCount m k) =
      (↑(sampleSize m - k) : ℝ) := by
    rw [Nat.cast_sub hk]
    simp [stratumCountPolynomial, estimatorAtCount]
    field_simp
    ring
  rw [eval_mul, inclusionFactor_eval _ _ _ _ _ hpos, inclusionFactor_eval _ _ _ _ _ hneg]
  ring

private noncomputable def inclusionPolynomial (m : ℕ) (A : Finset (Population m)) : ℝ[X] :=
  inclusionFactor m 1 (positiveCount A) * inclusionFactor m (-1) (negativeCount A)

private theorem card_inclusion_cell (m : ℕ) (A : Finset (Population m))
    (k : ℕ) (hk : k ≤ sampleSize m) :
    (((univ : Finset (Sample m)).filter (fun S => positiveCount S.val = k ∧ A ⊆ S.val)).card : ℝ) =
      (((univ : Finset (Sample m)).filter (fun S => positiveCount S.val = k)).card : ℝ) *
        (inclusionPolynomial m A).eval (estimatorAtCount m k) := by
  have ha : positiveCount A ≤ stratumSize m := by
    rw [← positiveCount_univ m]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  have hb : negativeCount A ≤ stratumSize m := by
    rw [← negativeCount_univ m]
    exact card_le_card (filter_subset_filter _ (subset_univ _))
  have ha' : ((stratumSize m).choose (positiveCount A) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos ha).ne'
  have hb' : ((stratumSize m).choose (negativeCount A) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hb).ne'
  have h := congrArg (fun n : ℕ => (n : ℝ)) (cell_count_mul_choose m A k hk)
  push_cast at h
  rw [inclusionPolynomial, polynomial_eval_at_cell m A k hk]
  field_simp
  linear_combination h

private theorem sum_inclusion_eq_polynomial (m : ℕ) (A : Finset (Population m)) (f : ℝ → ℝ) :
    (∑ S ∈ (univ : Finset (Sample m)).filter (fun S => A ⊆ S.val), f (estimator m S)) =
      ∑ S : Sample m, (inclusionPolynomial m A).eval (estimator m S) * f (estimator m S) := by
  have group (T : Finset (Sample m)) (g : Sample m → ℝ) :
      (∑ S ∈ T, g S) = ∑ k ∈ range (sampleSize m + 1),
        ∑ S ∈ T.filter (fun S => positiveCount S.val = k), g S := by
    symm
    apply sum_fiberwise_of_maps_to
    intro S _
    apply mem_range.mpr
    exact Nat.lt_succ_of_le ((card_le_card (filter_subset _ _)).trans_eq S.property)
  rw [group (univ.filter (fun S : Sample m => A ⊆ S.val)), group univ]
  refine sum_congr rfl fun k hk => ?_
  have hk' := Nat.le_of_lt_succ (mem_range.mp hk)
  have hest (S : Sample m) (hS : positiveCount S.val = k) :
      estimator m S = estimatorAtCount m k := by
    rw [estimator_eq_count, hS, estimatorAtCount]
  have hfilter :
      (univ.filter (fun S : Sample m => A ⊆ S.val)).filter (fun S => positiveCount S.val = k) =
        univ.filter (fun S : Sample m => positiveCount S.val = k ∧ A ⊆ S.val) := by
    simp only [filter_filter, and_comm]
  rw [hfilter]
  calc
    _ = ∑ _S ∈ univ.filter (fun S : Sample m => positiveCount S.val = k ∧ A ⊆ S.val),
        f (estimatorAtCount m k) := by
      exact sum_congr rfl fun S hS => congrArg f (hest S (mem_filter.mp hS).2.1)
    _ = ∑ _S ∈ univ.filter (fun S : Sample m => positiveCount S.val = k),
        (inclusionPolynomial m A).eval (estimatorAtCount m k) * f (estimatorAtCount m k) := by
      simp only [sum_const, nsmul_eq_mul, card_inclusion_cell m A k hk', mul_assoc]
    _ = _ := by
      refine sum_congr rfl fun S hS => ?_
      rw [hest S (mem_filter.mp hS).2]

/-- Under uniform fixed-size sampling, a prescribed inclusion event acts on any function
of the common estimator as multiplication by a polynomial of degree at most the order. -/
theorem exists_inclusionPolynomial (m : ℕ) (A : Finset (Population m)) :
    ∃ p : ℝ[X], p.natDegree ≤ A.card ∧ ∀ f : ℝ → ℝ,
      (∫ S in inclusion m A, f (estimator m S) ∂(uniformOn (Set.univ : Set (Sample m)))) =
        ∫ S : Sample m, p.eval (estimator m S) * f (estimator m S)
          ∂(uniformOn (Set.univ : Set (Sample m))) := by
  refine ⟨inclusionPolynomial m A, ?_, ?_⟩
  · exact natDegree_mul_le.trans ((add_le_add (inclusionFactor_natDegree_le _ _ _)
      (inclusionFactor_natDegree_le _ _ _)).trans_eq (counts_add A))
  · intro f
    have hsum :
        (∑ S : Sample m, (inclusion m A).indicator (f ∘ estimator m) S) =
          ∑ S : Sample m, (inclusionPolynomial m A).eval (estimator m S) * f (estimator m S) := by
      rw [← sum_inclusion_eq_polynomial m A f, sum_filter]
      apply sum_congr rfl
      intro S _
      by_cases h : A ⊆ S.val
      · rw [Set.indicator_of_mem (show S ∈ inclusion m A from h), ite_eq_left h]
        rfl
      · rw [Set.indicator_of_notMem (show S ∉ inclusion m A from h), ite_eq_right h]
    rw [← integral_indicator (inclusion m A).toFinite.measurableSet]
    simp only [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ, integral_smul_measure,
      integral_count]
    exact congrArg (fun z : ℝ => ((Measure.count (Set.univ : Set (Sample m)))⁻¹).toReal • z) hsum

end ChenFixedOrderSampling

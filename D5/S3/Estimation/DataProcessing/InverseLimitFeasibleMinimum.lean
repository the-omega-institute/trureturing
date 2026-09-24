/- GID: D5/S3/Estimation/DataProcessing/InverseLimitFeasibleMinimum
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InverseLimitFeasibleMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common radius attains the supremum of finite feasible-law minimum distances. -/

import D5.S3.Estimation.DataProcessing.InverseLimitFeasibleLaws
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.InverseLimitFeasibleMinimum

universe u
open Set Function MeasureTheory CategoryTheory
open scoped ENNReal NNReal
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
open D5.S3.Estimation.DataProcessing.OneCutZeroExcess
open D5.S3.Estimation.DataProcessing.InverseLimitZeroExcess
open D5.S3.Estimation.DataProcessing.InverseLimitFeasibleLaws
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open private measurable_total_variation_map_le from
  D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

set_option maxHeartbeats 1000000 in
-- Two probability extensions and the finite compact faces require additional elaboration steps.
/-- Every fixed comparison probability has a nearest feasible completed law.
All finite minima are attained and increase to its distance. The comparison
law has no support or marginal restrictions. -/
theorem exists_feasible_minimum_eq_iSup {B : ℕ → Type u}
    [∀ l, Finite (B l)] [∀ l, Nonempty (B l)]
    [∀ l, TopologicalSpace (B l)] [∀ l, DiscreteTopology (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, BorelSpace (B l)]
    (q : (l : ℕ) → B (l + 1) → B l) (hq : ∀ l, Surjective (q l))
    (g : (l : ℕ) → B l ≃ B l)
    (hg : ∀ l x, q l (g (l + 1) x) = g l (q l x)) (n : ℕ)
    (S : (l : ℕ) → Set (Fin (n + 1) → B l))
    (hS : ∀ l y, y ∈ S (l + 1) → (fun j => q l (y j)) ∈ S l)
    (μ₀ : (l : ℕ) → ProbabilityMeasure (B l))
    (hμ₀ : ∀ l, (μ₀ (l + 1) : Measure (B (l + 1))).map (q l) =
      (μ₀ l : Measure (B l)))
    (P : ProbabilityMeasure (Fin (n + 1) → Thread B q))
    (hne : ∀ l, ∃ Q : ProbabilityMeasure (Fin (n + 1) → B l),
      Feasible (g l) (S l) (μ₀ l : Measure (B l)) (Q : Measure (Fin (n + 1) → B l))) :
    ∃ μ : ProbabilityMeasure (Thread B q),
      (∀ l, (μ : Measure (Thread B q)).map (fun x => x.val l) = (μ₀ l : Measure (B l))) ∧
    ∃ d : ℕ → ℝ≥0∞,
      (∀ l, ∃ Q : ProbabilityMeasure (Fin (n + 1) → B l),
        Feasible (g l) (S l) (μ₀ l : Measure (B l)) (Q : Measure (Fin (n + 1) → B l)) ∧
        measurableTotalVariation
          ((P : Measure (Fin (n + 1) → Thread B q)).map (levelProjection q (n + 1) l))
          (Q : Measure (Fin (n + 1) → B l)) = d l ∧
        ∀ R : ProbabilityMeasure (Fin (n + 1) → B l),
          Feasible (g l) (S l) (μ₀ l : Measure (B l)) (R : Measure (Fin (n + 1) → B l)) →
          d l ≤ measurableTotalVariation
            ((P : Measure (Fin (n + 1) → Thread B q)).map (levelProjection q (n + 1) l))
            (R : Measure (Fin (n + 1) → B l))) ∧
      Monotone d ∧ (∀ l, d l ≤ 1) ∧
      ∃ Q : ProbabilityMeasure (Fin (n + 1) → Thread B q),
        Feasible (threadEquiv q g hg) (⋂ l, levelProjection q (n + 1) l ⁻¹' S l)
          (μ : Measure (Thread B q)) (Q : Measure (Fin (n + 1) → Thread B q)) ∧
        measurableTotalVariation (P : Measure (Fin (n + 1) → Thread B q))
          (Q : Measure (Fin (n + 1) → Thread B q)) = ⨆ l, d l ∧
        ∀ R : ProbabilityMeasure (Fin (n + 1) → Thread B q),
          Feasible (threadEquiv q g hg) (⋂ l, levelProjection q (n + 1) l ⁻¹' S l)
            (μ : Measure (Thread B q)) (R : Measure (Fin (n + 1) → Thread B q)) →
          measurableTotalVariation (P : Measure (Fin (n + 1) → Thread B q))
            (Q : Measure (Fin (n + 1) → Thread B q)) ≤
            measurableTotalVariation (P : Measure (Fin (n + 1) → Thread B q))
              (R : Measure (Fin (n + 1) → Thread B q)) := by
  classical
  let c (l : ℕ) : B l → Fin 1 → B l := fun x _ => x
  have hc (l : ℕ) : Measurable (c l) := measurable_pi_lambda _ fun _ => measurable_id
  let U (l : ℕ) : ProbabilityMeasure (Fin 1 → B l) := (μ₀ l).map (hc l).aemeasurable
  have hU (l : ℕ) : (U (l + 1) : Measure (Fin 1 → B (l + 1))).map
      (fun y j => q l (y j)) = (U l : Measure (Fin 1 → B l)) := by
    change ((μ₀ (l + 1) : Measure (B (l + 1))).map (c (l + 1))).map
      (fun y j => q l (y j)) = (μ₀ l : Measure (B l)).map (c l)
    rw [Measure.map_map (measurable_of_countable _) (hc (l + 1)), ← hμ₀ l,
      Measure.map_map (hc l) (measurable_of_countable (q l))]
    rfl
  obtain ⟨ν, hν, _⟩ := exists_unique_probability_extension q hq 1 U hU
  let μ : ProbabilityMeasure (Thread B q) := ν.map (measurable_pi_apply 0).aemeasurable
  have hμ (l : ℕ) : (μ : Measure (Thread B q)).map (fun x => x.val l) =
      (μ₀ l : Measure (B l)) := by
    have hp : Measurable (fun x : Thread B q => x.val l) :=
      (measurable_pi_apply l).comp measurable_subtype_coe
    have hπ : Measurable (levelProjection q 1 l) :=
      measurable_pi_lambda _ fun j => hp.comp (measurable_pi_apply j)
    change ((ν : Measure (Fin 1 → Thread B q)).map (fun y => y 0)).map
      (fun x => x.val l) = _
    rw [Measure.map_map hp (measurable_pi_apply 0)]
    have hcomp : (fun x : Thread B q => x.val l) ∘ (fun y : Fin 1 → Thread B q => y 0) =
        (fun y : Fin 1 → B l => y 0) ∘ levelProjection q 1 l := rfl
    rw [hcomp, ← Measure.map_map (measurable_pi_apply 0) hπ, hν l]
    change ((μ₀ l : Measure (B l)).map (c l)).map (fun y => y 0) = _
    rw [Measure.map_map (measurable_pi_apply 0) (hc l)]
    exact Measure.map_id
  clear_value μ
  refine ⟨μ, hμ, ?_⟩
  let A (l : ℕ) := Fin (n + 1) → B l
  let π := levelProjection q (n + 1)
  let b (l : ℕ) : A (l + 1) → A l := fun y j => q l (y j)
  have hπ (l : ℕ) : Measurable (π l) :=
    measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  have hp (l : ℕ) : Measurable (fun x : Thread B q => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hb (l : ℕ) : Measurable (b l) := measurable_of_countable _
  let μL (l : ℕ) := μ.map (hp l).aemeasurable
  let PL L := P.map (hπ L).aemeasurable
  let F (l : ℕ) : Set (ProbabilityMeasure (A l)) :=
    {Q | Feasible (g l) (S l) (μL l : Measure (B l)) (Q : Measure _)}
  let f (l : ℕ) (Q : ProbabilityMeasure (A l)) :=
    measurableTotalVariation (PL l : Measure (A l)) (Q : Measure (A l))
  let p (l : ℕ) (Q : ProbabilityMeasure (A (l + 1))) := Q.map (hb l).aemeasurable
  have hmass {C : Type u} [Finite C] [TopologicalSpace C] [DiscreteTopology C]
      [MeasurableSpace C] [BorelSpace C] (E : Set C) :
      Continuous (fun Q : ProbabilityMeasure C => (Q : Measure C) E) := by
    let v : ContinuousMap C ℝ≥0 := ⟨E.indicator (fun _ => 1), continuous_of_discreteTopology⟩
    have hv := ProbabilityMeasure.continuous_lintegral_continuousMap v
    simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_indicator, ENNReal.coe_one,
      lintegral_indicator_const (Set.toFinite E).measurableSet, one_mul] using hv
  have hf (l : ℕ) : Continuous (f l) := by
    let : Fintype {E : Set (A l) // MeasurableSet E} := Fintype.ofFinite _
    unfold f measurableTotalVariation
    simpa only [Finset.sup_univ_eq_iSup, Function.comp_def] using
      (Continuous.finset_sup_apply (s := Finset.univ)
        fun (E : {E : Set (A l) // MeasurableSet E}) _ =>
        ((ENNReal.continuous_sub_left (measure_ne_top (PL l : Measure (A l)) E.val)).comp
          (hmass E.val)).max
          ((ENNReal.continuous_sub_right ((PL l : Measure (A l)) E.val)).comp (hmass E.val)))
  have hFc (l : ℕ) : IsClosed (F l) := by
    have hmc (j : Fin (n + 1)) : IsClosed {Q : ProbabilityMeasure (A l) |
        (Q : Measure (A l)).map (fun y => y j) = (μL l : Measure (B l))} := by
      have hc : IsClosed {Q : ProbabilityMeasure (A l) |
          Q.map (measurable_pi_apply j).aemeasurable = μL l} :=
        isClosed_eq (ProbabilityMeasure.continuous_map (continuous_apply j)) continuous_const
      convert hc using 1
      ext Q
      exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
    let v : ContinuousMap (A l) ℝ≥0 := ⟨fun y => (cycleExcess (g l) y : ℝ≥0),
      continuous_of_discreteTopology⟩
    have hz : Continuous (fun Q : ProbabilityMeasure (A l) =>
        ∫⁻ y, (cycleExcess (g l) y : ℝ≥0∞) ∂(Q : Measure (A l))) := by
      simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_natCast] using
        ProbabilityMeasure.continuous_lintegral_continuousMap v
    change IsClosed ({Q : ProbabilityMeasure (A l) | (Q : Measure _) (S l) = 1} ∩
      ({Q | ∀ j, (Q : Measure (A l)).map (fun y => y j) = (μL l : Measure (B l))} ∩
        {Q | (∫⁻ y, (cycleExcess (g l) y : ℝ≥0∞) ∂(Q : Measure (A l))) = 0}))
    apply (isClosed_eq (hmass (S l)) continuous_const).inter
    apply IsClosed.inter _ (isClosed_eq hz continuous_const)
    simpa only [Set.ofPred_forall] using isClosed_iInter hmc
  have hML (l : ℕ) : (μL l : Measure (B l)) = (μ₀ l : Measure (B l)) := hμ l
  have hFn (l : ℕ) : (F l).Nonempty := by
    change ∃ Q : ProbabilityMeasure (A l),
      Feasible (g l) (S l) (μL l : Measure (B l)) (Q : Measure (A l))
    rw [hML l]
    exact hne l
  have hpres (l : ℕ) {Q : ProbabilityMeasure (A (l + 1))} (hQ : Q ∈ F (l + 1)) :
      p l Q ∈ F l := by
    have hμ : (μL (l + 1) : Measure (B (l + 1))).map (q l) = (μL l : Measure (B l)) := by
      change ((μ : Measure (Thread B q)).map (fun x => x.val (l + 1))).map (q l) = _
      rw [Measure.map_map (measurable_of_countable _) (hp (l + 1))]
      congr 1
      funext x
      exact x.property l
    have hinv (x : B (l + 1)) : q l ((g (l + 1)).symm x) = (g l).symm (q l x) := by
      apply (g l).injective
      rw [← hg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hz (y : A (l + 1)) (hy : cycleExcess (g (l + 1)) y = 0) :
        cycleExcess (g l) (b l y) = 0 := by
      have h := failure_count_equality_iff_one_cut (g (l + 1)) y
      obtain ⟨k, hk⟩ := h.2.mp (le_antisymm (Nat.sub_eq_zero_iff_le.mp hy) h.1)
      have he : b l y ∈ oneCutSet (g l) := by
        refine ⟨k, funext fun j => ?_⟩
        have hj := congrArg (q l) (congrFun hk j)
        simpa only [b, cutTuple, apply_ite, hinv] using hj
      exact Nat.sub_eq_zero_iff_le.mpr
        (((failure_count_equality_iff_one_cut (g l) (b l y)).2.mpr he).le)
    refine ⟨?_, ?_, ?_⟩
    · change ((Q : Measure _).map (b l)) (S l) = 1
      rw [Measure.map_apply (hb l) (Set.toFinite _).measurableSet]
      exact le_antisymm prob_le_one (by rw [← hQ.1]; exact measure_mono (hS l))
    · intro j
      change ((Q : Measure _).map (b l)).map (fun y => y j) = (μL l : Measure (B l))
      rw [Measure.map_map (measurable_pi_apply j) (hb l), ← hμ, ← hQ.2.1 j,
        Measure.map_map (measurable_of_countable (q l))
          (measurable_pi_apply (X := fun _ : Fin (n + 1) => B (l + 1)) j)]
      rfl
    · change (∫⁻ y, (cycleExcess (g l) y : ℝ≥0∞) ∂(Q : Measure _).map (b l)) = 0
      rw [lintegral_eq_zero_iff (measurable_of_countable _)]
      have hh := (lintegral_eq_zero_iff (measurable_of_countable _)).mp hQ.2.2
      simp only [Filter.EventuallyEq, Pi.zero_apply]
      rw [ae_map_iff (hb l).aemeasurable (Set.toFinite _).measurableSet]
      filter_upwards [hh] with y hy
      change (cycleExcess (g (l + 1)) y : ℝ≥0∞) = 0 at hy
      exact_mod_cast hz y (Nat.cast_eq_zero.mp hy)
  have hcontract (l : ℕ) (Q : ProbabilityMeasure (A (l + 1))) : f l (p l Q) ≤ f (l + 1) Q := by
    have hP : (PL (l + 1) : Measure (A (l + 1))).map (b l) = (PL l : Measure (A l)) := by
      change ((P : Measure (Fin (n + 1) → Thread B q)).map (π (l + 1))).map (b l) = _
      rw [Measure.map_map (hb l) (hπ (l + 1))]
      congr 1
      funext y j
      exact (y j).property l
    change measurableTotalVariation (PL l : Measure (A l)) ((Q : Measure _).map (b l)) ≤ _
    rw [← hP]
    exact measurable_total_variation_map_le
      (PL (l + 1) : Measure (A (l + 1))) (Q : Measure (A (l + 1))) (b l) (hb l)
  choose M hMF hMin using fun l => (hFc l).isCompact.exists_isMinOn (hFn l) (hf l).continuousOn
  let d (l : ℕ) := f l (M l)
  have hdBound (l : ℕ) : d l ≤ 1 := by
    change (⨆ E : {E : Set (A l) // MeasurableSet E},
      max ((PL l : Measure (A l)) E.val - (M l : Measure (A l)) E.val)
        ((M l : Measure (A l)) E.val - (PL l : Measure (A l)) E.val)) ≤ 1
    exact iSup_le fun _ => max_le (tsub_le_self.trans prob_le_one)
      (tsub_le_self.trans prob_le_one)
  let r := ⨆ l, d l
  have hd : Monotone d := monotone_nat_of_le_succ fun l =>
    (hMin l (hpres l (hMF (l + 1)))).trans (hcontract l (M (l + 1)))
  let G (l : ℕ) := F l ∩ {Q | f l Q ≤ r}
  have hGc (l : ℕ) : IsClosed (G l) := (hFc l).inter (isClosed_le (hf l) continuous_const)
  have hGn (l : ℕ) : (G l).Nonempty := ⟨M l, hMF l, le_iSup d l⟩
  have hGp (l : ℕ) {Q : ProbabilityMeasure (A (l + 1))} (hQ : Q ∈ G (l + 1)) :
      p l Q ∈ G l := ⟨hpres l hQ.1, (hcontract l Q).trans hQ.2⟩
  let H (l : ℕ) := TopCat.of (G l)
  let bond (l : ℕ) : H (l + 1) ⟶ H l :=
    TopCat.ofHom ⟨fun Q => ⟨p l Q.val, hGp l Q.property⟩,
      ((ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := b l))).comp
        continuous_subtype_val).subtype_mk _⟩
  let diagram := Functor.ofOpSequence bond
  have : ∀ l, CompactSpace (G l) := fun l => isCompact_iff_compactSpace.mp (hGc l).isCompact
  have : ∀ l, Nonempty (G l) := fun l => (hGn l).to_subtype
  have : ∀ j, Nonempty (diagram.obj j) := fun j => (hGn j.unop).to_subtype
  have : ∀ j, CompactSpace (diagram.obj j) := fun j =>
    isCompact_iff_compactSpace.mp (hGc j.unop).isCompact
  have : ∀ j, T2Space (diagram.obj j) := fun j => inferInstanceAs (T2Space (G j.unop))
  let thread := (TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system diagram).some
  let QL (l : ℕ) : ProbabilityMeasure (A l) := (thread.val ⟨l⟩).val
  have hQL (l : ℕ) : (QL (l + 1) : Measure _).map (b l) = (QL l : Measure _) := by
    have h := thread.property ((homOfLE (Nat.le_add_right l 1)).op)
    simp only [diagram, Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg (fun z => (z.val : Measure (A l))) h
  obtain ⟨Q, hQ, _⟩ := exists_unique_probability_extension q hq (n + 1) QL hQL
  have hfeas : Feasible (threadEquiv q g hg) (⋂ l, π l ⁻¹' S l)
      (μ : Measure (Thread B q)) (Q : Measure _) := by
    apply (feasible_iff_all_levels q g hg n S μ Q).mpr
    intro l
    rw [hQ l]
    exact (thread.val ⟨l⟩).property.1
  have lower (R : ProbabilityMeasure (Fin (n + 1) → Thread B q))
      (hR : Feasible (threadEquiv q g hg) (⋂ l, π l ⁻¹' S l)
        (μ : Measure (Thread B q)) (R : Measure _)) :
      r ≤ measurableTotalVariation (P : Measure (Fin (n + 1) → Thread B q)) (R : Measure _) := by
    have hRL := (feasible_iff_all_levels q g hg n S μ R).mp hR
    rw [total_variation_eq_iSup_level q (n + 1)]
    refine iSup_le fun l => ?_
    let RL : ProbabilityMeasure (A l) := R.map (hπ l).aemeasurable
    have hm : RL ∈ F l := hRL l
    have hmin : d l ≤ f l RL := hMin l hm
    exact hmin.trans (le_iSup (fun k =>
      measurableTotalVariation ((P : Measure (Fin (n + 1) → Thread B q)).map (π k))
        ((R : Measure (Fin (n + 1) → Thread B q)).map (π k))) l)
  have upper : measurableTotalVariation
      (P : Measure (Fin (n + 1) → Thread B q)) (Q : Measure _) ≤ r := by
    rw [total_variation_eq_iSup_level q (n + 1)]
    refine iSup_le fun l => ?_
    rw [hQ l]
    exact (thread.val ⟨l⟩).property.2
  refine ⟨d, ?_, hd, hdBound, Q, hfeas, le_antisymm upper (lower Q hfeas), ?_⟩
  · intro l
    refine ⟨M l, ?_, rfl, ?_⟩
    · have hm := hMF l
      change Feasible (g l) (S l) (μL l : Measure (B l)) (M l : Measure (A l)) at hm
      rwa [hML l] at hm
    · intro R hR
      apply hMin l
      change Feasible (g l) (S l) (μL l : Measure (B l)) (R : Measure (A l))
      rwa [hML l]
  · intro R hR
    exact upper.trans (lower R hR)

#print axioms exists_feasible_minimum_eq_iSup

end D5.S3.Estimation.DataProcessing.InverseLimitFeasibleMinimum

/- GID: D5/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InverseLimitFeasibleLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal support, exact node marginals and zero excess are detected by finite laws. -/

import D5.S3.Estimation.DataProcessing.InverseLimitZeroExcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.InverseLimitFeasibleLaws

universe u
open Set Function MeasureTheory
open scoped ENNReal
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.OneCutZeroExcess
open D5.S3.Estimation.DataProcessing.InverseLimitZeroExcess
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- A feasible law has legal support, exact marginals and zero expected excess. -/
def Feasible {B : Type*} [MeasurableSpace B] {n : ℕ}
    (g : B ≃ B) (S : Set (Fin (n + 1) → B)) (μ : Measure B)
    (Q : Measure (Fin (n + 1) → B)) : Prop :=
  Q S = 1 ∧ (∀ j, Q.map (fun y => y j) = μ) ∧
    (∫⁻ y, (cycleExcess g y : ℝ≥0∞) ∂Q) = 0

/-- Feasibility of a probability on the completed space is exactly feasibility
of all its actual projections. No support or zero-excess correspondence is
assumed, and the marginal probability is arbitrary. -/
theorem feasible_iff_all_levels {B : ℕ → Type u}
    [∀ l, Finite (B l)] [∀ l, TopologicalSpace (B l)] [∀ l, DiscreteTopology (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, BorelSpace (B l)]
    (q : (l : ℕ) → B (l + 1) → B l) (g : (l : ℕ) → B l ≃ B l)
    (hg : ∀ l x, q l (g (l + 1) x) = g l (q l x)) (n : ℕ)
    (S : (l : ℕ) → Set (Fin (n + 1) → B l))
    (μ : ProbabilityMeasure (Thread B q)) (Q : ProbabilityMeasure (Fin (n + 1) → Thread B q)) :
    Feasible (threadEquiv q g hg) (⋂ l, levelProjection q (n + 1) l ⁻¹' S l)
      (μ : Measure (Thread B q)) (Q : Measure (Fin (n + 1) → Thread B q)) ↔
    ∀ l, Feasible (g l) (S l) ((μ : Measure (Thread B q)).map (fun x => x.val l))
      ((Q : Measure (Fin (n + 1) → Thread B q)).map (levelProjection q (n + 1) l)) := by
  classical
  let X := Thread B q
  let π := levelProjection q (n + 1)
  have hπ (l : ℕ) : Measurable (π l) :=
    measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  have hp (l : ℕ) : Measurable (fun x : X => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hS (l : ℕ) : MeasurableSet (S l) := (Set.toFinite _).measurableSet
  have hsupp : (Q : Measure (Fin (n + 1) → X)) (⋂ l, π l ⁻¹' S l) = 1 ↔
      ∀ l, ((Q : Measure (Fin (n + 1) → X)).map (π l)) (S l) = 1 := by
    rw [← mem_ae_iff_prob_eq_one (MeasurableSet.iInter fun l => hπ l (hS l))]
    change (∀ᵐ y ∂(Q : Measure _), y ∈ ⋂ l, π l ⁻¹' S l) ↔ _
    simp only [Set.mem_iInter, Set.mem_preimage]
    rw [ae_all_iff]
    apply forall_congr'
    intro l
    rw [Measure.map_apply (hπ l) (hS l), ← mem_ae_iff_prob_eq_one (hπ l (hS l))]
    rfl
  have hmarg : (∀ j, (Q : Measure (Fin (n + 1) → X)).map (fun y => y j) = (μ : Measure X)) ↔
      ∀ l j, ((Q : Measure (Fin (n + 1) → X)).map (π l)).map (fun y => y j) =
        (μ : Measure X).map (fun x => x.val l) := by
    constructor
    · intro h l j
      rw [Measure.map_map (measurable_pi_apply j) (hπ l), ← h j,
        Measure.map_map (hp l) (measurable_pi_apply j)]
      rfl
    · intro h j
      let ν := (Q : Measure (Fin (n + 1) → X)).map (fun y => y j)
      have : IsProbabilityMeasure ν :=
        Measure.isProbabilityMeasure_map (measurable_pi_apply j).aemeasurable
      have heq (l : ℕ) : ν.map (fun x => x.val l) = (μ : Measure X).map (fun x => x.val l) := by
        rw [show ν = (Q : Measure (Fin (n + 1) → X)).map (fun y => y j) from rfl,
          Measure.map_map (hp l) (measurable_pi_apply j)]
        simpa only [Measure.map_map (measurable_pi_apply j) (hπ l), π,
          levelProjection, Function.comp_def] using h l j
      let c : X → Fin 1 → X := fun x _ => x
      have hc : Measurable c := measurable_pi_lambda _ fun _ => measurable_id
      have hlev (l : ℕ) : (ν.map c).map (levelProjection q 1 l) =
          ((μ : Measure X).map c).map (levelProjection q 1 l) := by
        have hp1 : Measurable (levelProjection q 1 l) :=
          measurable_pi_lambda _ fun i =>
            (hp l).comp (measurable_pi_apply i)
        have hc1 : Measurable (fun x : B l => fun _ : Fin 1 => x) :=
          measurable_pi_lambda _ fun _ => measurable_id
        rw [Measure.map_map hp1 hc, Measure.map_map hp1 hc]
        have hc_eq : levelProjection q 1 l ∘ c =
            (fun x : B l => fun _ : Fin 1 => x) ∘ (fun x : X => x.val l) := rfl
        rw [hc_eq, ← Measure.map_map hc1 (hp l), ← Measure.map_map hc1 (hp l), heq l]
      have hv : measurableTotalVariation (ν.map c) ((μ : Measure X).map c) = 0 := by
        rw [total_variation_eq_iSup_level q 1]
        simp only [hlev, measurableTotalVariation, tsub_self, max_self, iSup_const]
      apply Measure.ext
      intro A hA
      let C : Set (Fin 1 → X) := (fun y => y 0) ⁻¹' A
      have hC : MeasurableSet C := (measurable_pi_apply 0) hA
      have hgap := le_iSup (fun e : {s : Set (Fin 1 → X) // MeasurableSet s} =>
        max ((ν.map c) e.val - ((μ : Measure X).map c) e.val)
          (((μ : Measure X).map c) e.val - (ν.map c) e.val)) ⟨C, hC⟩
      change max ((ν.map c) C - ((μ : Measure X).map c) C)
        (((μ : Measure X).map c) C - (ν.map c) C) ≤
          measurableTotalVariation (ν.map c) ((μ : Measure X).map c) at hgap
      rw [hv, Measure.map_apply hc hC, Measure.map_apply hc hC] at hgap
      have hCA : c ⁻¹' C = A := rfl
      rw [hCA] at hgap
      exact le_antisymm
        (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_left _ _).trans hgap) bot_le))
        (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_right _ _).trans hgap) bot_le))
  unfold Feasible
  rw [hsupp, hmarg, expected_excess_zero_iff_all_levels q g hg n]
  exact ⟨fun h l => ⟨h.1 l, h.2.1 l, h.2.2 l⟩,
    fun h => ⟨fun l => (h l).1, fun l => (h l).2.1, fun l => (h l).2.2⟩⟩

#print axioms feasible_iff_all_levels

end D5.S3.Estimation.DataProcessing.InverseLimitFeasibleLaws

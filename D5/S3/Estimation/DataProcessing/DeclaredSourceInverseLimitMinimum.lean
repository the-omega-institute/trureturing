/- GID: D5/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum
   generality: I
   mirror-B: D5/B/S3/Estimation/DataProcessing/DeclaredSourceInverseLimitMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact label and joint-source constraints on arbitrary finite towers admit completed total-variation minimizers at the supremum of finite minima, with a common-radius equivalence and weakly lower semicontinuous costs. -/

import D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
import D5.S3.TotalVariation.Metric
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation

open Set Function TopologicalSpace CategoryTheory
open D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
open scoped ENNReal NNReal
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open private measurable_total_variation_map_le from
  D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
universe u v w
open Filter

namespace D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum

lemma event_tv_normalization {X : Type u} [MeasurableSpace X] (P Q : ProbabilityMeasure X) :
    let S : Set ℝ := Set.range (fun E : {E : Set X // MeasurableSet E} =>
      |(P : Measure X).real E.val - (Q : Measure X).real E.val|)
    let C : Set ℝ := Set.range (fun E : {E : Set X // NullMeasurableSet E ((P : Measure X) + (Q : Measure X))} =>
      |((P : Measure X).completion E.val).toReal - ((Q : Measure X).completion E.val).toReal|)
    (measurableTotalVariation (P : Measure X) (Q : Measure X)).toReal = sSup S ∧
      sSup C = sSup S := by
  classical
  dsimp only
  let gap (E : {E : Set X // MeasurableSet E}) : ℝ :=
    |(P : Measure X).real E.val - (Q : Measure X).real E.val|
  let S : Set ℝ := Set.range gap
  have hgap (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
      max (a - b) (b - a) = ENNReal.ofReal |a.toReal - b.toReal| := by
    have h₁ : ENNReal.ofReal (a.toReal - b.toReal) = a - b := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
    have h₂ : ENNReal.ofReal (b.toReal - a.toReal) = b - a := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb, ENNReal.ofReal_toReal ha]
    rw [← h₁, ← h₂]
    by_cases h : b.toReal ≤ a.toReal
    · rw [abs_of_nonneg (sub_nonneg.mpr h), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h),
        max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (a.toReal - b.toReal) from bot_le)]
    · have hh : a.toReal < b.toReal := lt_of_not_ge h
      rw [abs_of_neg (sub_neg.mpr hh), ENNReal.ofReal_of_nonpos (le_of_lt (sub_neg.mpr hh)),
        max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b.toReal - a.toReal) from bot_le)]
      congr 1
      ring
  have hgapE (E : {E : Set X // MeasurableSet E}) :
      max ((P : Measure X) E.val - (Q : Measure X) E.val)
        ((Q : Measure X) E.val - (P : Measure X) E.val) = ENNReal.ofReal (gap E) :=
    hgap _ _ (measure_ne_top _ _) (measure_ne_top _ _)
  have hbound : measurableTotalVariation (P : Measure X) (Q : Measure X) ≤ 1 := by
    unfold measurableTotalVariation
    exact iSup_le fun _ => max_le (tsub_le_self.trans prob_le_one)
      (tsub_le_self.trans prob_le_one)
  have hfinite : measurableTotalVariation (P : Measure X) (Q : Measure X) ≠ ⊤ :=
    ne_of_lt (hbound.trans_lt (by simp))
  have hgapNonneg (E : {E : Set X // MeasurableSet E}) : 0 ≤ gap E := abs_nonneg _
  have hgapLe (E : {E : Set X // MeasurableSet E}) :
      gap E ≤ (measurableTotalVariation (P : Measure X) (Q : Measure X)).toReal := by
    have h := le_iSup (fun e : {E : Set X // MeasurableSet E} =>
      max ((P : Measure X) e.val - (Q : Measure X) e.val)
        ((Q : Measure X) e.val - (P : Measure X) e.val)) E
    change max ((P : Measure X) E.val - (Q : Measure X) E.val)
      ((Q : Measure X) E.val - (P : Measure X) E.val) ≤
        measurableTotalVariation (P : Measure X) (Q : Measure X) at h
    rw [hgapE] at h
    have hh := ENNReal.toReal_mono hfinite h
    simpa only [ENNReal.toReal_ofReal (hgapNonneg E)] using hh
  have hSne : S.Nonempty := ⟨gap ⟨∅, MeasurableSet.empty⟩, Set.mem_range_self _⟩
  have hSb : BddAbove S := ⟨1, by
    rintro _ ⟨E, rfl⟩
    have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hbound
    exact (hgapLe E).trans (by simpa only [ENNReal.toReal_one] using h)⟩
  have hSnonneg : 0 ≤ sSup S :=
    (hgapNonneg ⟨∅, MeasurableSet.empty⟩).trans (le_csSup hSb (Set.mem_range_self _))
  have hreal : (measurableTotalVariation (P : Measure X) (Q : Measure X)).toReal = sSup S := by
    apply le_antisymm
    · have hupper : measurableTotalVariation (P : Measure X) (Q : Measure X) ≤
          ENNReal.ofReal (sSup S) := by
        unfold measurableTotalVariation
        refine iSup_le fun E => ?_
        rw [hgapE]
        exact ENNReal.ofReal_le_ofReal (le_csSup hSb (Set.mem_range_self E))
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
      simpa only [ENNReal.toReal_ofReal hSnonneg] using hh
    · apply csSup_le hSne
      rintro _ ⟨E, rfl⟩
      exact hgapLe E
  refine ⟨hreal, ?_⟩
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨E, rfl⟩
    let F := toMeasurable ((P : Measure X) + (Q : Measure X)) E.val
    have hF : MeasurableSet F := measurableSet_toMeasurable _ _
    have he : F =ᵐ[(P : Measure X) + (Q : Measure X)] E.val := E.property.toMeasurable_ae_eq
    have hp : F =ᵐ[(P : Measure X)] E.val :=
      (le_add_of_nonneg_right bot_le : (P : Measure X) ≤ (P : Measure X) + (Q : Measure X)).absolutelyContinuous.ae_le he
    have hq : F =ᵐ[(Q : Measure X)] E.val :=
      (le_add_of_nonneg_left bot_le : (Q : Measure X) ≤ (P : Measure X) + (Q : Measure X)).absolutelyContinuous.ae_le he
    refine ⟨⟨F, hF⟩, ?_⟩
    change |((P : Measure X) F).toReal - ((Q : Measure X) F).toReal| =
      |((P : Measure X) E.val).toReal - ((Q : Measure X) E.val).toReal|
    rw [measure_congr hp, measure_congr hq]
  · rintro ⟨E, rfl⟩
    refine ⟨⟨E.val, E.property.nullMeasurableSet⟩, ?_⟩
    simp only [Measure.completion_apply, measureReal_def]


lemma finite_feasible_pushforward {W Z U : ℕ → Type u}
    [∀ l, Finite (W l)] [∀ l, TopologicalSpace (W l)] [∀ l, DiscreteTopology (W l)]
    [∀ l, MeasurableSpace (W l)] [∀ l, BorelSpace (W l)]
    [∀ l, Finite (Z l)] [∀ l, TopologicalSpace (Z l)] [∀ l, DiscreteTopology (Z l)]
    [∀ l, MeasurableSpace (Z l)] [∀ l, BorelSpace (Z l)]
    [∀ l, Finite (U l)] [∀ l, TopologicalSpace (U l)] [∀ l, DiscreteTopology (U l)]
    [∀ l, MeasurableSpace (U l)] [∀ l, BorelSpace (U l)]
    (α : (l : ℕ) → W (l + 1) → W l)
    (β : (l : ℕ) → Z (l + 1) → Z l)
    (γ : (l : ℕ) → U (l + 1) → U l)
    (label : (l : ℕ) → W l → Z l) (source : (l : ℕ) → W l → U l)
    (hlabel : ∀ l x, label l (α l x) = β l (label (l + 1) x))
    (hsource : ∀ l x, source l (α l x) = γ l (source (l + 1) x))
    (Q : (l : ℕ) → ProbabilityMeasure (Z l))
    (hQ : ∀ l, (Q (l + 1) : Measure (Z (l + 1))).map (β l) = (Q l : Measure (Z l)))
    (A : (l : ℕ) → Set (W l)) (hA : ∀ l, A (l + 1) ⊆ (α l) ⁻¹' A l)
    (ρ : ProbabilityMeasure (Thread W α)) (l : ℕ) (θ : ProbabilityMeasure (W (l + 1)))
    (ht : (θ : Measure (W (l + 1))).map (label (l + 1)) = (Q (l + 1) : Measure (Z (l + 1))) ∧
      (θ : Measure (W (l + 1))).map (source (l + 1)) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val (l + 1))).map (source (l + 1)) ∧
      (θ : Measure (W (l + 1))) (A (l + 1)) = 1) :
    let θ : ProbabilityMeasure (W l) := θ.map (measurable_of_countable (α l)).aemeasurable
    (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
      (θ : Measure (W l)).map (source l) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
      (θ : Measure (W l)) (A l) = 1 := by
  classical
  have hπ (k : ℕ) : Measurable (fun x : Thread W α => x.val k) :=
    (measurable_pi_apply k).comp measurable_subtype_coe
  change ((θ : Measure (W (l + 1))).map (α l)).map (label l) = _ ∧
    ((θ : Measure (W (l + 1))).map (α l)).map (source l) = _ ∧
    ((θ : Measure (W (l + 1))).map (α l)) (A l) = 1
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      show label l ∘ α l = β l ∘ label (l + 1) from funext (hlabel l),
      ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), ht.1, hQ l]
  · rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      show source l ∘ α l = γ l ∘ source (l + 1) from funext (hsource l),
      ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), ht.2.1,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (hπ (l + 1)),
      Measure.map_map (measurable_of_countable _) (hπ l)]
    congr 1
    funext x
    exact (hsource l _).symm.trans (congrArg (source l) (x.property l))
  · rw [Measure.map_apply (measurable_of_countable _) (Set.toFinite (A l)).measurableSet]
    exact le_antisymm prob_le_one (by rw [← ht.2.2]; exact measure_mono (hA l))

lemma finite_feasible_minimum {W : Type u} {Z : Type u} {U : Type u}
    [Finite W] [TopologicalSpace W] [DiscreteTopology W] [MeasurableSpace W] [BorelSpace W]
    [Finite Z] [TopologicalSpace Z] [DiscreteTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    [Finite U] [TopologicalSpace U] [DiscreteTopology U] [MeasurableSpace U] [BorelSpace U]
    (label : W → Z) (source : W → U) (Q : ProbabilityMeasure Z) (ρ : ProbabilityMeasure W)
    (A : Set W)
    (hne : ∃ θ : ProbabilityMeasure W,
      (θ : Measure W).map label = (Q : Measure Z) ∧
      (θ : Measure W).map source = (ρ : Measure W).map source ∧ (θ : Measure W) A = 1) :
    let L : Set (ProbabilityMeasure W) := {θ |
      (θ : Measure W).map label = (Q : Measure Z) ∧
      (θ : Measure W).map source = (ρ : Measure W).map source ∧ (θ : Measure W) A = 1}
    let f : ProbabilityMeasure W → ℝ≥0∞ := fun θ => measurableTotalVariation (ρ : Measure W) (θ : Measure W)
    IsClosed L ∧ IsCompact L ∧ Continuous f ∧
      ∃ θ ∈ L, ∀ η ∈ L, f θ ≤ f η := by
  classical
  dsimp only
  let L : Set (ProbabilityMeasure W) := {θ |
      (θ : Measure W).map label = (Q : Measure Z) ∧
      (θ : Measure W).map source = (ρ : Measure W).map source ∧ (θ : Measure W) A = 1}
  let f : ProbabilityMeasure W → ℝ≥0∞ := fun θ => measurableTotalVariation (ρ : Measure W) (θ : Measure W)
  have hmass (E : Set W) : Continuous (fun θ : ProbabilityMeasure W => (θ : Measure W) E) := by
    let v : ContinuousMap W ℝ≥0 := ⟨E.indicator (fun _ => 1), continuous_of_discreteTopology⟩
    have hv := ProbabilityMeasure.continuous_lintegral_continuousMap v
    simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_indicator, ENNReal.coe_one,
      lintegral_indicator_const (Set.toFinite E).measurableSet, one_mul] using hv
  have hlabel : IsClosed {θ : ProbabilityMeasure W | (θ : Measure W).map label = (Q : Measure Z)} := by
    have hc : IsClosed {θ : ProbabilityMeasure W |
      θ.map (continuous_of_discreteTopology (f := label)).measurable.aemeasurable = Q} :=
      isClosed_eq (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := label))) continuous_const
    convert hc using 1
    ext θ
    exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
  have hsource : IsClosed {θ : ProbabilityMeasure W |
      (θ : Measure W).map source = (ρ : Measure W).map source} := by
    have hc : IsClosed {θ : ProbabilityMeasure W |
      θ.map (continuous_of_discreteTopology (f := source)).measurable.aemeasurable =
        ρ.map (continuous_of_discreteTopology (f := source)).measurable.aemeasurable} :=
      isClosed_eq (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := source))) continuous_const
    convert hc using 1
    ext θ
    exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
  have hL : IsClosed L := hlabel.inter (hsource.inter (isClosed_eq (hmass A) continuous_const))
  have hf : Continuous f := by
    letI : Fintype {E : Set W // MeasurableSet E} := Fintype.ofFinite _
    unfold f measurableTotalVariation
    simpa only [Finset.sup_univ_eq_iSup, Function.comp_def] using
      (Continuous.finset_sup_apply (s := Finset.univ)
        fun (E : {E : Set W // MeasurableSet E}) _ =>
          ((ENNReal.continuous_sub_left (measure_ne_top (ρ : Measure W) E.val)).comp
            (hmass E.val)).max
          ((ENNReal.continuous_sub_right ((ρ : Measure W) E.val)).comp (hmass E.val)))
  exact ⟨hL, hL.isCompact, hf, hL.isCompact.exists_isMinOn hne hf.continuousOn⟩

lemma thread_tv_eq_iSup {B : ℕ → Type u} [∀ l, Finite (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, MeasurableSingletonClass (B l)]
    (q : (l : ℕ) → B (l + 1) → B l)
    (P Q : Measure (Thread B q)) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measurableTotalVariation P Q =
      ⨆ l, measurableTotalVariation (P.map (fun x => x.val l)) (Q.map (fun x => x.val l)) := by
  have single {A : Type u} [MeasurableSpace A] (M N : Measure A) :
      measurableTotalVariation (M.map (fun x => fun _ : Fin 1 => x)) (N.map (fun x => fun _ : Fin 1 => x)) =
        measurableTotalVariation M N := by
    let c : A → Fin 1 → A := fun x _ => x
    have hc : Measurable c := Measurable.of_eval fun _ => measurable_id
    have hback : (fun y : Fin 1 → A => y 0) ∘ c = id := rfl
    refine le_antisymm (measurable_total_variation_map_le M N c hc) ?_
    have hb := measurable_total_variation_map_le (M.map c) (N.map c)
      (fun y : Fin 1 → A => y 0) (measurable_pi_apply 0)
    simpa only [Measure.map_map (measurable_pi_apply 0) hc, hback, Measure.map_id] using hb
  let c : Thread B q → Fin 1 → Thread B q := fun x _ => x
  have hc : Measurable c := Measurable.of_eval fun _ => measurable_id
  have hπ (l : ℕ) : Measurable (fun x : Thread B q => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hlev (l : ℕ) : Measurable (levelProjection q 1 l) :=
    Measurable.of_eval fun j => (hπ l).comp (measurable_pi_apply j)
  rw [← single P Q, total_variation_eq_iSup_level q 1]
  congr 1
  funext l
  rw [Measure.map_map (hlev l) hc, Measure.map_map (hlev l) hc]
  have hf : levelProjection q 1 l ∘ c =
      (fun x => fun _ : Fin 1 => x) ∘ (fun x : Thread B q => x.val l) := rfl
  have he : Measurable (fun x : B l => fun _ : Fin 1 => x) :=
    Measurable.of_eval fun _ => measurable_id
  rw [hf, ← Measure.map_map he (hπ l), ← Measure.map_map he (hπ l), single]

lemma select_common_radius {W Z U : ℕ → Type u}
    [∀ l, Finite (W l)] [∀ l, TopologicalSpace (W l)] [∀ l, DiscreteTopology (W l)]
    [∀ l, MeasurableSpace (W l)] [∀ l, BorelSpace (W l)]
    [∀ l, Finite (Z l)] [∀ l, TopologicalSpace (Z l)] [∀ l, DiscreteTopology (Z l)]
    [∀ l, MeasurableSpace (Z l)] [∀ l, BorelSpace (Z l)]
    [∀ l, Finite (U l)] [∀ l, TopologicalSpace (U l)] [∀ l, DiscreteTopology (U l)]
    [∀ l, MeasurableSpace (U l)] [∀ l, BorelSpace (U l)]
    (α : (l : ℕ) → W (l + 1) → W l)
    (β : (l : ℕ) → Z (l + 1) → Z l)
    (γ : (l : ℕ) → U (l + 1) → U l)
    (label : (l : ℕ) → W l → Z l) (source : (l : ℕ) → W l → U l)
    (hlabel : ∀ l x, label l (α l x) = β l (label (l + 1) x))
    (hsource : ∀ l x, source l (α l x) = γ l (source (l + 1) x))
    (Q : (l : ℕ) → ProbabilityMeasure (Z l))
    (hQ : ∀ l, (Q (l + 1) : Measure (Z (l + 1))).map (β l) = (Q l : Measure (Z l)))
    (A : (l : ℕ) → Set (W l)) (hA : ∀ l, A (l + 1) ⊆ (α l) ⁻¹' A l)
    (ρ : ProbabilityMeasure (Thread W α)) (c : ℝ≥0∞) :
    let F (l : ℕ) : Set (ProbabilityMeasure (W l)) := {θ |
      (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
      (θ : Measure (W l)).map (source l) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
      (θ : Measure (W l)) (A l) = 1}
    (∀ l, ∃ θ ∈ F l,
      measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l))
        (θ : Measure (W l)) ≤ c) →
    ∃ θ : (l : ℕ) → ProbabilityMeasure (W l),
      (∀ l, θ l ∈ F l ∧
        measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l))
          (θ l : Measure (W l)) ≤ c) ∧
      (∀ l, (θ (l + 1) : Measure (W (l + 1))).map (α l) = (θ l : Measure (W l))) := by
  classical
  dsimp only
  let F (l : ℕ) : Set (ProbabilityMeasure (W l)) := {θ |
      (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
      (θ : Measure (W l)).map (source l) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
      (θ : Measure (W l)) (A l) = 1}
  intro hne
  have hπ₀ (l : ℕ) : Measurable (fun x : Thread W α => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hFc (l : ℕ) : IsClosed (F l) := by
    have hmass (E : Set (W l)) : Continuous (fun θ : ProbabilityMeasure (W l) => (θ : Measure (W l)) E) := by
      let v : ContinuousMap (W l) ℝ≥0 := ⟨E.indicator (fun _ => 1), continuous_of_discreteTopology⟩
      simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_indicator, ENNReal.coe_one,
        lintegral_indicator_const (Set.toFinite E).measurableSet, one_mul] using
        ProbabilityMeasure.continuous_lintegral_continuousMap v
    have hl : IsClosed {θ : ProbabilityMeasure (W l) | (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l))} := by
      have hc := isClosed_eq (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := label l)))
        (continuous_const (y := Q l))
      convert hc using 1
      ext θ
      exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
    let R : ProbabilityMeasure (U l) :=
      (ρ.map (hπ₀ l).aemeasurable).map (measurable_of_countable (source l)).aemeasurable
    have hs : IsClosed {θ : ProbabilityMeasure (W l) | (θ : Measure (W l)).map (source l) = (R : Measure (U l))} := by
      have hc := isClosed_eq (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := source l)))
        (continuous_const (y := R))
      convert hc using 1
      ext θ
      exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
    exact hl.inter (hs.inter (isClosed_eq (hmass (A l)) continuous_const))
  have hpres (l : ℕ) (θ : ProbabilityMeasure (W (l + 1))) (ht : θ ∈ F (l + 1)) :
      θ.map (continuous_of_discreteTopology (f := α l)).measurable.aemeasurable ∈ F l :=
    finite_feasible_pushforward α β γ label source hlabel hsource Q hQ A hA ρ l θ ht
  let p (l : ℕ) (Q : ProbabilityMeasure (W (l + 1))) :=
    Q.map (continuous_of_discreteTopology (f := α l)).measurable.aemeasurable
  let f (l : ℕ) (Q : ProbabilityMeasure (W l)) :=
    measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l)) (Q : Measure (W l))
  have hπ (l : ℕ) : Measurable (fun x : Thread W α => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hmass (l : ℕ) (E : Set (W l)) :
      Continuous (fun Q : ProbabilityMeasure (W l) => (Q : Measure (W l)) E) := by
    let v : ContinuousMap (W l) ℝ≥0 := ⟨E.indicator (fun _ => 1), continuous_of_discreteTopology⟩
    have hv := ProbabilityMeasure.continuous_lintegral_continuousMap v
    simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_indicator, ENNReal.coe_one,
      lintegral_indicator_const (Set.toFinite E).measurableSet, one_mul] using hv
  have hf (l : ℕ) : Continuous (f l) := by
    letI : Fintype {E : Set (W l) // MeasurableSet E} := Fintype.ofFinite _
    unfold f measurableTotalVariation
    simpa only [Finset.sup_univ_eq_iSup, Function.comp_def] using
      (Continuous.finset_sup_apply (s := Finset.univ)
        fun (E : {E : Set (W l) // MeasurableSet E}) _ =>
          ((ENNReal.continuous_sub_left (measure_ne_top
            ((ρ : Measure (Thread W α)).map (fun x => x.val l)) E.val)).comp (hmass l E.val)).max
          ((ENNReal.continuous_sub_right
            (((ρ : Measure (Thread W α)).map (fun x => x.val l)) E.val)).comp (hmass l E.val)))
  have hcontract (l : ℕ) (Q : ProbabilityMeasure (W (l + 1))) : f l (p l Q) ≤ f (l + 1) Q := by
    have hρ : ((ρ : Measure (Thread W α)).map (fun x => x.val (l + 1))).map (α l) =
        (ρ : Measure (Thread W α)).map (fun x => x.val l) := by
      rw [Measure.map_map (measurable_of_countable (α l)) (hπ (l + 1))]
      congr 1
      funext x
      exact x.property l
    change measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l))
      ((Q : Measure (W (l + 1))).map (α l)) ≤ _
    rw [← hρ]
    exact measurable_total_variation_map_le _ _ (α l) (measurable_of_countable (α l))
  let G (l : ℕ) := F l ∩ {Q | f l Q ≤ c}
  have hGc (l : ℕ) : IsClosed (G l) := (hFc l).inter (isClosed_le (hf l) continuous_const)
  have hGn (l : ℕ) : (G l).Nonempty := hne l
  have hGp (l : ℕ) {Q : ProbabilityMeasure (W (l + 1))} (hQ : Q ∈ G (l + 1)) :
      p l Q ∈ G l := ⟨hpres l Q hQ.1, (hcontract l Q).trans hQ.2⟩
  let H (l : ℕ) := TopCat.of (G l)
  let bond (l : ℕ) : H (l + 1) ⟶ H l :=
    TopCat.ofHom ⟨fun Q => ⟨p l Q.val, hGp l Q.property⟩,
      ((ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := α l))).comp
        continuous_subtype_val).subtype_mk _⟩
  let diagram := CategoryTheory.Functor.ofOpSequence bond
  haveI : ∀ j, Nonempty (diagram.obj j) := fun j => (hGn j.unop).to_subtype
  haveI : ∀ j, CompactSpace (diagram.obj j) := fun j =>
    isCompact_iff_compactSpace.mp (hGc j.unop).isCompact
  haveI : ∀ j, T2Space (diagram.obj j) := fun j => inferInstanceAs (T2Space (G j.unop))
  let thread := (TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system diagram).some
  let Q (l : ℕ) : ProbabilityMeasure (W l) := (thread.val ⟨l⟩).val
  refine ⟨Q, fun l => (thread.val ⟨l⟩).property, ?_⟩
  intro l
  have ht := thread.property ((homOfLE (Nat.le_add_right l 1)).op)
  simp only [diagram, CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] at ht
  exact congrArg (fun z => (z.val : Measure (W l))) ht

lemma feasible_mixture {W : Type u} {Z : Type u} {U : Type u}
    [MeasurableSpace W] [MeasurableSpace Z] [MeasurableSpace U]
    (label : W → Z) (source : W → U) (hl : Measurable label) (hs : Measurable source)
    (Q : ProbabilityMeasure Z) (ν : ProbabilityMeasure U) (A : Set W)
    (θ η : ProbabilityMeasure W)
    (hθ : (θ : Measure W).map label = (Q : Measure Z) ∧
      (θ : Measure W).map source = (ν : Measure U) ∧ (θ : Measure W) A = 1)
    (hη : (η : Measure W).map label = (Q : Measure Z) ∧
      (η : Measure W).map source = (ν : Measure U) ∧ (η : Measure W) A = 1)
    (a : ℝ≥0∞) (ha : a ≤ 1) :
    let M := a • (θ : Measure W) + (1 - a) • (η : Measure W)
    IsProbabilityMeasure M ∧ M.map label = (Q : Measure Z) ∧
      M.map source = (ν : Measure U) ∧ M A = 1 := by
  have hsum : a + (1 - a) = 1 := add_tsub_cancel_of_le ha
  dsimp only
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, hsum]
  · rw [Measure.map_add _ _ hl, Measure.map_smul, Measure.map_smul, hθ.1, hη.1,
      ← add_smul, hsum, one_smul]
  · rw [Measure.map_add _ _ hs, Measure.map_smul, Measure.map_smul, hθ.2.1, hη.2.1,
      ← add_smul, hsum, one_smul]
  · simp only [Measure.add_apply, Measure.smul_apply, hθ.2.2, hη.2.2, smul_eq_mul, mul_one, hsum]
set_option maxHeartbeats 8000000 in
/-- Source-constrained minima on actual inverse limits, with exact normalized costs. -/
theorem exists_minimum_eq_iSup {W Z U : ℕ → Type u}
    [∀ l, Finite (W l)] [∀ l, Nonempty (W l)]
    [∀ l, Finite (Z l)] [∀ l, Nonempty (Z l)]
    [∀ l, Finite (U l)] [∀ l, Nonempty (U l)]
    [∀ l, TopologicalSpace (W l)] [∀ l, DiscreteTopology (W l)]
    [∀ l, MeasurableSpace (W l)] [∀ l, BorelSpace (W l)]
    [∀ l, TopologicalSpace (Z l)] [∀ l, DiscreteTopology (Z l)]
    [∀ l, MeasurableSpace (Z l)] [∀ l, BorelSpace (Z l)]
    [∀ l, TopologicalSpace (U l)] [∀ l, DiscreteTopology (U l)]
    [∀ l, MeasurableSpace (U l)] [∀ l, BorelSpace (U l)]
    (α : (l : ℕ) → W (l + 1) → W l)
    (β : (l : ℕ) → Z (l + 1) → Z l)
    (γ : (l : ℕ) → U (l + 1) → U l)
    (label : (l : ℕ) → W l → Z l) (source : (l : ℕ) → W l → U l)
    (hlabel : ∀ l x, label l (α l x) = β l (label (l + 1) x))
    (hsource : ∀ l x, source l (α l x) = γ l (source (l + 1) x))
    (f : Thread W α → Thread Z β) (g : Thread W α → Thread U γ)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : ∀ x l, (f x).val l = label l (x.val l))
    (hgc : ∀ x l, (g x).val l = source l (x.val l))
    (Q : (l : ℕ) → ProbabilityMeasure (Z l))
    (hQ : ∀ l, (Q (l + 1) : Measure (Z (l + 1))).map (β l) = (Q l : Measure (Z l)))
    (A : (l : ℕ) → Set (W l)) (hA : ∀ l, A (l + 1) ⊆ (α l) ⁻¹' A l)
    (ρ : ProbabilityMeasure (Thread W α))
    (hne : ∀ l, ∃ θ : ProbabilityMeasure (W l),
      (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
      (θ : Measure (W l)).map (source l) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
      (θ : Measure (W l)) (A l) = 1) :
    letI : ∀ l, Fintype (W l) := fun l => Fintype.ofFinite (W l)
    ∃ Qinf : ProbabilityMeasure (Thread Z β),
      (∀ l, (Qinf : Measure (Thread Z β)).map (fun x => x.val l) = (Q l : Measure (Z l))) ∧
      let F (l : ℕ) : Set (ProbabilityMeasure (W l)) := {θ |
        (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
        (θ : Measure (W l)).map (source l) =
          ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
        (θ : Measure (W l)) (A l) = 1}
      let L : Set (ProbabilityMeasure (Thread W α)) := {θ |
        (θ : Measure (Thread W α)).map f = (Qinf : Measure (Thread Z β)) ∧
        (θ : Measure (Thread W α)).map g = (ρ : Measure (Thread W α)).map g ∧
        (θ : Measure (Thread W α)) (⋂ l, (fun x : Thread W α => x.val l) ⁻¹' A l) = 1}
      let H : Set ((l : ℕ) → ProbabilityMeasure (W l)) := {η |
        (∀ l, η l ∈ F l) ∧
        ∀ l, (η (l + 1) : Measure (W (l + 1))).map (α l) = (η l : Measure (W l))}
      let eventCost (l : ℕ) (θ : ProbabilityMeasure (W l)) : ℝ :=
        sSup (Set.range (fun E : {E : Set (W l) // MeasurableSet E} =>
          |((ρ : Measure (Thread W α)).map (fun x => x.val l)).real E.val -
            (θ : Measure (W l)).real E.val|))
      let completedEventCost (θ : ProbabilityMeasure (Thread W α)) : ℝ :=
        sSup (Set.range (fun E : {E : Set (Thread W α) // MeasurableSet E} =>
          |(ρ : Measure (Thread W α)).real E.val - (θ : Measure (Thread W α)).real E.val|))
      let commonCost (θ : ProbabilityMeasure (Thread W α)) : ℝ :=
        sSup (Set.range (fun E : {E : Set (Thread W α) //
            NullMeasurableSet E ((ρ : Measure (Thread W α)) + (θ : Measure (Thread W α)))} =>
          |((ρ : Measure (Thread W α)).completion E.val).toReal -
            ((θ : Measure (Thread W α)).completion E.val).toReal|))
      IsCompact L ∧
      (∀ l (θ : ProbabilityMeasure (W l)), eventCost l θ =
        (1 / 2 : ℝ) * ∑ w, |((ρ : Measure (Thread W α)).map (fun x => x.val l)).real {w} -
          (θ : Measure (W l)).real {w}|) ∧
      (∀ θ, completedEventCost θ = commonCost θ) ∧
      (LowerSemicontinuous completedEventCost ∧
        LowerSemicontinuous commonCost ∧
        LowerSemicontinuous (fun θ : L => completedEventCost θ.val) ∧
        LowerSemicontinuous (fun θ : L => commonCost θ.val)) ∧
      (∃ e : L ≃ₜ H,
        (∀ (θ : L) l, ((e θ).val l : Measure (W l)) =
          (θ.val : Measure (Thread W α)).map (fun x => x.val l)) ∧
        (∀ (θ η : L) (t : ℝ), 0 ≤ t → t ≤ 1 → ∃ ζ : L,
          (ζ.val : Measure (Thread W α)) = ENNReal.ofReal t • (θ.val : Measure (Thread W α)) +
            ENNReal.ofReal (1 - t) • (η.val : Measure (Thread W α)) ∧
          ∀ l, ((e ζ).val l : Measure (W l)) = ENNReal.ofReal t • ((e θ).val l : Measure (W l)) +
            ENNReal.ofReal (1 - t) • ((e η).val l : Measure (W l))) ∧
        ∀ (a b c : H) (t : ℝ), 0 ≤ t → t ≤ 1 →
          (∀ l, (c.val l : Measure (W l)) = ENNReal.ofReal t • (a.val l : Measure (W l)) +
            ENNReal.ofReal (1 - t) • (b.val l : Measure (W l))) →
          ((e.symm c).val : Measure (Thread W α)) =
            ENNReal.ofReal t • ((e.symm a).val : Measure (Thread W α)) +
            ENNReal.ofReal (1 - t) • ((e.symm b).val : Measure (Thread W α))) ∧
      ∃ d : ℕ → ℝ,
        (∀ l, ∃ θ ∈ F l, eventCost l θ = d l ∧ ∀ η ∈ F l, d l ≤ eventCost l η) ∧
        Monotone d ∧ (∀ l, 0 ≤ d l ∧ d l ≤ 1) ∧
        Tendsto d atTop (nhds (sSup (Set.range d))) ∧
        (∀ c : ℝ, 0 ≤ c →
          ((∃ θ ∈ L, completedEventCost θ ≤ c) ↔ ∀ l, ∃ θ ∈ F l, eventCost l θ ≤ c)) ∧
        ∃ θ ∈ L, completedEventCost θ = sSup (Set.range d) ∧
          (∀ η ∈ L, sSup (Set.range d) ≤ completedEventCost η) ∧
          (∀ η ∈ L, completedEventCost θ ≤ completedEventCost η) := by
  classical
  letI : ∀ l, Fintype (W l) := fun l => Fintype.ofFinite (W l)
  have hCompletedCompact {W Z U : ℕ → Type u}
      [∀ l, Finite (W l)] [∀ l, TopologicalSpace (W l)] [∀ l, DiscreteTopology (W l)]
      [∀ l, MeasurableSpace (W l)] [∀ l, BorelSpace (W l)]
      [∀ l, Finite (Z l)] [∀ l, TopologicalSpace (Z l)] [∀ l, DiscreteTopology (Z l)]
      [∀ l, MeasurableSpace (Z l)] [∀ l, BorelSpace (Z l)]
      [∀ l, Finite (U l)] [∀ l, TopologicalSpace (U l)] [∀ l, DiscreteTopology (U l)]
      [∀ l, MeasurableSpace (U l)] [∀ l, BorelSpace (U l)]
      (α : (l : ℕ) → W (l + 1) → W l)
      (label : (l : ℕ) → W l → Z l) (source : (l : ℕ) → W l → U l)
      (Q : (l : ℕ) → ProbabilityMeasure (Z l))
      (A : (l : ℕ) → Set (W l)) (ρ : ProbabilityMeasure (Thread W α)) :
      let L : Set (ProbabilityMeasure (Thread W α)) := {θ | ∀ l,
        ((θ : Measure (Thread W α)).map (fun x => x.val l)).map (label l) =
          (Q l : Measure (Z l)) ∧
        ((θ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) =
          ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
        ((θ : Measure (Thread W α)).map (fun x => x.val l)) (A l) = 1}
      IsClosed L ∧ IsCompact L := by
    classical
    have hc : IsClosed {x : (l : ℕ) → W l | ∀ l, α l (x (l + 1)) = x l} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun l => isClosed_eq
        ((continuous_of_discreteTopology (f := α l)).comp (continuous_apply (l + 1)))
        (continuous_apply l)
    haveI : ∀ l, MetrizableSpace (W l) := fun l => DiscreteTopology.metrizableSpace
    haveI : MetrizableSpace ((l : ℕ) → W l) := inferInstance
    haveI : SecondCountableTopology ((l : ℕ) → W l) := inferInstance
    haveI : BorelSpace ((l : ℕ) → W l) := inferInstance
    haveI : CompactSpace (Thread W α) := isCompact_iff_compactSpace.mp hc.isCompact
    haveI : MetrizableSpace (Thread W α) :=
      MetrizableSpace.subtype {x : (l : ℕ) → W l | ∀ l, α l (x (l + 1)) = x l}
    haveI : SecondCountableTopology (Thread W α) := inferInstance
    haveI : BorelSpace (Thread W α) := inferInstance
    have hπ (l : ℕ) : Continuous (fun x : Thread W α => x.val l) :=
      (continuous_apply l).comp continuous_subtype_val
    let π (l : ℕ) (θ : ProbabilityMeasure (Thread W α)) : ProbabilityMeasure (W l) :=
      θ.map (hπ l).measurable.aemeasurable
    let F (l : ℕ) : Set (ProbabilityMeasure (W l)) := {θ |
      (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
      (θ : Measure (W l)).map (source l) =
        ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
      (θ : Measure (W l)) (A l) = 1}
    have hFc (l : ℕ) : IsClosed (F l) := by
      have hmass (E : Set (W l)) :
          Continuous (fun θ : ProbabilityMeasure (W l) => (θ : Measure (W l)) E) := by
        let v : ContinuousMap (W l) ℝ≥0 := ⟨E.indicator (fun _ => 1), continuous_of_discreteTopology⟩
        simpa only [v, ContinuousMap.coe_mk, ENNReal.coe_indicator, ENNReal.coe_one,
          lintegral_indicator_const (Set.toFinite E).measurableSet, one_mul] using
          ProbabilityMeasure.continuous_lintegral_continuousMap v
      have hl : IsClosed {θ : ProbabilityMeasure (W l) |
          (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l))} := by
        have hh := isClosed_eq
          (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := label l)))
          (continuous_const (y := Q l))
        convert hh using 1
        ext θ
        exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
      let R : ProbabilityMeasure (U l) :=
        (π l ρ).map (measurable_of_countable (source l)).aemeasurable
      have hs : IsClosed {θ : ProbabilityMeasure (W l) |
          (θ : Measure (W l)).map (source l) = (R : Measure (U l))} := by
        have hh := isClosed_eq
          (ProbabilityMeasure.continuous_map (continuous_of_discreteTopology (f := source l)))
          (continuous_const (y := R))
        convert hh using 1
        ext θ
        exact ⟨fun h => Subtype.ext h, fun h => congrArg ProbabilityMeasure.toMeasure h⟩
      exact hl.inter (hs.inter (isClosed_eq (hmass (A l)) continuous_const))
    have hclosed : IsClosed {θ : ProbabilityMeasure (Thread W α) | ∀ l, π l θ ∈ F l} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun l => (hFc l).preimage (ProbabilityMeasure.continuous_map (hπ l))
    change IsClosed {θ : ProbabilityMeasure (Thread W α) | ∀ l, π l θ ∈ F l} ∧
      IsCompact {θ : ProbabilityMeasure (Thread W α) | ∀ l, π l θ ∈ F l}
    exact ⟨hclosed, hclosed.isCompact⟩

  have hHalfL1 {W : Type u} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]
      (μ ν : ProbabilityMeasure W) :
      measurableTotalVariation (μ : Measure W) (ν : Measure W) =
        ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i, |(μ : Measure W).real {i} - (ν : Measure W).real {i}|) ∧
      (measurableTotalVariation (μ : Measure W) (ν : Measure W)).toReal =
        (1 / 2 : ℝ) * ∑ i, |(μ : Measure W).real {i} - (ν : Measure W).real {i}| := by
    classical
    let p : W → ℝ := fun i => (μ : Measure W).real {i}
    let q : W → ℝ := fun i => (ν : Measure W).real {i}
    have hp (E : Finset W) : (∑ i ∈ E, p i) = (μ : Measure W).real E := by
      exact sum_measureReal_singleton (μ := (μ : Measure W)) E
    have hq (E : Finset W) : (∑ i ∈ E, q i) = (ν : Measure W).real E := by
      exact sum_measureReal_singleton (μ := (ν : Measure W)) E
    have hpn : (∑ i, p i) = 1 := by
      simpa only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one] using hp Finset.univ
    have hqn : (∑ i, q i) = 1 := by
      simpa only [Finset.coe_univ, measureReal_def, measure_univ, ENNReal.toReal_one] using hq Finset.univ
    have greatest := D5.S3.TotalVariation.Metric.total_variation_eq_sup_event_gap p q (hpn.trans hqn.symm)
    have gap (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
        max (a - b) (b - a) = ENNReal.ofReal |a.toReal - b.toReal| := by
      have h₁ : ENNReal.ofReal (a.toReal - b.toReal) = a - b := by
        rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha, ENNReal.ofReal_toReal hb]
      have h₂ : ENNReal.ofReal (b.toReal - a.toReal) = b - a := by
        rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb, ENNReal.ofReal_toReal ha]
      rw [← h₁, ← h₂]
      by_cases h : b.toReal ≤ a.toReal
      · rw [abs_of_nonneg (sub_nonneg.mpr h), ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h), max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (a.toReal - b.toReal) from bot_le)]
      · have hh : a.toReal < b.toReal := lt_of_not_ge h
        rw [abs_of_neg (sub_neg.mpr hh), ENNReal.ofReal_of_nonpos (le_of_lt (sub_neg.mpr hh)), max_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (b.toReal - a.toReal) from bot_le)]
        congr 1
        ring
    have heq : measurableTotalVariation (μ : Measure W) (ν : Measure W) =
        ENNReal.ofReal (D5.S3.TotalVariation.Pinsker.totalVariation p q) := by
      apply le_antisymm
      · unfold measurableTotalVariation
        refine iSup_le fun E => ?_
        rw [gap _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
        apply ENNReal.ofReal_le_ofReal
        have hbound := greatest.2 (Set.mem_range_self E.val.toFinset)
        have hE : (E.val.toFinset : Set W) = E.val := Set.coe_toFinset E.val
        simpa only [hp, hq, hE, measureReal_def] using hbound
      · obtain ⟨E, hE⟩ := greatest.1
        have hEm : MeasurableSet (E : Set W) := (Set.toFinite _).measurableSet
        have hv : max ((μ : Measure W) E - (ν : Measure W) E)
            ((ν : Measure W) E - (μ : Measure W) E) =
            ENNReal.ofReal (D5.S3.TotalVariation.Pinsker.totalVariation p q) := by
          rw [gap _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
          change ENNReal.ofReal |(μ : Measure W).real E - (ν : Measure W).real E| = _
          rw [← hp E, ← hq E]
          exact congrArg ENNReal.ofReal hE
        rw [← hv]
        exact le_iSup (fun e : {E : Set W // MeasurableSet E} =>
          max ((μ : Measure W) e.val - (ν : Measure W) e.val)
            ((ν : Measure W) e.val - (μ : Measure W) e.val)) ⟨E, hEm⟩
    constructor
    · exact heq
    · rw [heq, ENNReal.toReal_ofReal (D5.S3.TotalVariation.Metric.total_variation_nonneg p q)]
      rfl

  have hTVBound {X : Type u} [MeasurableSpace X] (P R : ProbabilityMeasure X) :
      measurableTotalVariation (P : Measure X) (R : Measure X) ≤ 1 := by
    unfold measurableTotalVariation
    exact iSup_le fun _ => max_le (tsub_le_self.trans prob_le_one)
      (tsub_le_self.trans prob_le_one)
  have hTVFinite {X : Type u} [MeasurableSpace X] (P R : ProbabilityMeasure X) :
      measurableTotalVariation (P : Measure X) (R : Measure X) ≠ ⊤ :=
    ne_of_lt ((hTVBound P R).trans_lt (by simp))
  have hRealRadius {x : ℝ≥0∞} (hx : x ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
      x.toReal ≤ c ↔ x ≤ ENNReal.ofReal c := by
    constructor
    · intro h
      rw [← ENNReal.ofReal_toReal hx]
      exact ENNReal.ofReal_le_ofReal h
    · intro h
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      simpa only [ENNReal.toReal_ofReal hc] using hh
  have hUnique {B : ℕ → Type u} [∀ l, Finite (B l)]
      [∀ l, MeasurableSpace (B l)] [∀ l, MeasurableSingletonClass (B l)]
      (q : (l : ℕ) → B (l + 1) → B l)
      (M N : ProbabilityMeasure (Thread B q))
      (hm : ∀ l, (M : Measure (Thread B q)).map (fun x => x.val l) =
        (N : Measure (Thread B q)).map (fun x => x.val l)) : M = N := by
    have hz : measurableTotalVariation (M : Measure (Thread B q)) (N : Measure (Thread B q)) = 0 := by
      rw [thread_tv_eq_iSup q]
      simp only [hm, measurableTotalVariation, tsub_self, max_self, iSup_const]
    apply Subtype.ext
    apply Measure.ext
    intro E hE
    have hgap := le_iSup (fun e : {E : Set (Thread B q) // MeasurableSet E} =>
      max ((M : Measure (Thread B q)) e.val - (N : Measure (Thread B q)) e.val)
        ((N : Measure (Thread B q)) e.val - (M : Measure (Thread B q)) e.val)) ⟨E, hE⟩
    change max ((M : Measure (Thread B q)) E - (N : Measure (Thread B q)) E)
      ((N : Measure (Thread B q)) E - (M : Measure (Thread B q)) E) ≤
        measurableTotalVariation (M : Measure (Thread B q)) (N : Measure (Thread B q)) at hgap
    rw [hz] at hgap
    exact le_antisymm
      (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_left _ _).trans hgap) bot_le))
      (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_right _ _).trans hgap) bot_le))
  obtain ⟨Qinf, hQinf, hQu⟩ := D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension.exists_unique_extension β Q hQ
  refine ⟨Qinf, hQinf, ?_⟩
  dsimp only
  have hπ (l : ℕ) : Measurable (fun x : Thread W α => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hpZ (l : ℕ) : Measurable (fun x : Thread Z β => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  have hpU (l : ℕ) : Measurable (fun x : Thread U γ => x.val l) :=
    (measurable_pi_apply l).comp measurable_subtype_coe
  let π (l : ℕ) (θ : ProbabilityMeasure (Thread W α)) : ProbabilityMeasure (W l) :=
    θ.map (hπ l).aemeasurable
  let F (l : ℕ) : Set (ProbabilityMeasure (W l)) := {θ |
    (θ : Measure (W l)).map (label l) = (Q l : Measure (Z l)) ∧
    (θ : Measure (W l)).map (source l) =
      ((ρ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) ∧
    (θ : Measure (W l)) (A l) = 1}
  let L : Set (ProbabilityMeasure (Thread W α)) := {θ |
    (θ : Measure (Thread W α)).map f = (Qinf : Measure (Thread Z β)) ∧
    (θ : Measure (Thread W α)).map g = (ρ : Measure (Thread W α)).map g ∧
    (θ : Measure (Thread W α)) (⋂ l, (fun x : Thread W α => x.val l) ⁻¹' A l) = 1}
  let costE (l : ℕ) (θ : ProbabilityMeasure (W l)) :=
    measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l)) (θ : Measure (W l))
  let cost (l : ℕ) (θ : ProbabilityMeasure (W l)) : ℝ := (costE l θ).toReal
  let completedCost (θ : ProbabilityMeasure (Thread W α)) : ℝ :=
    (measurableTotalVariation (ρ : Measure (Thread W α)) (θ : Measure (Thread W α))).toReal
  have lf (l : ℕ) : (fun x : Thread Z β => x.val l) ∘ f =
      label l ∘ (fun x : Thread W α => x.val l) := funext fun x => hfc x l
  have sg (l : ℕ) : (fun x : Thread U γ => x.val l) ∘ g =
      source l ∘ (fun x : Thread W α => x.val l) := funext fun x => hgc x l
  have hFeas (θ : ProbabilityMeasure (Thread W α)) : θ ∈ L ↔ ∀ l, π l θ ∈ F l := by
    have hsupp : (θ : Measure (Thread W α)) (⋂ l, (fun x : Thread W α => x.val l) ⁻¹' A l) = 1 ↔
        ∀ l, ((θ : Measure (Thread W α)).map (fun x => x.val l)) (A l) = 1 := by
      have hAm (l : ℕ) : MeasurableSet (A l) := (Set.toFinite _).measurableSet
      rw [← mem_ae_iff_prob_eq_one (MeasurableSet.iInter fun l => hπ l (hAm l))]
      change (∀ᵐ x ∂(θ : Measure _), x ∈ ⋂ l, (fun x : Thread W α => x.val l) ⁻¹' A l) ↔ _
      simp only [Set.mem_iInter, Set.mem_preimage]
      rw [ae_all_iff]
      apply forall_congr'
      intro l
      rw [Measure.map_apply (hπ l) (hAm l), ← mem_ae_iff_prob_eq_one (hπ l (hAm l))]
      rfl
    constructor
    · intro hθ l
      change ((θ : Measure (Thread W α)).map (fun x => x.val l)).map (label l) = _ ∧
        ((θ : Measure (Thread W α)).map (fun x => x.val l)).map (source l) = _ ∧
        ((θ : Measure (Thread W α)).map (fun x => x.val l)) (A l) = 1
      refine ⟨?_, ?_, hsupp.mp hθ.2.2 l⟩
      · rw [Measure.map_map (measurable_of_countable (label l)) (hπ l), ← lf l,
          ← Measure.map_map (hpZ l) hf, hθ.1, hQinf l]
      · rw [Measure.map_map (measurable_of_countable (source l)) (hπ l), ← sg l,
          ← Measure.map_map (hpU l) hg, hθ.2.1,
          Measure.map_map (hpU l) hg, sg l,
          ← Measure.map_map (measurable_of_countable (source l)) (hπ l)]
    · intro hθ
      refine ⟨?_, ?_, hsupp.mpr (fun l => (hθ l).2.2)⟩
      · have hm : ∀ l, ((θ : Measure (Thread W α)).map f).map (fun x : Thread Z β => x.val l) =
            (Q l : Measure (Z l)) := by
          intro l
          rw [Measure.map_map (hpZ l) hf, lf l,
            ← Measure.map_map (measurable_of_countable (label l)) (hπ l)]
          exact (hθ l).1
        exact congrArg ProbabilityMeasure.toMeasure (hQu (θ.map hf.aemeasurable) hm)
      · have hm : ∀ l, ((θ : Measure (Thread W α)).map g).map (fun x : Thread U γ => x.val l) =
            ((ρ : Measure (Thread W α)).map g).map (fun x : Thread U γ => x.val l) := by
          intro l
          rw [Measure.map_map (hpU l) hg, Measure.map_map (hpU l) hg, sg l,
            ← Measure.map_map (measurable_of_countable (source l)) (hπ l),
            ← Measure.map_map (measurable_of_countable (source l)) (hπ l)]
          exact (hθ l).2.1
        exact congrArg ProbabilityMeasure.toMeasure
          (hUnique γ (θ.map hg.aemeasurable) (ρ.map hg.aemeasurable) hm)
  have hProjectCost (l : ℕ) (θ : ProbabilityMeasure (Thread W α)) :
      cost l (π l θ) ≤ completedCost θ := by
    exact ENNReal.toReal_mono (hTVFinite ρ θ)
      (measurable_total_variation_map_le (ρ : Measure (Thread W α))
        (θ : Measure (Thread W α)) (fun x => x.val l) (hπ l))
  have hRadius (c : ℝ) (hc : 0 ≤ c) :
      (∃ θ ∈ L, completedCost θ ≤ c) ↔ ∀ l, ∃ θ ∈ F l, cost l θ ≤ c := by
    constructor
    · rintro ⟨θ, hθ, hd⟩ l
      exact ⟨π l θ, (hFeas θ).mp hθ l, (hProjectCost l θ).trans hd⟩
    · intro hlevel
      have hlevelE : ∀ l, ∃ θ ∈ F l, costE l θ ≤ ENNReal.ofReal c := by
        intro l
        obtain ⟨θ, hθ, hd⟩ := hlevel l
        exact ⟨θ, hθ, (hRealRadius (hTVFinite (π l ρ) θ) hc).mp hd⟩
      obtain ⟨θl, hθl, hcompatible⟩ :=
        select_common_radius α β γ label source hlabel hsource Q hQ A hA ρ (ENNReal.ofReal c) hlevelE
      obtain ⟨θ, hθ, _⟩ := D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension.exists_unique_extension α θl hcompatible
      have hθF : θ ∈ L := (hFeas θ).mpr (by
        intro l
        have hsame : π l θ = θl l := Subtype.ext (hθ l)
        rw [hsame]
        exact (hθl l).1)
      have hθcost : measurableTotalVariation (ρ : Measure (Thread W α))
          (θ : Measure (Thread W α)) ≤ ENNReal.ofReal c := by
        rw [thread_tv_eq_iSup α]
        refine iSup_le fun l => ?_
        rw [hθ l]
        exact (hθl l).2
      exact ⟨θ, hθF, (hRealRadius (hTVFinite ρ θ) hc).mpr hθcost⟩
  have hMinExists (l : ℕ) : ∃ θ ∈ F l, ∀ η ∈ F l, costE l θ ≤ costE l η := by
    obtain ⟨_, _, _, θ, hθ, hmin⟩ :=
      finite_feasible_minimum (label l) (source l) (Q l) (π l ρ) (A l) (hne l)
    exact ⟨θ, hθ, hmin⟩
  choose M hMF hMin using hMinExists
  let d (l : ℕ) : ℝ := cost l (M l)
  have hRealMin (l : ℕ) (η : ProbabilityMeasure (W l)) (hη : η ∈ F l) : d l ≤ cost l η :=
    ENNReal.toReal_mono (hTVFinite (π l ρ) η) (hMin l η hη)
  have hdBounds (l : ℕ) : 0 ≤ d l ∧ d l ≤ 1 := by
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hh := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) (hTVBound (π l ρ) (M l))
    simpa only [ENNReal.toReal_one, d, cost, costE, π, ProbabilityMeasure.toMeasure_map] using hh
  let p (l : ℕ) (θ : ProbabilityMeasure (W (l + 1))) : ProbabilityMeasure (W l) :=
    θ.map (measurable_of_countable (α l)).aemeasurable
  have hPres (l : ℕ) (θ : ProbabilityMeasure (W (l + 1))) (ht : θ ∈ F (l + 1)) : p l θ ∈ F l :=
    finite_feasible_pushforward α β γ label source hlabel hsource Q hQ A hA ρ l θ ht
  have hContract (l : ℕ) (θ : ProbabilityMeasure (W (l + 1))) :
      cost l (p l θ) ≤ cost (l + 1) θ := by
    apply ENNReal.toReal_mono (hTVFinite (π (l + 1) ρ) θ)
    have hρ : ((ρ : Measure (Thread W α)).map (fun x => x.val (l + 1))).map (α l) =
        (ρ : Measure (Thread W α)).map (fun x => x.val l) := by
      rw [Measure.map_map (measurable_of_countable (α l)) (hπ (l + 1))]
      congr 1
      funext x
      exact x.property l
    change measurableTotalVariation ((ρ : Measure (Thread W α)).map (fun x => x.val l))
      ((θ : Measure (W (l + 1))).map (α l)) ≤ _
    rw [← hρ]
    exact measurable_total_variation_map_le _ _ (α l) (measurable_of_countable (α l))
  have hdMono : Monotone d := monotone_nat_of_le_succ fun l =>
    (hRealMin l (p l (M (l + 1))) (hPres l (M (l + 1)) (hMF (l + 1)))).trans
      (hContract l (M (l + 1)))
  have hbdd : BddAbove (Set.range d) := ⟨1, by
    rintro _ ⟨l, rfl⟩
    exact (hdBounds l).2⟩
  let c : ℝ := sSup (Set.range d)
  have hdLe (l : ℕ) : d l ≤ c := le_csSup hbdd (Set.mem_range_self l)
  have hc : 0 ≤ c := (hdBounds 0).1.trans (hdLe 0)
  have hLower (η : ProbabilityMeasure (Thread W α)) (hη : η ∈ L) : c ≤ completedCost η := by
    apply csSup_le (Set.range_nonempty d)
    rintro _ ⟨l, rfl⟩
    exact (hRealMin l (π l η) ((hFeas η).mp hη l)).trans (hProjectCost l η)
  obtain ⟨θ, hθ, hθUpper⟩ := (hRadius c hc).mpr (fun l => ⟨M l, hMF l, hdLe l⟩)
  have hθeq : completedCost θ = c := le_antisymm hθUpper (hLower θ hθ)
  have hdTendsto : Tendsto d atTop (nhds c) := by
    change Tendsto d atTop (nhds (⨆ l, d l))
    exact tendsto_atTop_ciSup hdMono hbdd
  have hResult : ∃ d : ℕ → ℝ,
      (∀ l, ∃ θ ∈ F l, cost l θ = d l ∧ ∀ η ∈ F l, d l ≤ cost l η) ∧
      Monotone d ∧ (∀ l, 0 ≤ d l ∧ d l ≤ 1) ∧
      Tendsto d atTop (nhds (sSup (Set.range d))) ∧
      (∀ c : ℝ, 0 ≤ c → ((∃ θ ∈ L, completedCost θ ≤ c) ↔ ∀ l, ∃ θ ∈ F l, cost l θ ≤ c)) ∧
      ∃ θ ∈ L, completedCost θ = sSup (Set.range d) ∧
        (∀ η ∈ L, sSup (Set.range d) ≤ completedCost η) ∧
        (∀ η ∈ L, completedCost θ ≤ completedCost η) := by
    refine ⟨d, ?_, hdMono, hdBounds, hdTendsto, hRadius, θ, hθ, hθeq, hLower, ?_⟩
    · intro l
      exact ⟨M l, hMF l, rfl, hRealMin l⟩
    · intro η hη
      rw [hθeq]
      exact hLower η hη
  let eventCost (l : ℕ) (θ : ProbabilityMeasure (W l)) : ℝ :=
    sSup (Set.range (fun E : {E : Set (W l) // MeasurableSet E} =>
      |((ρ : Measure (Thread W α)).map (fun x => x.val l)).real E.val -
        (θ : Measure (W l)).real E.val|))
  let completedEventCost (θ : ProbabilityMeasure (Thread W α)) : ℝ :=
    sSup (Set.range (fun E : {E : Set (Thread W α) // MeasurableSet E} =>
      |(ρ : Measure (Thread W α)).real E.val - (θ : Measure (Thread W α)).real E.val|))
  let commonCost (θ : ProbabilityMeasure (Thread W α)) : ℝ :=
    sSup (Set.range (fun E : {E : Set (Thread W α) //
        NullMeasurableSet E ((ρ : Measure (Thread W α)) + (θ : Measure (Thread W α)))} =>
      |((ρ : Measure (Thread W α)).completion E.val).toReal -
        ((θ : Measure (Thread W α)).completion E.val).toReal|))
  have hFiniteNorm (l : ℕ) (θ : ProbabilityMeasure (W l)) : cost l θ = eventCost l θ :=
    (event_tv_normalization (π l ρ) θ).1
  have hCompletedNorm (θ : ProbabilityMeasure (Thread W α)) : completedCost θ = completedEventCost θ :=
    (event_tv_normalization ρ θ).1
  have hCommon (θ : ProbabilityMeasure (Thread W α)) : completedEventCost θ = commonCost θ :=
    (event_tv_normalization ρ θ).2.symm
  have hHalf (l : ℕ) (θ : ProbabilityMeasure (W l)) : eventCost l θ =
      (1 / 2 : ℝ) * ∑ w, |((ρ : Measure (Thread W α)).map (fun x => x.val l)).real {w} -
        (θ : Measure (W l)).real {w}| :=
    (hFiniteNorm l θ).symm.trans (hHalfL1 (π l ρ) θ).2
  have hLdef : L = {θ : ProbabilityMeasure (Thread W α) | ∀ l, π l θ ∈ F l} := by
    ext θ
    exact hFeas θ
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hCompletedCompact α label source Q A ρ).2
  let H : Set ((l : ℕ) → ProbabilityMeasure (W l)) := {η |
    (∀ l, η l ∈ F l) ∧
    ∀ l, (η (l + 1) : Measure (W (l + 1))).map (α l) = (η l : Measure (W l))}
  let Ψ : L → H := fun θ => ⟨fun l => π l θ.val, (hFeas θ.val).mp θ.property, by
    intro l
    change ((θ.val : Measure (Thread W α)).map (fun x => x.val (l + 1))).map (α l) =
      (θ.val : Measure (Thread W α)).map (fun x => x.val l)
    rw [Measure.map_map (measurable_of_countable (α l)) (hπ (l + 1))]
    congr 1
    funext x
    exact x.property l⟩
  haveI : ∀ l, MetrizableSpace (W l) := fun l => DiscreteTopology.metrizableSpace
  haveI : MetrizableSpace ((l : ℕ) → W l) := inferInstance
  haveI : SecondCountableTopology ((l : ℕ) → W l) := inferInstance
  haveI : BorelSpace ((l : ℕ) → W l) := inferInstance
  haveI : BorelSpace (Thread W α) := inferInstance
  have hπcontinuous (l : ℕ) : Continuous (fun x : Thread W α => x.val l) :=
    (continuous_apply l).comp continuous_subtype_val
  have hC38FiniteContinuous (l : ℕ) :
      Continuous (fun η : ProbabilityMeasure (W l) => cost l η) := by
    have hF := finite_feasible_minimum (W := W l) (Z := W l) (U := W l)
      id id (π l ρ) (π l ρ) Set.univ ⟨π l ρ, by simp⟩
    have hE : Continuous (fun η : ProbabilityMeasure (W l) =>
        measurableTotalVariation ((π l ρ : ProbabilityMeasure (W l)) : Measure (W l))
          (η : Measure (W l))) := hF.2.2.1
    apply continuous_iff_continuousAt.mpr
    intro η
    exact (ENNReal.continuousAt_toReal (hTVFinite (π l ρ) η)).comp
      (f := fun η : ProbabilityMeasure (W l) =>
        measurableTotalVariation (π l ρ : Measure (W l)) (η : Measure (W l)))
      (x := η) hE.continuousAt
  have hC38Sup (θ : ProbabilityMeasure (Thread W α)) :
      completedCost θ = ⨆ l, cost l (π l θ) := by
    change (measurableTotalVariation (ρ : Measure (Thread W α))
      (θ : Measure (Thread W α))).toReal = _
    rw [thread_tv_eq_iSup α]
    exact ENNReal.toReal_iSup (fun l => hTVFinite (π l ρ) (π l θ))
  have hC38Bdd (θ : ProbabilityMeasure (Thread W α)) :
      BddAbove (Set.range (fun l => cost l (π l θ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨l, rfl⟩
    have h := ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤)
      (hTVBound (π l ρ) (π l θ))
    simpa only [cost, costE, π, ProbabilityMeasure.toMeasure_map, ENNReal.toReal_one] using h
  have hC38Completed : LowerSemicontinuous completedCost := by
    have hSupLSC : LowerSemicontinuous
        (fun θ : ProbabilityMeasure (Thread W α) => ⨆ l, cost l (π l θ)) :=
      lowerSemicontinuous_ciSup hC38Bdd (fun l =>
        ((hC38FiniteContinuous l).comp
          (ProbabilityMeasure.continuous_map (hπcontinuous l))).lowerSemicontinuous)
    have hEq : completedCost =
        (fun θ : ProbabilityMeasure (Thread W α) => ⨆ l, cost l (π l θ)) := funext hC38Sup
    rw [hEq]
    exact hSupLSC
  have hC38Event : LowerSemicontinuous completedEventCost := by
    have hEq : completedCost = completedEventCost := funext hCompletedNorm
    exact hEq ▸ hC38Completed
  have hC38Completion : LowerSemicontinuous commonCost := by
    have hEq : completedEventCost = commonCost := funext hCommon
    exact hEq ▸ hC38Event
  have hC38 : LowerSemicontinuous completedEventCost ∧
      LowerSemicontinuous commonCost ∧
      LowerSemicontinuous (fun θ : L => completedEventCost θ.val) ∧
      LowerSemicontinuous (fun θ : L => commonCost θ.val) :=
    ⟨hC38Event, hC38Completion,
      hC38Event.comp continuous_subtype_val, hC38Completion.comp continuous_subtype_val⟩
  have hΨcontinuous : Continuous Ψ := by
    exact (continuous_pi fun l =>
      (ProbabilityMeasure.continuous_map (hπcontinuous l)).comp continuous_subtype_val).subtype_mk _
  have hΨinjective : Injective Ψ := by
    intro θ η h
    apply Subtype.ext
    apply hUnique α θ.val η.val
    intro l
    exact congrArg (fun z : H => (z.val l : Measure (W l))) h
  have hΨsurjective : Surjective Ψ := by
    intro η
    obtain ⟨θ, hθ, _⟩ := D5.S3.Estimation.DataProcessing.FiniteTowerProbabilityExtension.exists_unique_extension α η.val η.property.2
    have hθF : θ ∈ L := (hFeas θ).mpr (by
      intro l
      have hsame : π l θ = η.val l := Subtype.ext (hθ l)
      rw [hsame]
      exact η.property.1 l)
    refine ⟨⟨θ, hθF⟩, ?_⟩
    apply Subtype.ext
    funext l
    exact Subtype.ext (hθ l)
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  haveI : T2Space H := inferInstance
  let e : L ≃ H := Equiv.ofBijective Ψ ⟨hΨinjective, hΨsurjective⟩
  let E : L ≃ₜ H := Continuous.homeoOfEquivCompactToT2 (f := e) hΨcontinuous
  have hProjection (θ : L) (l : ℕ) : ((E θ).val l : Measure (W l)) =
      (θ.val : Measure (Thread W α)).map (fun x => x.val l) := rfl
  have hAffine (θ η : L) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ∃ ζ : L,
      (ζ.val : Measure (Thread W α)) = ENNReal.ofReal t • (θ.val : Measure (Thread W α)) +
        ENNReal.ofReal (1 - t) • (η.val : Measure (Thread W α)) ∧
      ∀ l, ((E ζ).val l : Measure (W l)) = ENNReal.ofReal t • ((E θ).val l : Measure (W l)) +
        ENNReal.ofReal (1 - t) • ((E η).val l : Measure (W l)) := by
    have ha : ENNReal.ofReal t ≤ 1 := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht1
    have hsub : ENNReal.ofReal (1 - t) = 1 - ENNReal.ofReal t := by
      rw [ENNReal.ofReal_sub _ ht0, ENNReal.ofReal_one]
    let M : Measure (Thread W α) := ENNReal.ofReal t • (θ.val : Measure (Thread W α)) +
      (1 - ENNReal.ofReal t) • (η.val : Measure (Thread W α))
    obtain ⟨hprob, hlabelM, hsourceM, hlegalM⟩ :=
      feasible_mixture f g hf hg Qinf (ρ.map hg.aemeasurable)
        (⋂ l, (fun x : Thread W α => x.val l) ⁻¹' A l)
        θ.val η.val θ.property η.property (ENNReal.ofReal t) ha
    let ζ : L := ⟨⟨M, hprob⟩, hlabelM, hsourceM, hlegalM⟩
    refine ⟨ζ, ?_, ?_⟩
    · rw [hsub]
      rfl
    · intro l
      simp only [hProjection, hsub]
      change M.map (fun x => x.val l) = _
      unfold M
      rw [Measure.map_add _ _ (hπ l), Measure.map_smul, Measure.map_smul]
  have hAffineInverse (a b c : H) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (hmix : ∀ l, (c.val l : Measure (W l)) = ENNReal.ofReal t • (a.val l : Measure (W l)) +
        ENNReal.ofReal (1 - t) • (b.val l : Measure (W l))) :
      ((E.symm c).val : Measure (Thread W α)) =
        ENNReal.ofReal t • ((E.symm a).val : Measure (Thread W α)) +
        ENNReal.ofReal (1 - t) • ((E.symm b).val : Measure (Thread W α)) := by
    obtain ⟨ζ, hζ, hcoords⟩ := hAffine (E.symm a) (E.symm b) t ht0 ht1
    have hEζ : E ζ = c := by
      apply Subtype.ext
      funext l
      apply Subtype.ext
      have hh : ((E ζ).val l : Measure (W l)) =
          ENNReal.ofReal t • (a.val l : Measure (W l)) +
            ENNReal.ofReal (1 - t) • (b.val l : Measure (W l)) := by
        simpa only [E.apply_symm_apply] using hcoords l
      exact hh.trans (hmix l).symm
    have hback : ζ = E.symm c := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact hEζ
    rw [← hback]
    exact hζ
  refine ⟨hLc, hHalf, hCommon, hC38, ⟨E, hProjection, hAffine, hAffineInverse⟩, ?_⟩
  simpa only [hFiniteNorm, hCompletedNorm] using hResult

end D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum

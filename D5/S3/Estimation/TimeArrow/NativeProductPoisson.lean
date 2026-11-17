/- GID: D5/S3/Estimation/TimeArrow/NativeProductPoisson
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeProductPoisson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual native full marked-count vector admits a quantitative product Poisson bound. -/

import D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
import D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
import D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison

/-! Exact identification of the finite native reference law and its Poisson composition. -/

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Classical
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
open D5.S3.Estimation.TimeArrow.CategoricalProductPoisson
open D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison

set_option autoImplicit false
noncomputable section
namespace D5.S3.Estimation.TimeArrow.NativeProductPoisson

private def symbolWeight {J : Type*} [Fintype J] (a : J → ℝ≥0) : Option J → ℝ≥0
  | none => Real.toNNReal (1 - ∑ j, (a j : ℝ))
  | some j => a j

private def symbolLaw {J : Type*} [Fintype J] [MeasurableSpace (Option J)]
    (a : J → ℝ≥0) : Measure (Option J) :=
  ∑ o, (symbolWeight a o : ℝ≥0∞) • Measure.dirac o

private theorem reference_measure {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℝ≥0) (ha : ∑ j, (a j : ℝ) ≤ 1) (s : ℕ) (E : Set (J → ℕ)) :
    (independentSumLaw (categoricalIncrement a) s).real E =
      ∑ o : Fin s → Option J, if referenceCounts o ∈ E then
        ∏ t, (symbolWeight a (o t) : ℝ) else 0 := by
  letI : MeasurableSpace (Option J) := ⊤
  letI : MeasurableSingletonClass (Option J) := ⟨fun _ => trivial⟩
  let f : Option J → J → ℕ := fun o j => incrementExponent o j
  have hf : Measurable f := measurable_of_countable _
  have hmap : (symbolLaw a).map f = categoricalIncrement a := by
    rw [symbolLaw, Measure.map_finset_sum hf.aemeasurable]
    simp only [Measure.map_smul _ hf.aemeasurable, Measure.map_dirac' hf,
      Fintype.sum_option]
    have hs (j : J) : f (some j) = unitMark j := by
      exact Finsupp.single_eq_pi_single j 1
    simp_rw [hs]
    rfl
  haveI : IsFiniteMeasure (symbolLaw a) := by
    dsimp [symbolLaw]
    infer_instance
  have hi := Measure.pi_map_pi (μ := fun _ : Fin s => symbolLaw a)
    (f := fun _ => f) (fun _ => hf.aemeasurable)
  simp_rw [hmap] at hi
  have hcounts : aggregateCounts s ∘ (fun o : Fin s → Option J => fun t => f (o t)) =
      referenceCounts := by
    funext o j
    simp [aggregateCounts, referenceCounts, f]
  rw [independentSumLaw, ← hi, Measure.map_map (by fun_prop) (by fun_prop), hcounts]
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _) E.to_countable.measurableSet]
  rw [← (Measure.pi (fun _ : Fin s => symbolLaw a)).sum_smul_dirac]
  simp only [Measure.sum_apply _ (measurable_of_countable _ E.to_countable.measurableSet),
    Measure.smul_apply, smul_eq_mul, tsum_fintype, Measure.pi_singleton]
  have hw (o : Option J) : symbolLaw a {o} = (symbolWeight a o : ℝ≥0∞) := by
    simp only [symbolLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton o), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply]
    simp
  simp_rw [hw]
  rw [ENNReal.toReal_sum (fun o _ => by
    by_cases ho : referenceCounts o ∈ E
    · simp [Set.indicator_apply, ho, ENNReal.prod_ne_top]
    · simp [Set.indicator_apply, ho])]
  apply sum_congr rfl
  intro o _
  by_cases ho : referenceCounts o ∈ E
  · simp [ho, Set.indicator_apply, ENNReal.toReal_prod]
  · simp [ho, Set.indicator_apply]

/-- One-step rates for both signs of every support row. -/
def signalRates {q : ℕ} (M : ℕ) (r : ℝ) : (Fin q ⊕ Fin q) → ℝ≥0
  | .inl _ => Real.toNNReal (ap M r)
  | .inr _ => Real.toNNReal (am M r)

/-- Every full joint native count event is within 9 s (q/(2M))² of the
complete independent product Poisson law at the actual signal rates. -/
theorem native_product_poisson {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (hm : Function.Injective m) (hmS : ∀ j, m j ∈ S.val)
    (E : Set ((Fin q ⊕ Fin q) → ℕ)) :
    |(∑ o : Obs M s .path, if nativeCounts m o ∈ E then probability r .path S o else 0) -
      (poissonProduct (fun j : Fin q ⊕ Fin q => (s : ℝ≥0) * signalRates M r j)).real E| ≤
      9 * (s : ℝ) * (rho M q)^2 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hp : 0 ≤ ap M r := by unfold ap; positivity
  have hn : 0 ≤ am M r := by unfold am; positivity
  have hs : (∑ j : Fin q ⊕ Fin q, (signalRates M r j : ℝ)) = rho M q := by
    simp only [Fintype.sum_sum_type, signalRates, Real.coe_toNNReal _ hp,
      Real.coe_toNNReal _ hn, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold ap am rho
    field_simp
    <;> ring
  have hρ : rho M q ≤ 1 := by
    rw [rho, div_le_iff₀ (by positivity)]
    have hqM : (q : ℝ) < M := by exact_mod_cast hqm
    linarith
  have ha : (∑ j : Fin q ⊕ Fin q, (signalRates M r j : ℝ)) ≤ 1 := hs.le.trans hρ
  have hw (o : Option (Fin q ⊕ Fin q)) :
      (symbolWeight (signalRates M r) o : ℝ) = referenceIncrement M q r o := by
    cases o with
    | none =>
        change (Real.toNNReal (1 - ∑ j : Fin q ⊕ Fin q, (signalRates M r j : ℝ)) : ℝ) = _
        rw [Real.coe_toNNReal _ (sub_nonneg.mpr ha), hs]
        rfl
    | some j =>
        cases j with
        | inl j => exact Real.coe_toNNReal _ hp
        | inr j => exact Real.coe_toNNReal _ hn
  have href := reference_measure (signalRates M r) ha s E
  simp_rw [hw] at href
  change (independentSumLaw (categoricalIncrement (signalRates M r)) s).real E =
    (∑ o : Fin s → Option (Fin q ⊕ Fin q),
      if referenceCounts o ∈ E then referenceWeight M r o else 0) at href
  have hb := categorical_product_poisson (signalRates M r) ha s E
  rw [hs, href] at hb
  have hnative := native_joint_count_comparison (s := s) hq hqm hr hr1 hc1 S m hm hmS E
  calc
    _ ≤ |(∑ o : Obs M s .path, if nativeCounts m o ∈ E then probability r .path S o else 0) -
          (∑ o : Fin s → Option (Fin q ⊕ Fin q),
            if referenceCounts o ∈ E then referenceWeight M r o else 0)| +
        |(∑ o : Fin s → Option (Fin q ⊕ Fin q),
            if referenceCounts o ∈ E then referenceWeight M r o else 0) -
          (poissonProduct (fun j : Fin q ⊕ Fin q => (s : ℝ≥0) * signalRates M r j)).real E| :=
      abs_sub_le _ _ _
    _ ≤ 8 * (s : ℝ) * (rho M q)^2 + (s : ℝ) * (rho M q)^2 :=
      add_le_add hnative (by simpa only [poissonProduct] using hb)
    _ = 9 * (s : ℝ) * (rho M q)^2 := by ring

end D5.S3.Estimation.TimeArrow.NativeProductPoisson

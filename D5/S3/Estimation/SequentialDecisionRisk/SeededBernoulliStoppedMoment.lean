/- GID: D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent seeded Bernoulli prefix laws and stopped moment transfer. -/

import D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment

variable {Seed : Type*} [MeasurableSpace Seed]

local notation "Ber" => fun p : unitInterval => bernoulliMeasure true false p
local notation "Law" => fun (ν : Measure Seed) (p : unitInterval) =>
  ν.prod (Measure.infinitePi (fun _ : ℕ => Ber p))
local notation "Past" => fun (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  (ω.1, (range n).restrict ω.2)
local notation "Ratio" => fun (p₀ p : unitInterval) (b : Bool) =>
  if b then (p : ℝ) / (p₀ : ℝ) else (1 - (p : ℝ)) / (1 - (p₀ : ℝ))
local notation "Like" => fun (p₀ p : unitInterval) (n : ℕ) (ω : Seed × (ℕ → Bool)) =>
  ∏ i ∈ range n, Ratio p₀ p (ω.2 i)

/-- The private seed is visible initially; the first `n` acquired source bits
are visible at time `n`. -/
def seededFiltration : Filtration ℕ (inferInstance : MeasurableSpace (Seed × (ℕ → Bool))) where
  seq n := MeasurableSpace.comap (Past n) inferInstance
  mono' i j hij := by
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (h := fun z : Seed × ((k : range j) → Bool) =>
        (z.1, fun k : range i => z.2 ⟨k.1, mem_range.mpr ((mem_range.mp k.2).trans_le hij)⟩))
    · fun_prop
    · rfl
  le' n := (by fun_prop : Measurable (Past n)).comap_le

private lemma ratio_nonneg (p₀ p : unitInterval) (b : Bool) : 0 ≤ Ratio p₀ p b := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact div_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr p₀.2.2)
  · exact div_nonneg p.2.1 p₀.2.1

private lemma ratio_mass (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (b : Bool) :
    ENNReal.ofReal (Ratio p₀ p b) * Ber p₀ {b} = Ber p {b} := by
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,
    bernoulliMeasure_apply, measurableSet_singleton, Set.mem_singleton_iff,
    Bool.true_eq_false, Bool.false_eq_true,
    ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  · change ENNReal.ofReal ((1 - (p : ℝ)) / (1 - (p₀ : ℝ))) *
      ENNReal.ofReal (1 - (p₀ : ℝ)) = ENNReal.ofReal (1 - (p : ℝ))
    rw [← ENNReal.ofReal_mul (div_nonneg (sub_nonneg.mpr p.2.2)
      (sub_nonneg.mpr p₀.2.2)), div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr h₁))]
  · rw [← ENNReal.ofReal_mul (div_nonneg p.2.1 p₀.2.1), div_mul_cancel₀ _ (ne_of_gt h₀)]

private lemma finite_prefix_density (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (n : ℕ) :
    (Measure.pi (fun _ : range n => Ber p₀)).withDensity
      (fun x => ENNReal.ofReal (∏ i : range n, Ratio p₀ p (x i))) =
    Measure.pi (fun _ : range n => Ber p) := by
  apply Measure.ext_of_singleton
  intro x
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
    Measure.pi_singleton, Measure.pi_singleton,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => ratio_nonneg p₀ p (x i)),
    ← prod_mul_distrib]
  exact prod_congr rfl (fun i _ => ratio_mass p₀ p h₀ h₁ (x i))

omit [MeasurableSpace Seed] in
private lemma like_nonneg (p₀ p : unitInterval) (n : ℕ)
    (ω : Seed × (ℕ → Bool)) : 0 ≤ Like p₀ p n ω :=
  prod_nonneg (fun i _ => ratio_nonneg p₀ p (ω.2 i))

private lemma like_adapted (p₀ p : unitInterval) :
    StronglyAdapted (seededFiltration (Seed := Seed)) (Like p₀ p) := by
  intro n
  have hpast : Measurable[seededFiltration n] (Past n : Seed × (ℕ → Bool) → _) :=
    comap_measurable _
  have hfactor : Measurable (fun z : Seed × ((i : range n) → Bool) =>
      ∏ i : range n, Ratio p₀ p (z.2 i)) := by
    apply Finset.measurable_prod
    intro i _
    exact (Measurable.of_discrete : Measurable (Ratio p₀ p)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have heq : Like p₀ p n = (fun z : Seed × ((i : range n) → Bool) =>
      ∏ i : range n, Ratio p₀ p (z.2 i)) ∘ Past n := by
    funext ω
    exact (prod_coe_sort (range n) (fun i => Ratio p₀ p (ω.2 i))).symm
  rw [heq]
  exact (hfactor.comp hpast).stronglyMeasurable

private lemma prefix_law (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p : unitInterval) (n : ℕ) :
    (Law ν p).map (Past n) = ν.prod (Measure.pi (fun _ : range n => Ber p)) := by
  change (ν.prod (Measure.infinitePi (fun _ : ℕ => Ber p))).map
    (Prod.map id (range n).restrict) = _
  rw [← Measure.map_prod_map ν _ measurable_id (by fun_prop), Measure.map_id,
    Measure.infinitePi_map_restrict]

private lemma map_density_pullback {α γ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] (μ : Measure α) (f : α → γ) (hf : Measurable f)
    (d : γ → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity (d ∘ f)).map f = (μ.map f).withDensity d := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, ← lintegral_indicator (hf hs),
    ← lintegral_indicator hs, lintegral_map (hd.indicator hs) hf]
  rfl

private lemma prefix_density_law (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) (n : ℕ) :
    ((Law ν p₀).withDensity (fun ω => ENNReal.ofReal (Like p₀ p n ω))).map (Past n) =
      (Law ν p).map (Past n) := by
  let d := fun z : Seed × ((i : range n) → Bool) =>
    ENNReal.ofReal (∏ i : range n, Ratio p₀ p (z.2 i))
  have hd : Measurable d := by
    apply Measurable.ennreal_ofReal
    apply Finset.measurable_prod
    intro i _
    exact (Measurable.of_discrete : Measurable (Ratio p₀ p)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have heq : (fun ω => ENNReal.ofReal (Like p₀ p n ω)) = d ∘ Past n := by
    funext ω
    congr 1
    exact (prod_coe_sort (range n) (fun i => Ratio p₀ p (ω.2 i))).symm
  rw [heq, map_density_pullback _ _ (by fun_prop) _ hd, prefix_law, prefix_law]
  calc
    _ = ν.prod ((Measure.pi (fun _ : range n => Ber p₀)).withDensity
        (fun x => ENNReal.ofReal (∏ i : range n, Ratio p₀ p (x i)))) :=
      (prod_withDensity_right (μ := ν) (ν := Measure.pi (fun _ : range n => Ber p₀))
        (g := fun x => ENNReal.ofReal (∏ i : range n, Ratio p₀ p (x i)))
        (by fun_prop)).symm
    _ = _ := congrArg (fun μ => ν.prod μ) (finite_prefix_density p₀ p h₀ h₁ n)

private lemma density_on_past (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) (n : ℕ)
    {s : Set (Seed × (ℕ → Bool))} (hs : MeasurableSet[seededFiltration n] s) :
    (Law ν p₀).withDensity (fun ω => ENNReal.ofReal (Like p₀ p n ω)) s = Law ν p s := by
  obtain ⟨t, ht, rfl⟩ := hs
  have h := congrArg (fun μ : Measure (Seed × ((i : range n) → Bool)) => μ t)
    (prefix_density_law ν p₀ p h₀ h₁ n)
  simpa only [Measure.map_apply (by fun_prop : Measurable (Past n)) ht] using h

private lemma like_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (n : ℕ) : Integrable (Like p₀ p n) (Law ν p₀) := by
  let R := max ((p : ℝ) / (p₀ : ℝ)) ((1 - (p : ℝ)) / (1 - (p₀ : ℝ)))
  have hR : 0 ≤ R := (div_nonneg p.2.1 p₀.2.1).trans (le_max_left _ _)
  refine ⟨((like_adapted p₀ p n).mono (seededFiltration.le n)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := R ^ n) (ae_of_all _ (fun ω => ?_))⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (like_nonneg p₀ p n ω)]
  calc
    _ ≤ ∏ _i ∈ range n, R := by
      apply prod_le_prod (fun i _ => ratio_nonneg p₀ p (ω.2 i))
      intro i _
      cases ω.2 i <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact le_max_right _ _
      · exact le_max_left _ _
    _ = R ^ n := by simp

private lemma setIntegral_like (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) (n : ℕ)
    {s : Set (Seed × (ℕ → Bool))} (hs : MeasurableSet[seededFiltration n] s) :
    (∫ ω in s, Like p₀ p n ω ∂Law ν p₀) = (Law ν p).real s := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun ω => like_nonneg p₀ p n ω))
    ((like_integrable ν p₀ p n).aestronglyMeasurable.restrict)]
  rw [← withDensity_apply _ (seededFiltration.le n _ hs),
    density_on_past ν p₀ p h₀ h₁ n hs]
  rfl

private lemma likelihood_martingale (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) :
    Martingale (Like p₀ p) seededFiltration (Law ν p₀) := by
  apply martingale_of_setIntegral_eq_succ (like_adapted p₀ p) (like_integrable ν p₀ p)
  intro i s hs
  rw [setIntegral_like ν p₀ p h₀ h₁ i hs,
    setIntegral_like ν p₀ p h₀ h₁ (i + 1) (seededFiltration.mono (Nat.le_succ i) _ hs)]

private lemma stopping_nat_measurable {τ : Seed × (ℕ → Bool) → ℕ}
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ))) : Measurable τ := by
  simpa using (hτ.measurable.mono hτ.measurableSpace_le le_rfl).untopD 0

private lemma stopped_law_map (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ))) :
    ((Law ν p₀).withDensity (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω))).map τ =
      (Law ν p).map τ := by
  apply Measure.ext_of_singleton
  intro k
  have hmeas := stopping_nat_measurable hτ
  have hk : MeasurableSet[seededFiltration k]
      {ω | (τ ω : WithTop ℕ) = (k : WithTop ℕ)} := hτ.measurableSet_eq k
  have heq : {ω : Seed × (ℕ → Bool) | (τ ω : WithTop ℕ) = k} = τ ⁻¹' {k} := by
    ext ω
    simp
  rw [heq] at hk
  rw [Measure.map_apply hmeas (measurableSet_singleton k),
    Measure.map_apply hmeas (measurableSet_singleton k),
    withDensity_apply _ (hmeas (measurableSet_singleton k))]
  calc
    _ = ∫⁻ ω in τ ⁻¹' {k}, ENNReal.ofReal (Like p₀ p k ω) ∂Law ν p₀ := by
      apply setLIntegral_congr_fun (hmeas (measurableSet_singleton k))
      intro ω hω
      change ENNReal.ofReal (Like p₀ p (τ ω) ω) = ENNReal.ofReal (Like p₀ p k ω)
      rw [show τ ω = k from hω]
    _ = _ := by
      rw [← withDensity_apply _ (hmeas (measurableSet_singleton k))]
      exact density_on_past ν p₀ p h₀ h₁ k hk

private lemma stopped_moment_identity (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ))) (m : ℕ) :
    (∫ ω, (τ ω : ℝ) ^ m ∂Law ν p) =
      ∫ ω, (τ ω : ℝ) ^ m ∂(Law ν p₀).withDensity
        (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω)) := by
  have hmeas := stopping_nat_measurable hτ
  have hmap := stopped_law_map ν p₀ p h₀ h₁ τ hτ
  have hm : StronglyMeasurable (fun k : ℕ => (k : ℝ) ^ m) := by fun_prop
  rw [← integral_map hmeas.aemeasurable hm.aestronglyMeasurable,
    ← integral_map hmeas.aemeasurable hm.aestronglyMeasurable, hmap]

omit [MeasurableSpace Seed] in
private lemma likelihood_step (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (i : ℕ) (ω : Seed × (ℕ → Bool)) :
    Like p₀ p (i + 1) ω - Like p₀ p i ω =
      ((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) *
        Like p₀ p i ω * ((if ω.2 i then (1 : ℝ) else 0) - (p₀ : ℝ)) := by
  simp only [prod_range_succ]
  cases ω.2 i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp [ne_of_gt h₀, ne_of_gt (sub_pos.mpr h₁)] <;> ring

/-- A parameter-independent stopping rule on an iid Bernoulli stream and an
independent arbitrary private seed has its parameter-`p` stopped moment
bounded by twice its endpoint moment in the local likelihood window. -/
theorem bernoulli_stopped_moment_bound (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m)
    (hwindow : |((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
      Real.sqrt (n : ℝ) ≤
      (2 * (((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m *
        (2 : ℝ) ^ (2 * m)) + 1)⁻¹) :
    ((∫ ω, (τ ω : ℝ) ^ m ∂Law ν p) =
      ∫ ω, (τ ω : ℝ) ^ m ∂(Law ν p₀).withDensity
        (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω))) ∧
    ((∫ ω, (τ ω : ℝ) ^ m ∂Law ν p) ≤
      2 * ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p₀) := by
  have hidentity := stopped_moment_identity ν p₀ p h₀ h₁ τ hτ m
  refine ⟨hidentity, ?_⟩
  rw [hidentity]
  apply (StoppedLikelihoodAbsorption.stopped_likelihood_bounds
    (likelihood_martingale ν p₀ p h₀ h₁)
    (fun i ω => (if ω.2 i then (1 : ℝ) else 0) - (p₀ : ℝ)) τ hτ
    (((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))) n
    (fun ω => by simp) hτn
    (fun i ω => ?_) (fun ω => like_nonneg p₀ p (τ ω) ω)
    (likelihood_step p₀ p h₀ h₁) hm hwindow).2
  cases ω.2 i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [zero_sub, abs_neg, abs_of_nonneg p₀.2.1]
    exact p₀.2.2
  · rw [abs_of_nonneg (sub_nonneg.mpr p₀.2.2)]
    linarith [p₀.2.1]

end D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment

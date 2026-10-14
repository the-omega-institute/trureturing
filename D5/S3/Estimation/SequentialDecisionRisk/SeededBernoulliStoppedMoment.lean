/- GID: D5/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/SeededBernoulliStoppedMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seeded Bernoulli stopped laws and common endpoint moment budgets. -/

import D5.S3.Estimation.SequentialDecisionRisk.StoppedLikelihoodAbsorption
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

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
  simpa only [Function.comp_apply, Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs] using (setLIntegral_map (μ := μ) hs hd hf).symm

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

local notation "RatioBound" => fun p₀ : unitInterval =>
  max (1 : ℝ) (max (1 / (p₀ : ℝ)) (1 / (1 - (p₀ : ℝ))))

omit [MeasurableSpace Seed] in
private lemma like_uniform_bound (p₀ p : unitInterval) (i : ℕ)
    (ω : Seed × (ℕ → Bool)) : Like p₀ p i ω ≤ RatioBound p₀ ^ i := by
  calc
    _ ≤ ∏ _k ∈ range i, RatioBound p₀ := by
      apply Finset.prod_le_prod₀ (fun k _ => ratio_nonneg p₀ p (ω.2 k))
      intro k _
      cases ω.2 k <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (div_le_div_of_nonneg_right (by linarith [p.2.1])
          (sub_nonneg.mpr p₀.2.2)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
      · exact (div_le_div_of_nonneg_right p.2.2 p₀.2.1).trans
          ((le_max_left _ _).trans (le_max_right _ _))
    _ = _ := by simp


private lemma like_integrable (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (n : ℕ) : Integrable (Like p₀ p n) (Law ν p₀) := by
  refine ⟨((like_adapted p₀ p n).mono (seededFiltration.le n)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := RatioBound p₀ ^ n) (ae_of_all _ (fun ω => ?_))⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (like_nonneg p₀ p n ω)]
  exact like_uniform_bound p₀ p n ω

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

private lemma stopped_event_density (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (s : Set (Seed × (ℕ → Bool))) (hs : MeasurableSet[hτ.measurableSpace] s) :
    (Law ν p₀).withDensity (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω)) s =
      Law ν p s := by
  let E := fun k : ℕ => s ∩ {ω | τ ω = k}
  have hE : ∀ k, MeasurableSet[seededFiltration k] (E k) := by
    intro k
    simpa [E] using
      (hτ.measurableSet_inter_eq_iff s k).mp
        (hs.inter (hτ.measurableSet_eq' k))
  have hu : s = ⋃ k, E k := by ext ω; simp [E]
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    exact hij (hωi.2.symm.trans hωj.2)
  rw [hu, measure_iUnion hd (fun k => seededFiltration.le k _ (hE k)),
    measure_iUnion hd (fun k => seededFiltration.le k _ (hE k))]
  apply tsum_congr
  intro k
  rw [withDensity_apply _ (seededFiltration.le k _ (hE k))]
  calc
    _ = ∫⁻ ω in E k, ENNReal.ofReal (Like p₀ p k ω) ∂Law ν p₀ := by
      apply setLIntegral_congr_fun (seededFiltration.le k _ (hE k))
      intro ω hω
      change ENNReal.ofReal (Like p₀ p (τ ω) ω) = ENNReal.ofReal (Like p₀ p k ω)
      rw [hω.2]
    _ = _ := by
      rw [← withDensity_apply _ (seededFiltration.le k _ (hE k))]
      exact density_on_past ν p₀ p h₀ h₁ k (hE k)

/-- Changing the Bernoulli parameter changes every stopped observation by
its stopped likelihood. This identifies only the stopped sigma algebra. -/
theorem bernoulli_stopped_output_identity (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (f : Seed × (ℕ → Bool) → ℝ) (hf : StronglyMeasurable[hτ.measurableSpace] f) :
    (∫ ω, f ω ∂Law ν p) = ∫ ω, f ω ∂(Law ν p₀).withDensity
      (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω)) := by
  have ht : ((Law ν p₀).withDensity
      (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω))).trim hτ.measurableSpace_le =
      (Law ν p).trim hτ.measurableSpace_le := by
    refine @Measure.ext _ hτ.measurableSpace _ _ ?_
    intro s hs
    rw [trim_measurableSet_eq _ hs, trim_measurableSet_eq _ hs]
    exact stopped_event_density ν p₀ p h₀ h₁ τ hτ s hs
  rw [integral_trim hτ.measurableSpace_le hf,
    integral_trim hτ.measurableSpace_le hf, ht]

private lemma stopped_statistic_identity (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ))) (F : ℕ → ℝ) :
    (∫ ω, F (τ ω) ∂Law ν p) = ∫ ω, F (τ ω) ∂(Law ν p₀).withDensity
      (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω)) := by
  apply bernoulli_stopped_output_identity ν p₀ p h₀ h₁ τ hτ
  apply Measurable.stronglyMeasurable
  exact (measurable_from_nat (f := F)).comp (by simpa using hτ.measurable.untopD 0)


private lemma stopped_moment_identity (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ))) (m : ℕ) :
    (∫ ω, (τ ω : ℝ) ^ m ∂Law ν p) =
      ∫ ω, (τ ω : ℝ) ^ m ∂(Law ν p₀).withDensity
        (fun ω => ENNReal.ofReal (Like p₀ p (τ ω) ω)) := by
  exact stopped_statistic_identity ν p₀ p h₀ h₁ τ hτ (fun k => (k : ℝ) ^ m)

omit [MeasurableSpace Seed] in
private lemma likelihood_step (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ))
    (h₁ : (p₀ : ℝ) < 1) (i : ℕ) (ω : Seed × (ℕ → Bool)) :
    Like p₀ p (i + 1) ω - Like p₀ p i ω =
      ((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) *
        Like p₀ p i ω * ((if ω.2 i then (1 : ℝ) else 0) - (p₀ : ℝ)) := by
  simp only [prod_range_succ]
  cases ω.2 i <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals field_simp [ne_of_gt h₀, ne_of_gt (sub_pos.mpr h₁)] <;> ring

local notation "MomentC" => fun m : ℕ =>
  (((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m * (2 : ℝ) ^ (2 * m))
local notation "Bit" => fun (p : unitInterval) (i : ℕ) (ω : Seed × (ℕ → Bool)) =>
  (if ω.2 i then (1 : ℝ) else 0) - (p : ℝ)

omit [MeasurableSpace Seed] in
lemma centered_bit_bound (p : unitInterval) (i : ℕ) (ω : Seed × (ℕ → Bool)) :
    |Bit p i ω| ≤ 1 := by
  cases hb : ω.2 i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte]
  · rw [zero_sub, abs_neg, abs_of_nonneg p.2.1]; exact p.2.2
  · rw [abs_of_nonneg (sub_nonneg.mpr p.2.2)]; linarith [p.2.1]

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
  exact centered_bit_bound p₀ i ω

local notation "Weight" => fun (a : ℝ) (m j : ℕ) => ((2 : ℝ) ^ (a - (m : ℝ))) ^ j
local notation "GeoBudget" => fun (a : ℝ) (m : ℕ) =>
  (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) + (1 - (2 : ℝ) ^ (a - (m : ℝ)))⁻¹

omit [MeasurableSpace Seed] in
private lemma dyadic_truncation_kernel (a : ℝ) (m : ℕ) (ha : 0 < a)
    (ham : a < (m : ℝ)) (t K : ℕ) :
    (∑ j ∈ range K, Weight a m j * ((min t (2 ^ j) : ℕ) : ℝ) ^ m) ≤
      GeoBudget a m * (t : ℝ) ^ a := by
  have hm : m ≠ 0 := by intro h; simp only [h, Nat.cast_zero] at ham; linarith
  by_cases ht : t = 0
  · subst t
    simp [zero_pow hm, Real.zero_rpow ha.ne']
  let r : ℝ := (2 : ℝ) ^ a
  let q : ℝ := (2 : ℝ) ^ (a - (m : ℝ))
  let k := Nat.log 2 t
  let N := max K (k + 1)
  let f : ℕ → ℝ := fun j => q ^ j * ((min t (2 ^ j) : ℕ) : ℝ) ^ m
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) ha
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht
  have hf0 : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity
  have hqr : q * (2 : ℝ) ^ m = r := by
    dsimp [q, r]
    rw [Real.rpow_sub_natCast (by norm_num), div_mul_cancel₀ _ (by positivity)]
  have hlowterm : ∀ j, f j ≤ r ^ j := by
    intro j
    calc
      _ ≤ q ^ j * ((2 : ℝ) ^ j) ^ m := by
        dsimp [f]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0.le j)
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast min_le_right t (2 ^ j)
      _ = r ^ j := by rw [← pow_mul, Nat.mul_comm j m, pow_mul, ← mul_pow, hqr]
  have hrk : r ^ k = ((2 : ℝ) ^ k) ^ a := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num), mul_comm a,
      Real.rpow_natCast_mul (by norm_num)]
  have hrk_le : r ^ k ≤ (t : ℝ) ^ a := by
    rw [hrk]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 ht) ha.le
  have hlo : (∑ j ∈ range (k + 1), f j) ≤ (t : ℝ) ^ a * (r / (r - 1)) := by
    calc
      _ ≤ ∑ j ∈ range (k + 1), r ^ j := sum_le_sum (fun j _ => hlowterm j)
      _ = (r ^ (k + 1) - 1) / (r - 1) := geom_sum_eq (ne_of_gt hr) _
      _ ≤ r ^ k * (r / (r - 1)) := by
        rw [pow_succ, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hrk_le (div_nonneg (by linarith) (by linarith))
  have hqk : q ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ (a - (m : ℝ)) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast (by norm_num), mul_comm (a - (m : ℝ)),
      Real.rpow_natCast_mul (by norm_num)]
  have htailcoefficient : (t : ℝ) ^ m * q ^ (k + 1) ≤ (t : ℝ) ^ a := by
    rw [hqk]
    calc
      _ ≤ (t : ℝ) ^ m * (t : ℝ) ^ (a - (m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_nonpos ht0 _ (by linarith)
        exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t).le
      _ = (t : ℝ) ^ a := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]
        congr 1
        ring
  have hhi : (∑ j ∈ Ico (k + 1) N, f j) ≤ (t : ℝ) ^ a / (1 - q) := by
    calc
      _ ≤ ∑ j ∈ Ico (k + 1) N, (t : ℝ) ^ m * q ^ j := by
        apply sum_le_sum
        intro j _
        dsimp [f]
        rw [mul_comm ((t : ℝ) ^ m)]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0.le j)
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast min_le_left t (2 ^ j)
      _ = (t : ℝ) ^ m * ∑ j ∈ Ico (k + 1) N, q ^ j := by rw [mul_sum]
      _ ≤ (t : ℝ) ^ m * (q ^ (k + 1) / (1 - q)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0.le hq1) (by positivity)
      _ = ((t : ℝ) ^ m * q ^ (k + 1)) / (1 - q) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right htailcoefficient (by linarith)
  have hsum : (∑ j ∈ range K, f j) ≤ ∑ j ∈ range N, f j :=
    sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left K (k + 1)))
      (fun j _ _ => hf0 j)
  rw [← sum_range_add_sum_Ico f (le_max_right K (k + 1))] at hsum
  have h := hsum.trans (add_le_add hlo hhi)
  change (∑ j ∈ range K, f j) ≤ (r / (r - 1) + (1 - q)⁻¹) * (t : ℝ) ^ a
  calc
    _ ≤ (t : ℝ) ^ a * (r / (r - 1)) + (t : ℝ) ^ a / (1 - q) := h
    _ = _ := by ring

local notation "Trunc" => fun (t : WithTop ℕ) (n : ℕ) => (min t (n : WithTop ℕ)).untopD 0
local notation "EndpointCost" => fun (a : ℝ) (t : WithTop ℕ) =>
  if t = ⊤ then (⊤ : ℝ≥0∞) else ENNReal.ofReal (((t.untopD 0 : ℕ) : ℝ) ^ a)

omit [MeasurableSpace Seed] in
lemma truncation_cast (M : Seed × (ℕ → Bool) → WithTop ℕ) (n : ℕ)
    (ω : Seed × (ℕ → Bool)) :
    (Trunc (M ω) n : WithTop ℕ) = min (M ω) (n : WithTop ℕ) := by
  cases M ω with
  | top => simp
  | coe t => rfl

lemma truncation_stopping {M : Seed × (ℕ → Bool) → WithTop ℕ}
    (hM : IsStoppingTime seededFiltration M) (n : ℕ) :
    IsStoppingTime seededFiltration (fun ω => (Trunc (M ω) n : WithTop ℕ)) := by
  rw [show (fun ω => (Trunc (M ω) n : WithTop ℕ)) =
    (fun ω => min (M ω) (n : WithTop ℕ)) from funext (truncation_cast M n)]
  exact hM.min_const n

lemma truncation_le (t : WithTop ℕ) (n : ℕ) : Trunc t n ≤ n := by
  cases t with
  | top => simp
  | coe t =>
    change min t n ≤ n
    exact min_le_right t n

lemma truncated_moment_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : Ω → WithTop ℕ) (hM : Measurable M)
    (n m : ℕ) : Integrable (fun ω => (Trunc (M ω) n : ℝ) ^ m) μ := by
  have ht : Measurable (fun ω => Trunc (M ω) n) := (hM.min measurable_const).untopD 0
  have hf : Measurable (fun ω => (Trunc (M ω) n : ℝ) ^ m) :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht).pow_const m
  refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (C := (n : ℝ) ^ m) (ae_of_all _ (fun ω => ?_))⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast truncation_le (M ω) n

lemma truncation_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → WithTop ℕ) (hM : Measurable M) (n m : ℕ) :
    ENNReal.ofReal ((n : ℝ) ^ m) * μ {ω | (n : WithTop ℕ) < M ω} ≤
      ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ m) ∂μ := by
  have ht : Measurable (fun ω => Trunc (M ω) n) := (hM.min measurable_const).untopD 0
  have hf : Measurable (fun ω => ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ m)) :=
    (((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht).pow_const m).ennreal_ofReal
  have hsub : {ω | (n : WithTop ℕ) < M ω} ⊆
      {ω | ENNReal.ofReal ((n : ℝ) ^ m) ≤
        ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ m)} := by
    intro ω hω
    change ENNReal.ofReal ((n : ℝ) ^ m) ≤
      ENNReal.ofReal ((((min (M ω) (n : WithTop ℕ)).untopD 0 : ℕ) : ℝ) ^ m)
    rw [min_eq_right hω.le]
    simp
  calc
    _ ≤ ENNReal.ofReal ((n : ℝ) ^ m) * μ
        {ω | ENNReal.ofReal ((n : ℝ) ^ m) ≤
          ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ m)} := by
      gcongr
    _ ≤ _ := mul_meas_ge_le_lintegral (μ := μ) hf (ENNReal.ofReal ((n : ℝ) ^ m))

lemma endpoint_budget_finite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → WithTop ℕ) (hM : Measurable M) (a : ℝ) (m : ℕ)
    (ha : 0 < a) (ham : a < (m : ℝ)) (K : ℕ) :
    (∑ j ∈ range K, ENNReal.ofReal (Weight a m j) *
      ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂μ) ≤
    ENNReal.ofReal (GeoBudget a m) * ∫⁻ ω, EndpointCost a (M ω) ∂μ := by
  have htrunc : ∀ j, Measurable (fun ω =>
      ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m)) := by
    intro j
    have ht : Measurable (fun ω => Trunc (M ω) (2 ^ j)) :=
      (hM.min measurable_const).untopD 0
    exact (((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht).pow_const m).ennreal_ofReal
  have hG : 0 < GeoBudget a m := by
    have hr := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) ha
    have hq := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (show a - (m : ℝ) < 0 by linarith)
    positivity
  simp_rw [← lintegral_const_mul _ (htrunc _)]
  rw [← lintegral_finsetSum _ (fun j _ => (htrunc j).const_mul _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ω
  cases hMt : M ω with
  | top =>
    change _ ≤ ENNReal.ofReal (GeoBudget a m) *
      (if M ω = ⊤ then ⊤ else ENNReal.ofReal ((((M ω).untopD 0 : ℕ) : ℝ) ^ a))
    rw [hMt, if_pos rfl]
    rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hG))]
    exact le_top
  | coe t =>
    simp only [hMt, WithTop.untopD_coe, WithTop.coe_ne_top,
      if_false]
    have hw : ∀ j, 0 ≤ Weight a m j := fun j =>
      pow_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) j
    simp_rw [← ENNReal.ofReal_mul (hw _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity),
      ← ENNReal.ofReal_mul hG.le]
    exact ENNReal.ofReal_le_ofReal (dyadic_truncation_kernel a m ha ham t K)

lemma stopped_like_measurable (p₀ p : unitInterval)
    (τ : Seed × (ℕ → Bool) → ℕ) (hτ : Measurable τ) :
    Measurable (fun ω => Like p₀ p (τ ω) ω) := by
  have hjoint : Measurable (fun z : ℕ × (Seed × (ℕ → Bool)) => Like p₀ p z.1 z.2) :=
    measurable_from_prod_countable_right
      (fun i => ((like_adapted p₀ p i).mono (seededFiltration.le i)).measurable)
  exact hjoint.comp (hτ.prodMk measurable_id)

private lemma stopped_statistic_continuous (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) (F : ℕ → ℝ) :
    Continuous (fun p : unitInterval => ∫ ω, F (τ ω) ∂Law ν p) := by
  have ht := stopping_nat_measurable hτ
  have hL : ∀ p : unitInterval, Measurable (fun ω => Like p₀ p (τ ω) ω) :=
    fun p => stopped_like_measurable p₀ p τ ht
  have hF : Measurable (fun ω => F (τ ω)) := (measurable_from_nat (f := F)).comp ht
  let R : ℝ := ∑ k ∈ range (n + 1), |F k|
  have hFb : ∀ ω, |F (τ ω)| ≤ R := fun ω =>
    single_le_sum (fun k _ => abs_nonneg (F k)) (mem_range.mpr (Nat.lt_succ_of_le (hτn ω)))
  have hRb : 1 ≤ RatioBound p₀ := le_max_left _ _
  have hbound : ∀ (p : unitInterval) ω,
      ‖Like p₀ p (τ ω) ω * F (τ ω)‖ ≤ RatioBound p₀ ^ n * R := by
    intro p ω
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (like_nonneg p₀ p (τ ω) ω),
      Real.norm_eq_abs]
    exact mul_le_mul ((like_uniform_bound p₀ p (τ ω) ω).trans
      (pow_le_pow_right₀ hRb (hτn ω))) (hFb ω) (abs_nonneg _) (by positivity)
  have hcont : ∀ ω, Continuous (fun p : unitInterval => Like p₀ p (τ ω) ω * F (τ ω)) := by
    intro ω
    apply Continuous.mul _ continuous_const
    apply continuous_finsetProd
    intro k _
    cases ω.2 k <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hc : Continuous (fun p : unitInterval =>
      ∫ ω, Like p₀ p (τ ω) ω * F (τ ω) ∂Law ν p₀) :=
    continuous_of_dominated (fun p => ((hL p).mul hF).aestronglyMeasurable)
      (fun p => ae_of_all _ (hbound p)) (integrable_const _) (ae_of_all _ hcont)
  have hid : ∀ p : unitInterval, (∫ ω, F (τ ω) ∂Law ν p) =
      ∫ ω, Like p₀ p (τ ω) ω * F (τ ω) ∂Law ν p₀ := by
    intro p
    rw [stopped_statistic_identity ν p₀ p h₀ h₁ τ hτ F,
      integral_withDensity_eq_integral_toReal_smul ((hL p).ennreal_ofReal)
        (ae_of_all _ (fun ω => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (like_nonneg p₀ p _ _), smul_eq_mul]
  exact hc.congr (fun p => (hid p).symm)

private lemma endpoint_cost_limit (a : ℝ) (ha : 0 < a) (t : WithTop ℕ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((Trunc t n : ℝ) ^ a)) atTop
      (𝓝 (EndpointCost a t)) := by
  cases t with
  | top =>
    change Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ a)) atTop (𝓝 ⊤)
    simpa only [Function.comp_def] using ENNReal.tendsto_ofReal_atTop.comp
      ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  | coe t =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop t] with n hn
    simp only [WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
    change ENNReal.ofReal ((t : ℝ) ^ a) = ENNReal.ofReal (((min t n : ℕ) : ℝ) ^ a)
    rw [min_eq_left hn]

private lemma endpoint_from_uniform_cost (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (M : Seed × (ℕ → Bool) → WithTop ℕ) (hM : IsStoppingTime seededFiltration M)
    (a : ℝ) (ha : 0 < a) (p : ℕ → unitInterval) (hp : Tendsto p atTop (𝓝 p₀))
    (K : ℝ≥0∞) (hK : ∀ j, (∫⁻ ω, EndpointCost a (M ω) ∂Law ν (p j)) ≤ K) :
    (∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀) ≤ K := by
  have hmeas := hM.measurable.mono hM.measurableSpace_le le_rfl
  have htrunc : ∀ n, Measurable (fun ω => ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a)) := by
    intro n
    have ht : Measurable (fun ω => Trunc (M ω) n) := (hmeas.min measurable_const).untopD 0
    exact (((Real.continuous_rpow_const ha.le).measurable.comp
      ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht))).ennreal_ofReal
  have htruncint : ∀ (p : unitInterval) n,
      Integrable (fun ω => (Trunc (M ω) n : ℝ) ^ a) (Law ν p) := by
    intro p n
    have ht : Measurable (fun ω => Trunc (M ω) n) := (hmeas.min measurable_const).untopD 0
    have hf : Measurable (fun ω => (Trunc (M ω) n : ℝ) ^ a) :=
      (Real.continuous_rpow_const ha.le).measurable.comp
        ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp ht)
    refine ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (C := (n : ℝ) ^ a) (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    apply Real.rpow_le_rpow (by positivity) _ ha.le
    exact_mod_cast truncation_le (M ω) n
  have hpath : ∀ n ω,
      ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ≤ EndpointCost a (M ω) := by
    intro n ω
    cases hMt : M ω with
    | top => simp
    | coe t =>
      simp only [WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ ha.le
      exact_mod_cast min_le_left t n
  have hfinite : ∀ n, (∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ∂Law ν p₀) ≤ K := by
    intro n
    have hc := (stopped_statistic_continuous ν p₀ h₀ h₁
      (fun ω => Trunc (M ω) n) (truncation_stopping hM n) n
      (fun ω => truncation_le (M ω) n) (fun k => (k : ℝ) ^ a)).tendsto p₀
    have ht : Tendsto (fun j => ∫⁻ ω,
        ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ∂Law ν (p j)) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ∂Law ν p₀)) := by
      have hi : ∀ q : unitInterval,
          ENNReal.ofReal (∫ ω, (Trunc (M ω) n : ℝ) ^ a ∂Law ν q) =
            ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ∂Law ν q :=
        fun q => ofReal_integral_eq_lintegral_ofReal (htruncint q n)
          (ae_of_all _ (fun ω => Real.rpow_nonneg (by positivity) _))
      simpa only [Function.comp_def, hi]
        using (ENNReal.continuous_ofReal.tendsto
          (∫ ω, (Trunc (M ω) n : ℝ) ^ a ∂Law ν p₀)).comp (hc.comp hp)
    exact le_of_tendsto' ht (fun j => (lintegral_mono (hpath n)).trans (hK j))
  have hlim : Tendsto (fun n => ∫⁻ ω,
      ENNReal.ofReal ((Trunc (M ω) n : ℝ) ^ a) ∂Law ν p₀) atTop
      (𝓝 (∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (htrunc n).aemeasurable)
    · apply ae_of_all
      intro ω n k hnk
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (by positivity) _ ha.le
      cases M ω with
      | top => simpa using (show (n : ℝ) ≤ k by exact_mod_cast hnk)
      | coe t => exact_mod_cast min_le_min_left t hnk
    · exact ae_of_all _ (fun ω => endpoint_cost_limit a ha (M ω))
  exact le_of_tendsto' hlim hfinite

private lemma dyadic_window_tendsto (p₀ : unitInterval) (p : ℕ → unitInterval)
    (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1) (θ : ℝ)
    (hw : ∀ j, |((p j : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
      Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤ θ) : Tendsto p atTop (𝓝 p₀) := by
  let d : ℝ := (p₀ : ℝ) * (1 - (p₀ : ℝ))
  let lam : ℕ → ℝ := fun j => ((p j : ℝ) - (p₀ : ℝ)) / d
  let z : ℕ → ℝ := fun j => Real.sqrt ((2 ^ j : ℕ) : ℝ)
  have hd : d ≠ 0 := ne_of_gt (mul_pos h₀ (sub_pos.mpr h₁))
  have hz : Tendsto z atTop atTop := by
    simpa only [z, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
      Real.tendsto_sqrt_atTop.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hdiv : Tendsto (fun j => (|lam j| * z j) / z j) atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall (fun j => mul_nonneg (abs_nonneg (lam j)) (Real.sqrt_nonneg _)))
      (Eventually.of_forall hw) hz
  have habs : Tendsto (fun j => |lam j|) atTop (𝓝 0) := by
    apply hdiv.congr'
    apply Eventually.of_forall
    intro j
    exact mul_div_cancel_right₀ _ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hlam : Tendsto lam atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using habs)
  have hreal : Tendsto (fun j => (p j : ℝ)) atTop (𝓝 (p₀ : ℝ)) := by
    have ht := (hlam.mul_const d).add_const (p₀ : ℝ)
    convert ht using 1
    · funext j
      dsimp [lam]
      rw [div_mul_cancel₀ _ hd]
      ring
    · simp
  exact tendsto_subtype_rng.2 hreal

/-- All dyadic truncated moments are charged to one endpoint law of the same
stopping rule. The endpoint cost is allowed to be infinite; every perturbed
law retains the independent private seed and the same acquired-bit rule.
A uniform fractional-cost bound along the shrinking windows also bounds
the endpoint cost, without assuming endpoint termination in advance. -/
theorem bernoulli_common_endpoint_budget (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (p : ℕ → unitInterval) (M : Seed × (ℕ → Bool) → WithTop ℕ)
    (hM : IsStoppingTime seededFiltration M) (a : ℝ) (m : ℕ)
    (ha : 0 < a) (ham : a < (m : ℝ))
    (hwindow : ∀ j, |((p j : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ)))| *
      Real.sqrt ((2 ^ j : ℕ) : ℝ) ≤
      (2 * (((2 : ℝ) ^ (2 * m + 1) * (2 * m : ℝ) ^ 2) ^ m *
        (2 : ℝ) ^ (2 * m)) + 1)⁻¹) :
    (∀ j, (∫ ω, (Trunc (M ω) (2 ^ j) : ℝ) ^ m ∂Law ν (p j)) ≤
      2 * ∫ ω, (Trunc (M ω) (2 ^ j) : ℝ) ^ m ∂Law ν p₀) ∧
    (∀ j, ENNReal.ofReal (((2 ^ j : ℕ) : ℝ) ^ m) *
      Law ν (p j) {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω} ≤
      2 * ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂Law ν p₀) ∧
    ((∑' j, ENNReal.ofReal (Weight a m j) *
      ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂Law ν p₀) ≤
      ENNReal.ofReal (GeoBudget a m) * ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀) ∧
    (∀ K : ℝ≥0∞, (∀ j, (∫⁻ ω, EndpointCost a (M ω) ∂Law ν (p j)) ≤ K) →
      (∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀) ≤ K) ∧
    ((∑' j, ENNReal.ofReal (Weight a m j) *
      (ENNReal.ofReal (((2 ^ j : ℕ) : ℝ) ^ m) *
        Law ν (p j) {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω})) ≤
      2 * ENNReal.ofReal (GeoBudget a m) *
        ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀) := by
  have hm : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    simp only [hz, Nat.cast_zero] at ham
    linarith
  have hmoment : ∀ j, (∫ ω, (Trunc (M ω) (2 ^ j) : ℝ) ^ m ∂Law ν (p j)) ≤
      2 * ∫ ω, (Trunc (M ω) (2 ^ j) : ℝ) ^ m ∂Law ν p₀ := by
    intro j
    exact (bernoulli_stopped_moment_bound ν p₀ (p j) h₀ h₁
      (fun ω => Trunc (M ω) (2 ^ j)) (truncation_stopping hM (2 ^ j))
      (2 ^ j) (fun ω => truncation_le (M ω) (2 ^ j)) hm (hwindow j)).2
  have hmeas := hM.measurable.mono hM.measurableSpace_le le_rfl
  have htail : ∀ j, ENNReal.ofReal (((2 ^ j : ℕ) : ℝ) ^ m) *
      Law ν (p j) {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω} ≤
      2 * ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂Law ν p₀ := by
    intro j
    apply (truncation_tail_bound (Law ν (p j)) M hmeas (2 ^ j) m).trans
    rw [← ofReal_integral_eq_lintegral_ofReal
      (truncated_moment_integrable (Law ν (p j)) M hmeas (2 ^ j) m)
      (ae_of_all _ (fun ω => by positivity)),
      ← ofReal_integral_eq_lintegral_ofReal
      (truncated_moment_integrable (Law ν p₀) M hmeas (2 ^ j) m)
      (ae_of_all _ (fun ω => by positivity))]
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      using ENNReal.ofReal_le_ofReal (hmoment j)
  refine ⟨hmoment, htail, ?_, fun K hK =>
    endpoint_from_uniform_cost ν p₀ h₀ h₁ M hM a ha p
      (dyadic_window_tendsto p₀ p h₀ h₁ _ hwindow) K hK, ?_⟩
  · apply ENNReal.tsum_le_of_sum_range_le
    intro K
    exact endpoint_budget_finite (Law ν p₀) M hmeas a m ha ham K
  · apply ENNReal.tsum_le_of_sum_range_le
    intro K
    calc
      (∑ j ∈ range K, ENNReal.ofReal (Weight a m j) *
          (ENNReal.ofReal (((2 ^ j : ℕ) : ℝ) ^ m) *
            Law ν (p j) {ω | ((2 ^ j : ℕ) : WithTop ℕ) < M ω})) ≤
          ∑ j ∈ range K, 2 * (ENNReal.ofReal (Weight a m j) *
            ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂Law ν p₀) := by
        apply sum_le_sum
        intro j hj
        simpa only [mul_left_comm] using
          mul_le_mul_right (htail j) (ENNReal.ofReal (Weight a m j))
      _ = 2 * (∑ j ∈ range K, ENNReal.ofReal (Weight a m j) *
          ∫⁻ ω, ENNReal.ofReal ((Trunc (M ω) (2 ^ j) : ℝ) ^ m) ∂Law ν p₀) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * (ENNReal.ofReal (GeoBudget a m) *
          ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀) :=
        mul_le_mul_right (endpoint_budget_finite (Law ν p₀) M hmeas a m ha ham K) 2
      _ = 2 * ENNReal.ofReal (GeoBudget a m) *
          ∫⁻ ω, EndpointCost a (M ω) ∂Law ν p₀ := (mul_assoc _ _ _).symm


private lemma normalized_likelihood_moment (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ p : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (heq : ((p : ℝ) - (p₀ : ℝ)) / ((p₀ : ℝ) * (1 - (p₀ : ℝ))) = lam)
    {m : ℕ} (hm : 0 < m)
    (hw : lam * Real.sqrt (n : ℝ) ≤ (2 * MomentC m + 1)⁻¹) :
    (∫⁻ ω, ENNReal.ofReal (|(Like p₀ p (τ ω) ω - 1) / lam| ^ (2 * m)) ∂Law ν p₀) ≤
      ENNReal.ofReal (2 * MomentC m * ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p₀) := by
  let μ := Law ν p₀
  let S := fun ω => (range (n + 1)).sup' nonempty_range_add_one
    (fun i => |Like p₀ p (min i (τ ω)) ω - 1|)
  have ht := stopping_nat_measurable hτ
  have hS : Measurable S := by
    have hm : ∀ i ∈ range (n + 1), Measurable
        (fun ω => |Like p₀ p (min i (τ ω)) ω - 1|) := by
      intro i hi
      exact continuous_abs.measurable.comp
        ((stopped_like_measurable p₀ p (fun ω => min i (τ ω))
          (measurable_const.min ht)).sub measurable_const)
    convert Finset.measurable_sup' nonempty_range_add_one hm using 1
    funext ω
    exact (Finset.sup'_apply nonempty_range_add_one
      (fun i ω => |Like p₀ p (min i (τ ω)) ω - 1|) ω).symm
  have hS0 : ∀ ω, 0 ≤ S ω := by
    intro ω
    exact (abs_nonneg (Like p₀ p (min 0 (τ ω)) ω - 1)).trans
      (le_sup' (fun i => |Like p₀ p (min i (τ ω)) ω - 1|)
        (mem_range.mpr (show 0 < n + 1 by omega)))
  have hSb : ∀ ω, S ω ≤ RatioBound p₀ ^ n + 1 := by
    intro ω
    apply sup'_le
    intro i hi
    calc
      _ ≤ |Like p₀ p (min i (τ ω)) ω| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ RatioBound p₀ ^ n + 1 := by
        rw [abs_of_nonneg (like_nonneg p₀ p _ _), abs_one]
        exact add_le_add_left ((like_uniform_bound p₀ p _ ω).trans
          (pow_le_pow_right₀ (le_max_left _ _) ((min_le_right i (τ ω)).trans (hτn ω)))) 1
  have hSi : Integrable (fun ω => S ω ^ (2 * m)) μ :=
    ⟨hS.stronglyMeasurable.pow _ |>.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (RatioBound p₀ ^ n + 1) ^ (2 * m))
        (ae_of_all _ (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hS0 ω) _)]
          exact pow_le_pow_left₀ (hS0 ω) (hSb ω) _))⟩
  have hterminal : ∀ ω, |Like p₀ p (τ ω) ω - 1| ≤ S ω := by
    intro ω
    have h := le_sup' (fun i => |Like p₀ p (min i (τ ω)) ω - 1|)
      (mem_range.mpr (Nat.lt_succ_self n))
    simpa only [min_eq_right (hτn ω)] using h
  have htp : Measurable (fun ω => |Like p₀ p (τ ω) ω - 1| ^ (2 * m)) :=
    (continuous_abs.measurable.comp
      ((stopped_like_measurable p₀ p τ ht).sub measurable_const)).pow_const _
  have hti : Integrable (fun ω => |Like p₀ p (τ ω) ω - 1| ^ (2 * m)) μ :=
    hSi.mono' htp.aestronglyMeasurable (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hterminal ω) _))
  have habs := (StoppedLikelihoodAbsorption.stopped_likelihood_bounds
    (likelihood_martingale ν p₀ p h₀ h₁) (Bit p₀) τ hτ lam n
    (fun ω => by simp) hτn (centered_bit_bound p₀)
    (fun ω => like_nonneg p₀ p _ _)
    (fun i ω => by rw [← heq]; exact likelihood_step p₀ p h₀ h₁ i ω) hm
    (by simpa only [abs_of_pos hlam] using hw)).1
  have hreal : (∫ ω, |Like p₀ p (τ ω) ω - 1| ^ (2 * m) ∂μ) ≤
      2 * MomentC m * lam ^ (2 * m) * ∫ ω, (τ ω : ℝ) ^ m ∂μ :=
    (integral_mono hti hSi (fun ω => pow_le_pow_left₀ (abs_nonneg _)
      (hterminal ω) _)).trans (by simpa only [abs_of_pos hlam] using habs)
  simp_rw [abs_div, abs_of_pos hlam, div_pow]
  rw [← ofReal_integral_eq_lintegral_ofReal (hti.div_const _)
    (ae_of_all _ (fun ω => by positivity)), integral_div]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ (pow_pos hlam _)).2
  convert hreal using 1 <;> first | rfl | ring

/-- The stopped centered Bernoulli score has an even moment controlled by the
same random stopping-time moment, uniformly in the deterministic horizon. -/
theorem bernoulli_stopped_score_moment (ν : Measure Seed) [IsProbabilityMeasure ν]
    (p₀ : unitInterval) (h₀ : 0 < (p₀ : ℝ)) (h₁ : (p₀ : ℝ) < 1)
    (τ : Seed × (ℕ → Bool) → ℕ)
    (hτ : IsStoppingTime seededFiltration (fun ω => (τ ω : WithTop ℕ)))
    (n : ℕ) (hτn : ∀ ω, τ ω ≤ n) {m : ℕ} (hm : 0 < m) :
    (∫⁻ ω, ENNReal.ofReal (|∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m)) ∂Law ν p₀) ≤
      ENNReal.ofReal (2 * MomentC m * ∫ ω, (τ ω : ℝ) ^ m ∂Law ν p₀) := by
  let d : ℝ := (p₀ : ℝ) * (1 - (p₀ : ℝ))
  have hd : 0 < d := mul_pos h₀ (sub_pos.mpr h₁)
  let lam : ℕ → ℝ := fun j => ((j : ℝ) + 2)⁻¹
  have hl0 : ∀ j, 0 < lam j := fun j => by dsimp [lam]; positivity
  have hl1 : ∀ j, lam j ≤ 1 := fun j => by
    dsimp [lam]
    exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
  let p : ℕ → unitInterval := fun j => ⟨(p₀ : ℝ) + lam j * d, by
    constructor
    · positivity
    · have hp : (p₀ : ℝ) ≤ 1 := p₀.2.2
      have hmul := mul_le_mul_of_nonneg_right (hl1 j) hd.le
      dsimp [d] at hmul
      nlinarith [p₀.2.1]⟩
  have heq : ∀ j, ((p j : ℝ) - (p₀ : ℝ)) / d = lam j := by
    intro j
    dsimp [p]
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ hd.ne']
  let f := fun j ω => ENNReal.ofReal (|(Like p₀ (p j) (τ ω) ω - 1) / lam j| ^ (2 * m))
  have ht := stopping_nat_measurable hτ
  have hf : ∀ j, Measurable (f j) := by
    intro j
    have hg : Measurable (fun ω => (Like p₀ (p j) (τ ω) ω - 1) / lam j) :=
      ((stopped_like_measurable p₀ (p j) τ ht).sub measurable_const).div_const _
    exact ((continuous_abs.measurable.comp hg).pow_const _).ennreal_ofReal
  have hl : Tendsto lam atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hlne : Tendsto lam atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hl, Eventually.of_forall (fun j => (hl0 j).ne')⟩
  have hlim : ∀ ω, Tendsto (fun j => f j ω) atTop
      (𝓝 (ENNReal.ofReal (|∑ i ∈ range (τ ω), Bit p₀ i ω| ^ (2 * m)))) := by
    intro ω
    have hder : HasDerivAt (fun t : ℝ => ∏ i ∈ range (τ ω), (1 + t * Bit p₀ i ω))
        (∑ i ∈ range (τ ω), Bit p₀ i ω) 0 := by
      simpa using HasDerivAt.fun_finsetProd (u := range (τ ω))
        (fun i hi => ((hasDerivAt_id (0 : ℝ)).mul_const (Bit p₀ i ω)).const_add 1)
    have hprod : ∀ j, Like p₀ (p j) (τ ω) ω =
        ∏ i ∈ range (τ ω), (1 + lam j * Bit p₀ i ω) := by
      intro j
      apply prod_congr rfl
      intro i hi
      cases hb : ω.2 i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte]
      all_goals dsimp [p, d]; field_simp [h₀.ne', (sub_pos.mpr h₁).ne'] <;> ring
    have hs := hder.tendsto_slope_zero.comp hlne
    have hs' : Tendsto (fun j => (Like p₀ (p j) (τ ω) ω - 1) / lam j) atTop
        (𝓝 (∑ i ∈ range (τ ω), Bit p₀ i ω)) := by
      simpa only [Function.comp_def, zero_add, zero_mul, add_zero, prod_const_one,
        smul_eq_mul, ← div_eq_inv_mul, ← hprod] using hs
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs'.abs.pow _)
  have hw : ∀ᶠ j in atTop,
      lam j * Real.sqrt (n : ℝ) ≤ (2 * MomentC m + 1)⁻¹ := by
    have hpos : 0 < (2 * MomentC m + 1)⁻¹ := by positivity
    have hz : Tendsto (fun j => lam j * Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
      simpa using hl.mul_const (Real.sqrt (n : ℝ))
    exact (hz.eventually (gt_mem_nhds hpos)).mono (fun j hj => hj.le)
  calc
    _ = ∫⁻ ω, liminf (fun j => f j ω) atTop ∂Law ν p₀ :=
      lintegral_congr (fun ω => (hlim ω).liminf_eq.symm)
    _ ≤ liminf (fun j => ∫⁻ ω, f j ω ∂Law ν p₀) atTop := lintegral_liminf_le hf
    _ ≤ _ := liminf_le_of_frequently_le' (hw.mono (fun j hj =>
      normalized_likelihood_moment ν p₀ (p j) h₀ h₁ τ hτ n hτn (lam j) (hl0 j)
        (heq j) hm hj)).frequently



end D5.S3.Estimation.SequentialDecisionRisk.SeededBernoulliStoppedMoment

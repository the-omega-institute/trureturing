/- GID: D5/S3/Observer/ProbabilisticClosure/FiniteHorizonJointAttainment
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/FiniteHorizonJointAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-history shape control jointly attains finite paid-count and marginal root risk. -/

import D5.S3.Observer.ProbabilisticClosure.BeneficialMarkerDeflection
import D5.S3.Observer.ProbabilisticClosure.RawFiniteAtomLinearRealization
import Mathlib.Data.Bool.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.FiniteHorizonJointAttainment

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
open AdaptiveMarkerStoppingTails BeneficialMarkerDeflection FiniteAtomLinearRealization

local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace (List Bool) := ⊤

/-- The next even-depth shape is selected using only the acquired actions. -/
def shapePolicy {Seed : Type*} [MeasurableSpace Seed] (d : ℕ → Bool) : Policy Seed where
  choose := fun _ actions _ =>
    if actions.length % 2 = 0 then false
    else xor (parity actions).2 (d ((actions.length + 1) / 2))
  measurable_section := fun _ _ => measurable_const

/-- Every prescribed sequence occurs at its original even replay depth. -/
theorem prescribed_even_parity {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (seed : Seed) (m : ℕ) (hm : 1 ≤ m) :
    parity (zeroReplay (shapePolicy d) seed (2 * m)) = (d m, d m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let actions := zeroReplay (shapePolicy d) seed (2 * k)
  have hlen : actions.length = 2 * k := zero_replay_length _ _ _
  have hcounts : sideCount actions false + sideCount actions true = 2 * k := by
    simpa [sideCount, hlen] using List.count_false_add_count_true actions
  have hp : (parity actions).1 = (parity actions).2 := by
    have hmod : sideCount actions false % 2 = sideCount actions true % 2 := by omega
    simp only [parity, hmod]
  have hrun : zeroReplay (shapePolicy d) seed (2 * (k + 1)) =
      xor (parity (false :: actions)).2 (d (k + 1)) :: false :: actions := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
    simp [zeroReplay, shapePolicy, actions, zero_replay_length, Nat.add_mod]
    congr 1
    omega
  rw [hrun, parity_cons, parity_cons]
  generalize he : parity actions = eta at *
  rcases eta with ⟨l, r⟩
  cases l <;> cases r <;> cases hd : d (k + 1) <;>
    simp_all [flipParity, Bool.xor]

/-- The prescribed shape controls the actual independent-seed shape probability. -/
private theorem shape_lambda {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (m : ℕ) (hm : 1 ≤ m) :
    lambda (shapePolicy d) ν m = if d m then 1 else 0 := by
  have he (u : Seed) := prescribed_even_parity d u m hm
  have hboth (u : Seed) :
      (sideCount (zeroReplay (shapePolicy d) u (2 * m)) false % 2 = 1 ∧
        sideCount (zeroReplay (shapePolicy d) u (2 * m)) true % 2 = 1) ↔ d m = true := by
    have h1 := congrArg Prod.fst (he u)
    have h2 := congrArg Prod.snd (he u)
    simp only [parity, decide_eq_true_eq] at h1 h2
    cases hd : d m <;> simp_all
  unfold lambda
  simp_rw [hboth]
  cases hd : d m <;> simp [hd]

private instance prior_probability {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (alpha : unitInterval)
    (μ : Measure unitInterval) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (priorLaw ν alpha μ) :=
  isProbabilityMeasure_bind (measurable_joint_law ν alpha).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

/-- Finite moments are integrated before any root decision. -/
def moment (μ : Measure unitInterval) (j : ℕ) : ℝ := ∫ q, (q : ℝ) ^ j ∂μ

def momentSum (μ : Measure unitInterval) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, moment μ j

/-- The expectation of the number actually paid by the absorbing execution. -/
def cappedMean {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (ν : Measure Seed) (alpha : unitInterval) (μ : Measure unitInterval) (n : ℕ) : ℝ :=
  ∫ p, (actualQueryCount policy p.1 p.2 n : ℝ) ∂priorLaw ν alpha μ

private theorem prior_real {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (alpha : unitInterval)
    (μ : Measure unitInterval) (S : Set (Seed × Source)) (hS : MeasurableSet S) :
    (priorLaw ν alpha μ).real S = ∫ q, (jointLaw ν alpha q).real S ∂μ := by
  rw [measureReal_def, priorLaw, Measure.bind_apply hS (measurable_joint_law ν alpha).aemeasurable]
  exact (integral_toReal ((Measure.measurable_coe hS).comp
    (measurable_joint_law ν alpha)).aemeasurable
    (Eventually.of_forall fun q => measure_lt_top _ _)).symm

private theorem measurable_survival {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (n : ℕ) : MeasurableSet
      {p : Seed × Source | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} := by
  have he : {p : Seed × Source | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} =
      {p | (actualRun policy p.1 p.2 n).stopped = false} := by
    ext p
    exact (stopped_execution_replay_bridge policy p.1 p.2 n).1.trans
      (stopped_execution_replay_bridge policy p.1 p.2 n).2.1.symm
  rw [he]
  exact ((measurable_of_countable State.stopped).comp
    (RawFiniteAtomLinearRealization.measurable_actual_run policy n)) (measurableSet_singleton false)

private theorem mean_tails {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] (n : ℕ) :
    cappedMean policy ν alpha μ n = ∑ t ∈ Finset.range n,
      (priorLaw ν alpha μ).real {p | (t : WithTop ℕ) < stoppingTime policy p.1 p.2} := by
  classical
  let S (t : ℕ) : Set (Seed × Source) :=
    {p | (t : WithTop ℕ) < stoppingTime policy p.1 p.2}
  have hc (p : Seed × Source) : ∀ n,
      (actualQueryCount policy p.1 p.2 n : ℝ) =
        ∑ t ∈ Finset.range n, (S t).indicator (fun _ => (1 : ℝ)) p := by
    intro n
    induction n with
    | zero => simp [actualQueryCount, actualRun]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hb := stopped_execution_replay_bridge policy p.1 p.2 n
      by_cases hs : (actualRun policy p.1 p.2 n).stopped = true
      · have hnot : p ∉ S n := by
          intro hin
          have hf := hb.2.1.mpr (hb.1.mp hin)
          simp [hs] at hf
        simp [actualQueryCount, actualRun, hs, Set.indicator_of_notMem hnot]
      · have hf : (actualRun policy p.1 p.2 n).stopped = false := Bool.eq_false_iff.mpr hs
        have hin : p ∈ S n := hb.1.mpr (hb.2.1.mp hf)
        simp [actualQueryCount, actualRun, hs, Set.indicator_of_mem hin, Nat.cast_add]
  unfold cappedMean
  simp_rw [hc]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t ht
    exact integral_indicator_one (measurable_survival policy t)
  · intro t ht
    exact (integrable_const (1 : ℝ)).indicator (measurable_survival policy t)

private theorem moment_integrable (μ : Measure unitInterval) [IsFiniteMeasure μ] (j : ℕ) :
    Integrable (fun q : unitInterval => (q : ℝ) ^ j) μ :=
  by
    simpa using (show Continuous (fun q : unitInterval => (q : ℝ) ^ j) by fun_prop).continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ

private theorem moment_zero (μ : Measure unitInterval) [IsProbabilityMeasure μ] : moment μ 0 = 1 := by
  simp [moment]

private theorem coefficient_moments (alpha : unitInterval) (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 1 ≤ m) :
    coefficient alpha μ m = (alpha : ℝ) * (moment μ (m - 1) - moment μ m) -
      (1 - (alpha : ℝ)) * (moment μ m - moment μ (m + 1)) := by
  have he : (fun q : unitInterval =>
      (1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ (m - 1)) =
      (fun q : unitInterval => (alpha : ℝ) * ((q : ℝ) ^ (m - 1) - (q : ℝ) ^ m) -
        (1 - (alpha : ℝ)) * ((q : ℝ) ^ m - (q : ℝ) ^ (m + 1))) := by
    funext q
    have hp : (q : ℝ) ^ m = (q : ℝ) ^ (m - 1) * (q : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [pow_succ, hp]
    ring
  unfold coefficient
  have hi1 : Integrable (fun q : unitInterval => (alpha : ℝ) *
      ((q : ℝ) ^ (m - 1) - (q : ℝ) ^ m)) μ :=
    ((moment_integrable μ (m - 1)).sub (moment_integrable μ m)).const_mul _
  have hi2 : Integrable (fun q : unitInterval => (1 - (alpha : ℝ)) *
      ((q : ℝ) ^ m - (q : ℝ) ^ (m + 1))) μ :=
    ((moment_integrable μ m).sub (moment_integrable μ (m + 1))).const_mul _
  rw [he, integral_sub hi1 hi2]
  simp_rw [integral_const_mul, integral_sub (moment_integrable μ _) (moment_integrable μ _)]
  rfl

private theorem integrated_tails {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] :
    (∀ m, (priorLaw ν alpha μ).real
      {p | ((2 * m + 1 : ℕ) : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        (alpha : ℝ) * moment μ m + (1 - (alpha : ℝ)) * moment μ (m + 1)) ∧
    (∀ m, 1 ≤ m → (priorLaw ν alpha μ).real
      {p | ((2 * m : ℕ) : WithTop ℕ) < stoppingTime policy p.1 p.2} =
        moment μ m + lambda policy ν m * coefficient alpha μ m) := by
  constructor
  · intro m
    rw [prior_real ν alpha μ _ (measurable_survival policy _)]
    simp_rw [(adaptive_marker_stopping_tails policy ν alpha _).1 m]
    have he : (fun q : unitInterval =>
        ((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ m) =
        (fun q : unitInterval => (alpha : ℝ) * (q : ℝ) ^ m +
          (1 - (alpha : ℝ)) * (q : ℝ) ^ (m + 1)) := by
      funext q
      rw [pow_succ]
      ring
    rw [he, integral_add ((moment_integrable μ _).const_mul _)
      ((moment_integrable μ _).const_mul _)]
    simp [moment, integral_const_mul]
  · intro m hm
    rw [prior_real ν alpha μ _ (measurable_survival policy _)]
    simp_rw [(adaptive_marker_stopping_tails policy ν alpha _).2.1 m hm]
    have he : (fun q : unitInterval => (q : ℝ) ^ m + lambda policy ν m *
        (((alpha : ℝ) + (1 - (alpha : ℝ)) * (q : ℝ) ^ 2) - (q : ℝ)) *
          (q : ℝ) ^ (m - 1)) =
        (fun q : unitInterval => (q : ℝ) ^ m + lambda policy ν m *
          ((1 - (q : ℝ)) * ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) *
            (q : ℝ) ^ (m - 1))) := by funext q; ring
    have hi : Integrable (fun q : unitInterval => (1 - (q : ℝ)) *
        ((alpha : ℝ) - (1 - (alpha : ℝ)) * (q : ℝ)) * (q : ℝ) ^ (m - 1)) μ :=
      by simpa using (show Continuous _ by fun_prop).continuousOn.integrableOn_compact (μ := μ) isCompact_univ
    rw [he]
    rw [integral_add (moment_integrable μ _) (hi.const_mul _), integral_const_mul]
    rfl

private def correction {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) (alpha : unitInterval)
    (μ : Measure unitInterval) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, lambda policy ν (j + 1) * coefficient alpha μ (j + 1)

private def evenBase (alpha : unitInterval) (μ : Measure unitInterval) (N : ℕ) : ℝ :=
  2 * momentSum μ N - (1 - (alpha : ℝ)) + (1 - (alpha : ℝ)) * moment μ N

private def oddBase (alpha : unitInterval) (μ : Measure unitInterval) (N : ℕ) : ℝ :=
  2 * momentSum μ N - (1 - (alpha : ℝ)) + (2 - (alpha : ℝ)) * moment μ N

private theorem mean_formulas {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] :
    (∀ N, cappedMean policy ν alpha μ (2 * N + 1) =
      oddBase alpha μ N + correction policy ν alpha μ N) ∧
    (∀ N, 1 ≤ N → cappedMean policy ν alpha μ (2 * N) =
      evenBase alpha μ N + correction policy ν alpha μ (N - 1)) := by
  have ht := integrated_tails policy ν alpha μ
  have hrec (n : ℕ) : cappedMean policy ν alpha μ (n + 1) =
      cappedMean policy ν alpha μ n +
        (priorLaw ν alpha μ).real {p | (n : WithTop ℕ) < stoppingTime policy p.1 p.2} := by
    simp only [mean_tails, Finset.sum_range_succ]
  have heven (N : ℕ) (ho : cappedMean policy ν alpha μ (2 * N + 1) =
      oddBase alpha μ N + correction policy ν alpha μ N) :
      cappedMean policy ν alpha μ (2 * (N + 1)) =
        evenBase alpha μ (N + 1) + correction policy ν alpha μ N := by
    rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega, hrec, ho, ht.1 N]
    simp only [evenBase, oddBase, momentSum, Finset.sum_range_succ]
    ring
  have hodd : ∀ N, cappedMean policy ν alpha μ (2 * N + 1) =
      oddBase alpha μ N + correction policy ν alpha μ N := by
    intro N
    induction N with
    | zero =>
      simp [cappedMean, actualQueryCount, actualRun, oddBase, momentSum, correction, moment_zero]
    | succ N ih =>
      rw [hrec, heven N ih, ht.2 (N + 1) (by omega)]
      simp only [correction, Finset.sum_range_succ, evenBase, oddBase]
      ring
  refine ⟨hodd, ?_⟩
  intro N hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  simpa using heven k (hodd k)

/-- The closed finite paid-prefix minimum, with no reciprocal-moment premise. -/
def minimumMean (alpha : unitInterval) (μ : Measure unitInterval) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (if n % 2 = 0 then evenBase alpha μ (n / 2) else oddBase alpha μ (n / 2)) +
      ∑ j ∈ Finset.range ((n - 1) / 2), min 0 (coefficient alpha μ (j + 1))

private theorem minimum_even (alpha : unitInterval) (μ : Measure unitInterval)
    (N : ℕ) (hN : 1 ≤ N) : minimumMean alpha μ (2 * N) =
      evenBase alpha μ N + ∑ j ∈ Finset.range (N - 1), min 0 (coefficient alpha μ (j + 1)) := by
  simp [minimumMean, show 2 * N ≠ 0 by omega, show (2 * N - 1) / 2 = N - 1 by omega]

private theorem minimum_odd (alpha : unitInterval) (μ : Measure unitInterval) (N : ℕ) :
    minimumMean alpha μ (2 * N + 1) =
      oddBase alpha μ N + ∑ j ∈ Finset.range N, min 0 (coefficient alpha μ (j + 1)) := by
  simp [minimumMean, Nat.add_mod, show (2 * N + 1) / 2 = N by omega]

private theorem mixture_min_bound (l v : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) : min 0 v ≤ l * v := by
  by_cases hv : 0 ≤ v
  · rw [min_eq_left hv]
    exact mul_nonneg hl.1 hv
  · rw [min_eq_right (le_of_not_ge hv)]
    nlinarith [hl.1, hl.2]

private theorem mean_lower {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] (n : ℕ) :
    minimumMean alpha μ n ≤ cappedMean policy ν alpha μ n := by
  have hl := (adaptive_marker_stopping_tails policy ν alpha (0 : unitInterval)).2.2
  have hsum (N : ℕ) : (∑ j ∈ Finset.range N, min 0 (coefficient alpha μ (j + 1))) ≤
      correction policy ν alpha μ N :=
    Finset.sum_le_sum fun j _ => mixture_min_bound _ _ (hl (j + 1))
  by_cases hn : n = 0
  · subst n
    simp [minimumMean, cappedMean, actualQueryCount, actualRun]
  · by_cases he : n % 2 = 0
    · have hN : 1 ≤ n / 2 := by omega
      have hne : n = 2 * (n / 2) := by omega
      rw [hne, minimum_even _ _ _ hN, (mean_formulas policy ν alpha μ).2 _ hN]
      exact add_le_add_left (hsum _) _
    · have hne : n = 2 * (n / 2) + 1 := by omega
      rw [hne, minimum_odd, (mean_formulas policy ν alpha μ).1]
      exact add_le_add_left (hsum _) _

end D5.S3.Observer.ProbabilisticClosure.FiniteHorizonJointAttainment

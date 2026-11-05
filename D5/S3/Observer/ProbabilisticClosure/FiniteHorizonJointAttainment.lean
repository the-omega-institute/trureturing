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

universe u

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
private theorem prescribed_even_parity {Seed : Type*} [MeasurableSpace Seed]
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
      <;> norm_num
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
      exact add_le_add le_rfl (hsum _)
    · have hne : n = 2 * (n / 2) + 1 := by omega
      rw [hne, minimum_odd, (mean_formulas policy ν alpha μ).1]
      exact add_le_add le_rfl (hsum _)

private def replay (d : ℕ → Bool) (n : ℕ) : List Side :=
  zeroReplay (shapePolicy d : Policy Unit) () n

private theorem replay_seed_independent {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (seed : Seed) (n : ℕ) :
    zeroReplay (shapePolicy d) seed n = replay d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change zeroReplay (shapePolicy d) seed n = zeroReplay (shapePolicy d : Policy Unit) () n at ih
    change zeroReplay (shapePolicy d) seed (n + 1) = zeroReplay (shapePolicy d : Policy Unit) () (n + 1)
    simp only [zeroReplay]
    rw [ih]
    rfl

private def rootExponent (root : Bool) (actions : List Side) : ℕ :=
  if root then sideCount actions false / 2 + sideCount actions true / 2
  else (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2

/-- Original-prior root mass on the only leaf without an acquired marker. -/
def rootEvidence (alpha : unitInterval) (μ : Measure unitInterval)
    (actions : List Side) (root : Bool) : ℝ :=
  (if root then (alpha : ℝ) else 1 - (alpha : ℝ)) * moment μ (rootExponent root actions)

/-- This decision integrates the hidden parameter and then compares root masses. -/
def integratedRoot (alpha : unitInterval) (μ : Measure unitInterval) (actions : List Side) : Bool :=
  decide (rootEvidence alpha μ actions false ≤ rootEvidence alpha μ actions true)

/-- Acquired markers use native root recovery; the other leaf uses integrated MAP. -/
def forcedRootDecoder (alpha : unitInterval) (μ : Measure unitInterval)
    (actions : List Side) (h : State) : Bool :=
  if h.stopped then recoveredRoot h else integratedRoot alpha μ actions

/-- The marginal error of the decoder on the same absorbing execution and prior. -/
def marginalError {Seed : Type*} [MeasurableSpace Seed] (policy : Policy Seed)
    (decode : State → Bool) (ν : Measure Seed) (alpha : unitInterval)
    (μ : Measure unitInterval) (n : ℕ) : ℝ :=
  (priorLaw ν alpha μ).real {p | decode (actualRun policy p.1 p.2 n) ≠ p.2.1}

private theorem measurable_error {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (decode : State → Bool) (n : ℕ) :
    MeasurableSet {p : Seed × Source | decode (actualRun policy p.1 p.2 n) ≠ p.2.1} := by
  exact (measurableSet_eq_fun ((measurable_of_countable decode).comp
    (RawFiniteAtomLinearRealization.measurable_actual_run policy n))
    (measurable_fst.comp measurable_snd)).compl

private theorem root_cylinder_mass (alpha q : unitInterval) (actions : List Side) (root : Bool) :
    (sourceLaw alpha q).real {s | prefixNoMarker s actions ∧ s.1 = root} =
      (if root then (alpha : ℝ) else 1 - (alpha : ℝ)) * rootCylinderWeight q root actions := by
  have hc (r : Bool) :
      (conditionalSourceLaw q r).real {s | prefixNoMarker s actions ∧ s.1 = root} =
        if r = root then rootCylinderWeight q r actions else 0 := by
    have hr : ∀ᵐ s ∂conditionalSourceLaw q r, s.1 = r := by
      rw [conditionalSourceLaw]
      exact (ae_map_iff (by fun_prop) (measurableSet_eq_fun measurable_fst measurable_const)).mpr
        (Eventually.of_forall fun _ => rfl)
    have he : ({s | prefixNoMarker s actions ∧ s.1 = root} : Set Source) =ᵐ[conditionalSourceLaw q r]
        (if r = root then {s | prefixNoMarker s actions} else ∅) := by
      filter_upwards [hr] with s hs
      by_cases heq : r = root <;> simp [hs, heq]
    rw [measureReal_def, measure_congr he]
    by_cases heq : r = root
    · rw [if_pos heq, if_pos heq, ← measureReal_def, conditional_prefix_mass]
    · simp [heq]
  rw [source_law_real, hc true, hc false]
  cases root <;> simp

private theorem actual_shape_risk {Seed : Type u} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] (n : ℕ) :
    marginalError (shapePolicy d) (forcedRootDecoder alpha μ (replay d n)) ν alpha μ n =
      min (rootEvidence alpha μ (replay d n) false) (rootEvidence alpha μ (replay d n) true) := by
  classical
  let actions := replay d n
  let c := integratedRoot alpha μ actions
  have hcond (q : unitInterval) :
      (jointLaw ν alpha q).real
        {p | forcedRootDecoder alpha μ actions (actualRun (shapePolicy d) p.1 p.2 n) ≠ p.2.1} =
      (sourceLaw alpha q).real {s | prefixNoMarker s actions ∧ s.1 = !c} := by
    have hc := RawFiniteAtomLinearRealization.result.{u, 0}.2 1 alpha
      (fun _ : Fin 1 => q) (fun _ : Fin 1 => (1 : ℝ))
    have hcoupling : ∀ᵐ s ∂sourceLaw alpha q,
        ∀ (Seed : Type _) [MeasurableSpace Seed] (policy : Policy Seed) (seed : Seed) (n : ℕ),
          (actualRun policy seed s n).stopped = true → recoveredRoot (actualRun policy seed s n) = s.1 := by
      simpa [RawFiniteAtomLinearRealization.RootCoupling, sourceMixture] using hc
    have hp := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := sourceLaw alpha q)).ae hcoupling
    have he : ({p : Seed × Source |
        forcedRootDecoder alpha μ actions (actualRun (shapePolicy d) p.1 p.2 n) ≠ p.2.1} : Set _) =ᵐ[jointLaw ν alpha q]
        (Set.univ ×ˢ {s | prefixNoMarker s actions ∧ s.1 = !c}) := by
      filter_upwards [hp] with p hp
      have hb := stopped_execution_replay_bridge (shapePolicy d) p.1 p.2 n
      have hr : zeroReplay (shapePolicy d) p.1 n = actions := replay_seed_independent d p.1 n
      by_cases hs : (actualRun (shapePolicy d) p.1 p.2 n).stopped = true
      · have hroot := hp Seed (shapePolicy d) p.1 n hs
        have hn : ¬prefixNoMarker p.2 actions := by
          intro hn
          have hf := hb.2.1.mpr (hr ▸ hn)
          simp [hs] at hf
        simp [forcedRootDecoder, hs, hroot, hn]
      · have hf : (actualRun (shapePolicy d) p.1 p.2 n).stopped = false := Bool.eq_false_iff.mpr hs
        have hn : prefixNoMarker p.2 actions := hr ▸ (hb.2.1.mp hf)
        simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_setOf_eq]
        change (forcedRootDecoder alpha μ actions (actualRun (shapePolicy d) p.1 p.2 n) ≠ p.2.1) =
          (prefixNoMarker p.2 actions ∧ p.2.1 = !c)
        simp only [forcedRootDecoder, hs, Bool.false_eq_true, ite_false, hn, true_and]
        change (c ≠ p.2.1) = (p.2.1 = !c)
        cases c <;> cases p.2.1 <;> simp
    rw [measureReal_def, measure_congr he, ← measureReal_def, jointLaw,
      measureReal_prod_prod]
    simp
  unfold marginalError
  rw [prior_real ν alpha μ _ (measurable_error _ _ _)]
  change (∫ q, (jointLaw ν alpha q).real
    {p | forcedRootDecoder alpha μ actions (actualRun (shapePolicy d) p.1 p.2 n) ≠ p.2.1} ∂μ) = _
  simp_rw [hcond, root_cylinder_mass]
  have hint : (∫ q, (if !c then (alpha : ℝ) else 1 - (alpha : ℝ)) *
      rootCylinderWeight q (!c) actions ∂μ) = rootEvidence alpha μ actions (!c) := by
    rw [integral_const_mul]
    rfl
  rw [hint]
  change rootEvidence alpha μ actions (!c) =
    min (rootEvidence alpha μ actions false) (rootEvidence alpha μ actions true)
  by_cases h : rootEvidence alpha μ actions false ≤ rootEvidence alpha μ actions true
  · simp [c, integratedRoot, h, min_eq_left h]
  · simp [c, integratedRoot, h, min_eq_right (le_of_not_ge h)]

/-- Both lawful terminal shapes are evaluated under the integrated prior. -/
def evenRisk (alpha : unitInterval) (μ : Measure unitInterval) (N : ℕ) (d : Bool) : ℝ :=
  if d then min ((1 - (alpha : ℝ)) * moment μ (N + 1)) ((alpha : ℝ) * moment μ (N - 1))
  else min ((1 - (alpha : ℝ)) * moment μ N) ((alpha : ℝ) * moment μ N)

/-- The finite root-error frontier, including the unqueried root. -/
def minimumRisk (alpha : unitInterval) (μ : Measure unitInterval) (n : ℕ) : ℝ :=
  if n = 0 then min (1 - (alpha : ℝ)) (alpha : ℝ)
  else min ((1 - (alpha : ℝ)) * moment μ (n / 2 + 1)) ((alpha : ℝ) * moment μ (n / 2))

private theorem moment_antitone (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) :
    moment μ (N + 1) ≤ moment μ N := by
  apply integral_mono (moment_integrable μ _) (moment_integrable μ _)
  intro q
  change (q : ℝ) ^ (N + 1) ≤ (q : ℝ) ^ N
  rw [pow_succ]
  exact mul_le_of_le_one_right (pow_nonneg (unitInterval.nonneg q) _) (unitInterval.le_one q)

private theorem even_risk_minimum (alpha : unitInterval) (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N) :
    min (evenRisk alpha μ N false) (evenRisk alpha μ N true) = minimumRisk alpha μ (2 * N) := by
  have hp := mul_le_mul_of_nonneg_left (moment_antitone μ N) (unitInterval.one_minus_nonneg alpha)
  have hm : moment μ N ≤ moment μ (N - 1) := by
    simpa [Nat.sub_add_cancel hN] using moment_antitone μ (N - 1)
  have hq := mul_le_mul_of_nonneg_left hm (unitInterval.nonneg alpha)
  simp only [evenRisk, Bool.false_eq_true, ite_false, ite_true, minimumRisk,
    show 2 * N ≠ 0 by omega, ite_false, show 2 * N / 2 = N by omega]
  apply le_antisymm
  · exact le_min ((min_le_right _ _).trans (min_le_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
  · exact le_min (le_min ((min_le_left _ _).trans hp) (min_le_right _ _))
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hq))

private theorem shape_risk_even {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) :
    marginalError (shapePolicy d) (forcedRootDecoder alpha μ (replay d (2 * N))) ν alpha μ (2 * N) =
      evenRisk alpha μ N (d N) := by
  rw [actual_shape_risk]
  let actions := replay d (2 * N)
  have hlen : actions.length = 2 * N := zero_replay_length _ _ _
  have hcounts : sideCount actions false + sideCount actions true = 2 * N := by
    simpa [sideCount, hlen] using List.count_false_add_count_true actions
  have hp : parity actions = (d N, d N) := prescribed_even_parity d () N hN
  have hpf := congrArg Prod.fst hp
  have hpt := congrArg Prod.snd hp
  change min (rootEvidence alpha μ actions false) (rootEvidence alpha μ actions true) = _
  unfold rootEvidence rootExponent
  cases hd : d N
  · simp only [parity, hd, Prod.fst, Prod.snd, decide_eq_false_iff_not] at hpf hpt
    have hf : (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2 = N := by omega
    have ht : sideCount actions false / 2 + sideCount actions true / 2 = N := by omega
    simp [evenRisk, hf, ht]
  · simp only [parity, hd, Prod.fst, Prod.snd, decide_eq_true_eq] at hpf hpt
    have hf : (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2 = N + 1 := by omega
    have ht : sideCount actions false / 2 + sideCount actions true / 2 = N - 1 := by omega
    simp [evenRisk, hf, ht]

private theorem shape_risk_odd {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) :
    marginalError (shapePolicy d) (forcedRootDecoder alpha μ (replay d (2 * N + 1))) ν alpha μ (2 * N + 1) =
      minimumRisk alpha μ (2 * N + 1) := by
  rw [actual_shape_risk]
  let actions := replay d (2 * N + 1)
  have hlen : actions.length = 2 * N + 1 := zero_replay_length _ _ _
  have hcounts : sideCount actions false + sideCount actions true = 2 * N + 1 := by
    simpa [sideCount, hlen] using List.count_false_add_count_true actions
  have hf : (sideCount actions false + 1) / 2 + (sideCount actions true + 1) / 2 = N + 1 := by omega
  have ht : sideCount actions false / 2 + sideCount actions true / 2 = N := by omega
  change min (rootEvidence alpha μ actions false) (rootEvidence alpha μ actions true) = _
  simp [rootEvidence, rootExponent, minimumRisk, hf, ht, show (2 * N + 1) / 2 = N by omega]

/-- Only earlier even depths affect cost; the terminal even shape affects risk alone. -/
def OptimalShapes (alpha : unitInterval) (μ : Measure unitInterval) (n : ℕ) (d : ℕ → Bool) : Prop :=
  (∀ m, 1 ≤ m → 2 * m < n →
    (if d m then coefficient alpha μ m else 0) = min 0 (coefficient alpha μ m)) ∧
  (0 < n → n % 2 = 0 → evenRisk alpha μ (n / 2) (d (n / 2)) = minimumRisk alpha μ n)

private theorem optimal_shapes_exist (alpha : unitInterval) (μ : Measure unitInterval)
    [IsProbabilityMeasure μ] (n : ℕ) : ∃ d, OptimalShapes alpha μ n d := by
  classical
  let terminal : Bool := decide (evenRisk alpha μ (n / 2) true < evenRisk alpha μ (n / 2) false)
  let d (m : ℕ) : Bool :=
    if 2 * m = n then terminal else decide (coefficient alpha μ m < 0)
  refine ⟨d, ?_, ?_⟩
  · intro m hm hmn
    have hne : 2 * m ≠ n := by omega
    by_cases hv : coefficient alpha μ m < 0
    · simp [d, hne, hv, min_eq_right hv.le]
    · simp [d, hne, hv, min_eq_left (le_of_not_gt hv)]
  · intro hn he
    have hN : 1 ≤ n / 2 := by omega
    have hne : 2 * (n / 2) = n := by omega
    have hmin := even_risk_minimum alpha μ (n / 2) hN
    rw [hne] at hmin
    dsimp [d]
    rw [if_pos hne]
    by_cases ht : evenRisk alpha μ (n / 2) true < evenRisk alpha μ (n / 2) false
    · simpa [terminal, ht, min_eq_right ht.le] using hmin
    · simpa [terminal, ht, min_eq_left (le_of_not_gt ht)] using hmin

private theorem shape_mean_optimal {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (n : ℕ) (hd : OptimalShapes alpha μ n d) :
    cappedMean (shapePolicy d) ν alpha μ n = minimumMean alpha μ n := by
  have hcor : correction (shapePolicy d) ν alpha μ ((n - 1) / 2) =
      ∑ j ∈ Finset.range ((n - 1) / 2), min 0 (coefficient alpha μ (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have he := hd.1 (j + 1) (by omega) (by omega)
    rw [shape_lambda d ν (j + 1) (by omega)]
    cases h : d (j + 1) <;> simpa [h] using he
  by_cases hn : n = 0
  · subst n
    simp [minimumMean, cappedMean, actualQueryCount, actualRun]
  · by_cases he : n % 2 = 0
    · have hN : 1 ≤ n / 2 := by omega
      have hne : n = 2 * (n / 2) := by omega
      have hc : (n - 1) / 2 = n / 2 - 1 := by omega
      rw [hc] at hcor
      rw [hne, (mean_formulas (shapePolicy d) ν alpha μ).2 _ hN, minimum_even _ _ _ hN, hcor]
    · have hne : n = 2 * (n / 2) + 1 := by omega
      have hc : (n - 1) / 2 = n / 2 := by omega
      rw [hc] at hcor
      rw [hne, (mean_formulas (shapePolicy d) ν alpha μ).1, minimum_odd, hcor]

private theorem shape_risk_optimal {Seed : Type*} [MeasurableSpace Seed]
    (d : ℕ → Bool) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (alpha : unitInterval) (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (n : ℕ) (hd : OptimalShapes alpha μ n d) :
    marginalError (shapePolicy d) (forcedRootDecoder alpha μ (replay d n)) ν alpha μ n =
      minimumRisk alpha μ n := by
  by_cases hn : n = 0
  · subst n
    rw [actual_shape_risk]
    simp [replay, zeroReplay, rootEvidence, rootExponent, sideCount, moment_zero, minimumRisk]
  · by_cases he : n % 2 = 0
    · have hN : 1 ≤ n / 2 := by omega
      have hne : n = 2 * (n / 2) := by omega
      have hr := shape_risk_even d ν alpha μ (n / 2) hN
      rw [← hne] at hr
      exact hr.trans (hd.2 (by omega) he)
    · have hne : n = 2 * (n / 2) + 1 := by omega
      rw [hne]
      exact shape_risk_odd d ν alpha μ (n / 2)

/-- One original-history execution and one measurable root decoder attain both coordinates. -/
def JointAttains {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy Seed) (decode : State → Bool) (ν : Measure Seed)
    (alpha : unitInterval) (μ : Measure unitInterval) (n : ℕ) : Prop :=
  Measurable decode ∧ cappedMean policy ν alpha μ n = minimumMean alpha μ n ∧
    marginalError policy decode ν alpha μ n = minimumRisk alpha μ n

/-- Every finite horizon has its own joint attainer; all admissible shape choices coexist. -/
theorem result {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (a : ℝ) (b : unitInterval) (ha : 0 < a) (hb : 0 < (b : ℝ)) (hab : a + (b : ℝ) = 1)
    (μ : Measure unitInterval) [IsProbabilityMeasure μ]
    (hQ : ∀ᵐ (q : unitInterval) ∂μ, 0 < (q : ℝ) ∧ (q : ℝ) < 1) :
    (∀ n, ∃ (policy : Policy Seed) (decode : State → Bool), JointAttains policy decode ν b μ n) ∧
    (∀ n d, OptimalShapes b μ n d →
      ∃ (policy : Policy Seed) (decode : State → Bool), JointAttains policy decode ν b μ n ∧
        ∀ (seed : Seed) m, 1 ≤ m → parity (zeroReplay policy seed (2 * m)) = (d m, d m)) ∧
    (∀ (policy : Policy Seed) n, minimumMean b μ n ≤ cappedMean policy ν b μ n) ∧
    minimumMean b μ 0 = 0 ∧ minimumMean b μ 1 = 1 ∧
    (∀ N, 1 ≤ N →
      minimumMean b μ (2 * N) = 2 * momentSum μ N - a + a * moment μ N +
        ∑ j ∈ Finset.range (N - 1), min 0 (coefficient b μ (j + 1)) ∧
      minimumMean b μ (2 * N + 1) = 2 * momentSum μ N - a + (1 + a) * moment μ N +
        ∑ j ∈ Finset.range N, min 0 (coefficient b μ (j + 1))) ∧
    minimumRisk b μ 0 = min a (b : ℝ) ∧
    (∀ N, minimumRisk b μ (2 * N + 1) =
      min (a * moment μ (N + 1)) ((b : ℝ) * moment μ N)) ∧
    (∀ N, 1 ≤ N → minimumRisk b μ (2 * N) =
      min (a * moment μ (N + 1)) ((b : ℝ) * moment μ N)) ∧
    (∀ m, 1 ≤ m → coefficient b μ m =
      (b : ℝ) * (moment μ (m - 1) - moment μ m) - a * (moment μ m - moment μ (m + 1))) := by
  have haeq : 1 - (b : ℝ) = a := by linarith
  have hb2 : 2 - (b : ℝ) = 1 + a := by linarith
  have hshape (n : ℕ) (d : ℕ → Bool) (hd : OptimalShapes b μ n d) :
      ∃ (policy : Policy Seed) (decode : State → Bool), JointAttains policy decode ν b μ n ∧
        ∀ (seed : Seed) m, 1 ≤ m → parity (zeroReplay policy seed (2 * m)) = (d m, d m) := by
    refine ⟨shapePolicy d, forcedRootDecoder b μ (replay d n), ?_, ?_⟩
    · exact ⟨measurable_of_countable _, shape_mean_optimal d ν b μ n hd,
        shape_risk_optimal d ν b μ n hd⟩
    · intro seed m hm
      exact prescribed_even_parity d seed m hm
  refine ⟨?_, hshape, fun policy n => mean_lower policy ν b μ n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨d, hd⟩ := optimal_shapes_exist b μ n
    obtain ⟨policy, decode, hj, _⟩ := hshape n d hd
    exact ⟨policy, decode, hj⟩
  · simp [minimumMean]
  · rw [show (1 : ℕ) = 2 * 0 + 1 by omega, minimum_odd]
    simp [oddBase, momentSum, moment_zero]
    <;> norm_num
  · intro N hN
    constructor
    · rw [minimum_even b μ N hN]
      simp only [evenBase, haeq]
    · rw [minimum_odd]
      simp only [oddBase, haeq, hb2]
  · simp [minimumRisk, haeq]
  · intro N
    simp [minimumRisk, haeq, show (2 * N + 1) / 2 = N by omega]
  · intro N hN
    simp [minimumRisk, haeq, show 2 * N ≠ 0 by omega]
  · intro m hm
    simpa only [haeq] using coefficient_moments b μ m hm

end D5.S3.Observer.ProbabilisticClosure.FiniteHorizonJointAttainment

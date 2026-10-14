/- GID: D5/S1/Dynamics/Shadowing/ProductMetricCounterexample
   generality: I
   mirror-B: D5/B/S1/Dynamics/Shadowing/ProductMetricCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.product_metric_stability; result=D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.result; claim=D5/S1/Dynamics/Shadowing/ProductMetricCounterexample.product_metric_stability
   digest: A uniform product-metric change preserves full shadowing and destroys Lipschitz shadowing. -/

import D5.S1.Dynamics.Shadowing.HeadWeightedMetric
import Mathlib.Analysis.SpecificLimits.Basic

open Function Set Filter Topology
open scoped Uniformity

noncomputable section

namespace D5.S1.Dynamics.Shadowing.ProductMetricCounterexample

abbrev X := ℕ → ℕ
abbrev σ : X → X := SymbolicDynamics.FullShift.shift (1 : ℕ)

def a (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
def b (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n * n)

private theorem a_positive (n : ℕ) : 0 < a n := by unfold a; positivity
private theorem b_positive (n : ℕ) : 0 < b n := by unfold b; positivity
private theorem a_antitone : Antitone a :=
  pow_right_anti₀ (by norm_num) (by norm_num)
private theorem b_antitone : Antitone b := by
  intro m n h
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul h h)
private theorem b_le_a (n : ℕ) : b n ≤ a n := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  nlinarith
private theorem a_le_one (n : ℕ) : a n ≤ 1 := by
  simpa only [a, pow_zero] using a_antitone (Nat.zero_le n)

/-- The preferred head 1 has geometric weights; all other heads have quadratic-exponent weights. -/
def weights : HeadWeights where
  weight := fun s n => if s = 1 then a n else b n
  positive := by
    intro s n
    split_ifs
    · exact a_positive n
    · exact b_positive n
  antitone := by
    intro s
    by_cases h : s = 1 <;> simp only [h, ↓reduceIte]
    · exact a_antitone
    · exact b_antitone
  initial := by intro s; simp [a, b]

def bounds : weights.UniformBounds where
  lower := b
  lower_positive := b_positive
  lower_le := by
    intro s n
    simp only [weights]
    split_ifs
    · exact b_le_a n
    · exact le_rfl
  upper := a
  le_upper := by
    intro s n
    simp only [weights]
    split_ifs
    · exact le_rfl
    · exact b_le_a n
  upper_small := by
    intro ε hε
    exact exists_pow_lt_of_lt_one hε (by norm_num)

/-- An actual MetricSpace on the entire countably infinite full product. -/
@[instance_reducible] def metric : MetricSpace X := bounds.metric

local instance : MetricSpace X := metric

open Classical in
/-- The displayed two-branch distance, including the explicit zero diagonal. -/
theorem distance_formula (x y : X) :
    dist x y = if x = y then 0 else
      if x 0 = 1 ∧ y 0 = 1 then a (PiNat.firstDiff x y) else b (PiNat.firstDiff x y) := by
  classical
  change weights.distance x y = _
  by_cases he : x = y
  · simp [HeadWeights.distance, he]
  rw [weights.distance_of_ne he, if_neg he]
  by_cases hx : x 0 = 1
  · by_cases hy : y 0 = 1
    · simp [weights, hx, hy]
    · have hh : x 0 ≠ y 0 := by omega
      have hn : PiNat.firstDiff x y = 0 := by
        by_contra hn
        exact hh (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hn))
      simp [weights, hx, hy, hn, a, b]
  · simp [weights, hx]

/-- Global sandwich bounds on all distinct pairs; equality is separately zero. -/
theorem distance_bounds {x y : X} (hne : x ≠ y) :
    b (PiNat.firstDiff x y) ≤ dist x y ∧ dist x y ≤ a (PiNat.firstDiff x y) := by
  change b _ ≤ weights.distance x y ∧ weights.distance x y ≤ a _
  rw [weights.distance_of_ne hne]
  exact ⟨bounds.lower_le _ _, bounds.le_upper _ _⟩

theorem strong_triangle (x y z : X) : dist x z ≤ max (dist x y) (dist y z) :=
  weights.distance_ultra x y z

/-- Both identity maps compare actual metric-derived uniform structures. -/
theorem uniform_identities :
    @UniformContinuous X X metric.toUniformSpace PiNat.metricSpaceNatNat.toUniformSpace id ∧
    @UniformContinuous X X PiNat.metricSpaceNatNat.toUniformSpace metric.toUniformSpace id := by
  constructor <;> exact uniformContinuous_id

theorem product_uniformity : metric.toUniformSpace = Pi.uniformSpace (fun _ : ℕ => ℕ) :=
  bounds.metric_uniformSpace
theorem product_topology : metric.toUniformSpace.toTopologicalSpace = Pi.topologicalSpace :=
  bounds.metric_topology

/-- Arbitrary positive accuracy and an entire infinite pseudo-orbit. -/
theorem hasShadowing : MetricHasShadowing σ := bounds.metric_hasShadowing

theorem uniformHasShadowing : UniformHasShadowing σ :=
  (metric_shadowing_iff_uniform σ).mp hasShadowing

private theorem quadratic_gap {N : ℕ} (hN : 4 ≤ N) : b (N - 1) ≤ (a N) ^ 2 := by
  unfold a b
  rw [← pow_mul]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have he : N - 1 + 1 = N := Nat.sub_add_cancel (by omega)
  nlinarith

/-- Geometric decay provides the required large index for every pair of positive constants. -/
private theorem choose_index {L δ₀ : ℝ} (hL : 0 < L) (hδ₀ : 0 < δ₀) :
    ∃ N : ℕ, 4 ≤ N ∧ 2 * b (N - 1) ≤ δ₀ ∧ L * (2 * b (N - 1)) < a N := by
  have he : 0 < min (δ₀ / 2) (1 / (2 * L)) := by positivity
  obtain ⟨K, hK⟩ : ∃ K : ℕ, a K < min (δ₀ / 2) (1 / (2 * L)) :=
    exists_pow_lt_of_lt_one he (by norm_num)
  let N := K + 4
  have hN : 4 ≤ N := by omega
  have hsmall := (a_antitone (show K ≤ N by omega)).trans_lt hK
  have hcut : a N < δ₀ / 2 := hsmall.trans_le (min_le_left _ _)
  have hscale : a N < 1 / (2 * L) := hsmall.trans_le (min_le_right _ _)
  have hq := quadratic_gap hN
  have ha := a_positive N
  have hone := a_le_one N
  have hsq : (a N) ^ 2 ≤ a N := by nlinarith
  have hd : 2 * b (N - 1) ≤ δ₀ := by nlinarith
  have hr : a N * (2 * L) < 1 := (lt_div_iff₀ (by positivity)).mp hscale
  have hm := mul_lt_mul_of_pos_right hr ha
  have hb := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2 * L by positivity)
  refine ⟨N, hN, hd, ?_⟩
  nlinarith

/-- Every positive L and cutoff admit a positive control and a full bad orbit. -/
theorem bad_pseudoOrbit (L δ₀ : ℝ) (hL : 0 < L) (hδ₀ : 0 < δ₀) :
    ∃ δ, 0 < δ ∧ δ ≤ δ₀ ∧ ∃ z : ℕ → X,
      MetricPseudoOrbit σ δ z ∧ ∀ y, ¬ MetricTraces σ (L * δ) z y := by
  obtain ⟨N, hN, hcut, hscale⟩ := choose_index hL hδ₀
  let δ := 2 * b (N - 1)
  have hδ : 0 < δ := by dsimp [δ]; exact mul_pos (by norm_num) (b_positive _)
  refine ⟨δ, hδ, hcut, HeadWeights.defectOrbit 1 0 N, ?_, ?_⟩
  · apply weights.defect_pseudoOrbit 1 0 N (by decide)
    change b (N - 1) < 2 * b (N - 1)
    linarith [b_positive (N - 1)]
  · intro y
    apply weights.defect_no_tracer 1 0 N (by decide) (by omega) (y := y)
    change L * δ ≤ a N
    exact hscale.le

theorem not_lipschitzShadowing : ¬ HasLipschitzShadowing σ := by
  rintro ⟨L, hL, δ₀, hδ₀, ht⟩
  obtain ⟨δ, hδ, hcut, z, hz, hbad⟩ := bad_pseudoOrbit L δ₀ hL hδ₀
  obtain ⟨y, hy⟩ := ht δ hδ hcut z hz
  exact hbad y hy

/-- Literal uniform-metric stability question for the natural full product shift. -/
def product_metric_stability : Prop :=
  ∀ m : MetricSpace X,
    (@UniformContinuous X X m.toUniformSpace PiNat.metricSpaceNatNat.toUniformSpace id ∧
     @UniformContinuous X X PiNat.metricSpaceNatNat.toUniformSpace m.toUniformSpace id) →
    @MetricHasShadowing X m.toPseudoMetricSpace σ →
    @HasLipschitzShadowing X m.toPseudoMetricSpace σ

/-- A negative answer on N^N. No local compactness assertion is made. -/
theorem result : ¬ product_metric_stability := by
  intro h
  exact not_lipschitzShadowing (h metric uniform_identities hasShadowing)

open Classical in
/-- The complete concrete certificate: exact geometry, product structures and all tracing claims. -/
theorem metric_change_counterexample :
    (∀ x y : X, dist x y = if x = y then 0 else
      if x 0 = 1 ∧ y 0 = 1 then a (PiNat.firstDiff x y) else b (PiNat.firstDiff x y)) ∧
    (∀ x y : X, x ≠ y →
      b (PiNat.firstDiff x y) ≤ dist x y ∧ dist x y ≤ a (PiNat.firstDiff x y)) ∧
    (∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)) ∧
    (@UniformContinuous X X metric.toUniformSpace PiNat.metricSpaceNatNat.toUniformSpace id ∧
      @UniformContinuous X X PiNat.metricSpaceNatNat.toUniformSpace metric.toUniformSpace id) ∧
    metric.toUniformSpace = Pi.uniformSpace (fun _ : ℕ => ℕ) ∧
    metric.toUniformSpace.toTopologicalSpace = Pi.topologicalSpace ∧
    Continuous σ ∧ UniformHasShadowing σ ∧
    @MetricHasShadowing X PiNat.metricSpaceNatNat.toPseudoMetricSpace σ ∧
    @HasLipschitzShadowing X PiNat.metricSpaceNatNat.toPseudoMetricSpace σ ∧
    MetricHasShadowing σ ∧ ¬ HasLipschitzShadowing σ := by
  exact ⟨distance_formula, fun _ _ h => distance_bounds h, strong_triangle,
    uniform_identities, product_uniformity, product_topology,
    SymbolicDynamics.FullShift.continuous_shift 1, uniformHasShadowing,
    @HasLipschitzShadowing.metricHasShadowing X
      PiNat.metricSpaceNatNat.toPseudoMetricSpace σ standard_product_lipschitzShadowing,
    standard_product_lipschitzShadowing, hasShadowing, not_lipschitzShadowing⟩

#print axioms bad_pseudoOrbit
#print axioms not_lipschitzShadowing
#print axioms result
#print axioms metric_change_counterexample

end D5.S1.Dynamics.Shadowing.ProductMetricCounterexample

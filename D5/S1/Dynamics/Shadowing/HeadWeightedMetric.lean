/- GID: D5/S1/Dynamics/Shadowing/HeadWeightedMetric
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/HeadWeightedMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Head-dependent prefix ultrametrics with uniform product bounds and infinite shadowing. -/

import D5.S1.Dynamics.Shadowing.MetricTracing
import Mathlib.Topology.MetricSpace.PiNat

open Function Set Filter Topology
open scoped Uniformity

noncomputable section

namespace D5.S1.Dynamics.Shadowing

/-- Positive nonincreasing weights, allowed to depend on the first symbol. -/
structure HeadWeights where
  weight : ℕ → ℕ → ℝ
  positive : ∀ s n, 0 < weight s n
  antitone : ∀ s, Antitone (weight s)
  initial : ∀ s, weight s 0 = 1

namespace HeadWeights

abbrev Space := ℕ → ℕ

/-- The explicit zero clause is essential because firstDiff defaults to zero on equality. -/
def distance (w : HeadWeights) (x y : Space) : ℝ := by
  classical
  exact if x = y then 0 else w.weight (x 0) (PiNat.firstDiff x y)

private theorem firstDiff_zero_of_head_ne {x y : Space} (h : x 0 ≠ y 0) :
    PiNat.firstDiff x y = 0 := by
  by_contra hn
  exact h (PiNat.apply_eq_of_lt_firstDiff (Nat.pos_of_ne_zero hn))

@[simp] theorem distance_self (w : HeadWeights) (x : Space) : w.distance x x = 0 := by
  classical
  simp [distance]

theorem distance_of_ne (w : HeadWeights) {x y : Space} (h : x ≠ y) :
    w.distance x y = w.weight (x 0) (PiNat.firstDiff x y) := by
  classical
  simp [distance, h]

theorem distance_of_head_ne (w : HeadWeights) {x y : Space} (h : x 0 ≠ y 0) :
    w.distance x y = 1 := by
  have hn : x ≠ y := fun e => h (congrFun e 0)
  rw [w.distance_of_ne hn, firstDiff_zero_of_head_ne h, w.initial]

theorem distance_nonneg (w : HeadWeights) (x y : Space) : 0 ≤ w.distance x y := by
  classical
  by_cases h : x = y
  · simp [distance, h]
  · rw [w.distance_of_ne h]; exact (w.positive _ _).le

theorem distance_le_one (w : HeadWeights) (x y : Space) : w.distance x y ≤ 1 := by
  classical
  by_cases h : x = y
  · simp [distance, h]
  · rw [w.distance_of_ne h, ← w.initial (x 0)]
    exact w.antitone _ (Nat.zero_le _)

theorem distance_comm (w : HeadWeights) (x y : Space) :
    w.distance x y = w.distance y x := by
  classical
  by_cases he : x = y
  · subst y; rfl
  by_cases hh : x 0 = y 0
  · rw [w.distance_of_ne he, w.distance_of_ne (Ne.symm he), PiNat.firstDiff_comm, hh]
  · rw [w.distance_of_head_ne hh, w.distance_of_head_ne (Ne.symm hh)]

/-- Mixed-head triples have a unit comparison edge; common-head triples use firstDiff's minimum. -/
theorem distance_ultra (w : HeadWeights) (x y z : Space) :
    w.distance x z ≤ max (w.distance x y) (w.distance y z) := by
  classical
  by_cases hxz : x = z
  · subst z
    exact (w.distance_self x).symm ▸ (w.distance_nonneg x y).trans (le_max_left _ _)
  by_cases hxy : x = y
  · subst y; exact le_max_right _ _
  by_cases hyz : y = z
  · subst z; exact le_max_left _ _
  by_cases hhxy : x 0 = y 0
  · by_cases hhyz : y 0 = z 0
    · rw [w.distance_of_ne hxz, w.distance_of_ne hxy, w.distance_of_ne hyz, ← hhxy]
      rcases min_le_iff.mp (PiNat.min_firstDiff_le x y z hxz) with h | h
      · exact (w.antitone _ h).trans (le_max_left _ _)
      · exact (w.antitone _ h).trans (le_max_right _ _)
    · rw [w.distance_of_head_ne hhyz]
      exact (w.distance_le_one x z).trans (le_max_right _ _)
  · rw [w.distance_of_head_ne hhxy]
    exact (w.distance_le_one x z).trans (le_max_left _ _)

/-- An actual metric, before alignment with the product uniform structure. -/
@[instance_reducible] def rawMetric (w : HeadWeights) : MetricSpace Space where
  dist := w.distance
  dist_self := w.distance_self
  dist_comm := w.distance_comm
  dist_triangle := fun x y z => (w.distance_ultra x y z).trans
    (max_le_add_of_nonneg (w.distance_nonneg x y) (w.distance_nonneg y z))
  eq_of_dist_eq_zero := by
    intro x y h
    classical
    by_contra hn
    rw [w.distance_of_ne hn] at h
    exact (ne_of_gt (w.positive _ _)) h

/-- A strict weight bound forces all coordinates through N to agree, for one head. -/
theorem agree_of_distance_lt_weight (w : HeadWeights) {x y : Space} (N : ℕ)
    (hd : w.distance x y < w.weight (x 0) N) :
    ∀ j ≤ N, x j = y j := by
  classical
  by_cases he : x = y
  · subst y; exact fun _ _ => rfl
  have hn : N < PiNat.firstDiff x y := by
    by_contra hn
    have hb := w.antitone (x 0) (Nat.le_of_not_gt hn)
    rw [← w.distance_of_ne he] at hb
    exact (not_lt_of_ge hb) hd
  exact fun j hj => PiNat.apply_eq_of_lt_firstDiff (hj.trans_lt hn)

/-- Uniform lower bounds convert a strict error threshold into a closed prefix agreement. -/
theorem agree_of_distance_lt_lower (w : HeadWeights) (lower : ℕ → ℝ)
    (hl : ∀ s n, lower n ≤ w.weight s n) {x y : Space} (N : ℕ)
    (hd : w.distance x y < lower N) : ∀ j ≤ N, x j = y j := by
  classical
  by_cases he : x = y
  · subst y; exact fun _ _ => rfl
  have hn : N < PiNat.firstDiff x y := by
    by_contra hn
    have hb := (hl (x 0) N).trans (w.antitone (x 0) (Nat.le_of_not_gt hn))
    rw [← w.distance_of_ne he] at hb
    exact (not_lt_of_ge hb) hd
  exact fun j hj => PiNat.apply_eq_of_lt_firstDiff (hj.trans_lt hn)

/-- A common prefix has a uniform tail bound, independently of its first symbol. -/
theorem distance_le_upper_of_prefix (w : HeadWeights) (upper : ℕ → ℝ)
    (hu : ∀ s n, w.weight s n ≤ upper n) (hu₀ : ∀ n, 0 ≤ upper n)
    {x y : Space} (N : ℕ) (hp : ∀ j < N, x j = y j) :
    w.distance x y ≤ upper N := by
  classical
  by_cases he : x = y
  · subst y; rw [w.distance_self]; exact hu₀ N
  have hn : N ≤ PiNat.firstDiff x y :=
    (PiNat.mem_cylinder_iff_le_firstDiff he N).mp hp
  rw [w.distance_of_ne he]
  exact (w.antitone _ hn).trans (hu _ _)

/-- Fixed-index positive lower bounds and uniformly vanishing upper tails. -/
structure UniformBounds (w : HeadWeights) where
  lower : ℕ → ℝ
  lower_positive : ∀ n, 0 < lower n
  lower_le : ∀ s n, lower n ≤ w.weight s n
  upper : ℕ → ℝ
  le_upper : ∀ s n, w.weight s n ≤ upper n
  upper_small : ∀ ε > 0, ∃ N, upper N < ε

namespace UniformBounds

variable {w : HeadWeights} (b : w.UniformBounds)

include b

theorem upper_positive (N : ℕ) : 0 < b.upper N :=
  (w.positive 0 N).trans_le (b.le_upper 0 N)

/-- The raw weighted metric maps uniformly to the actual standard product metric. -/
theorem uniformContinuous_to_product :
    @UniformContinuous Space Space w.rawMetric.toUniformSpace
      PiNat.metricSpaceNatNat.toUniformSpace id := by
  apply (@Metric.uniformContinuous_iff Space Space
    w.rawMetric.toPseudoMetricSpace PiNat.metricSpaceNatNat.toPseudoMetricSpace id).mpr
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε := exists_pow_lt_of_lt_one hε (by norm_num)
  refine ⟨b.lower N, b.lower_positive N, fun {x y} hxy => ?_⟩
  have hp := w.agree_of_distance_lt_lower b.lower b.lower_le N hxy
  exact (PiNat.mem_cylinder_iff_dist_le.mp (fun j hj => hp j hj.le)).trans_lt hN

/-- The standard product metric maps uniformly to the raw weighted metric. -/
theorem uniformContinuous_from_product :
    @UniformContinuous Space Space PiNat.metricSpaceNatNat.toUniformSpace
      w.rawMetric.toUniformSpace id := by
  apply (@Metric.uniformContinuous_iff Space Space
    PiNat.metricSpaceNatNat.toPseudoMetricSpace w.rawMetric.toPseudoMetricSpace id).mpr
  intro ε hε
  obtain ⟨N, hN⟩ := b.upper_small ε hε
  refine ⟨(1 / 2 : ℝ) ^ N, by positivity, fun {x y} hxy => ?_⟩
  have hp : ∀ j < N, x j = y j := fun j hj => PiNat.apply_eq_of_dist_lt hxy hj.le
  exact (w.distance_le_upper_of_prefix b.upper b.le_upper
    (fun n => (b.upper_positive n).le) N hp).trans_lt hN

/-- Equality of the full product and weighted uniform structures. -/
theorem uniformSpace_eq_product :
    w.rawMetric.toUniformSpace = PiNat.metricSpaceNatNat.toUniformSpace := by
  apply le_antisymm
  · exact le_iff_uniformContinuous_id.mpr b.uniformContinuous_to_product
  · exact le_iff_uniformContinuous_id.mpr b.uniformContinuous_from_product

/-- The metric retains the definitionally standard discrete product topology and uniformity. -/
@[instance_reducible] def metric : MetricSpace Space :=
  @MetricSpace.replaceUniformity Space PiNat.metricSpaceNatNat.toUniformSpace w.rawMetric
    (congrArg (fun U : UniformSpace Space => U.uniformity) b.uniformSpace_eq_product.symm)

theorem metric_uniformSpace : b.metric.toUniformSpace = Pi.uniformSpace (fun _ : ℕ => ℕ) := rfl

theorem metric_topology : b.metric.toUniformSpace.toTopologicalSpace =
    Pi.topologicalSpace := rfl

/-- Uniform cylinder overlap gives ordinary shadowing on the whole product. -/
theorem metric_hasShadowing :
    @MetricHasShadowing Space b.metric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := b.upper_small ε hε
  refine ⟨b.lower N, b.lower_positive N, fun z hz => ?_⟩
  have he : ∀ i j, j ≤ N → z i (j + 1) = z (i + 1) j := by
    intro i j hj
    have hh := w.agree_of_distance_lt_lower b.lower b.lower_le N (hz i) j hj
    simpa only [SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using hh
  refine ⟨diagonalSplice z, fun i => ?_⟩
  have hp : ∀ j < N,
      (SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] (diagonalSplice z) j = z i j := by
    intro j hj
    rw [shift_one_iterate_apply]
    exact diagonal_splice_overlap z N he i j (by omega)
  exact (w.distance_le_upper_of_prefix b.upper b.le_upper
    (fun n => (b.upper_positive n).le) N hp).trans_lt hN

end UniformBounds

/-- One marked symbol against a constant background. -/
def spike (p q n : ℕ) : Space := fun j => if j = n then p else q

private theorem firstDiff_constant_spike (p q n : ℕ) (hpq : p ≠ q) :
    PiNat.firstDiff (fun _ => q) (spike p q n) = n := by
  have he : (fun _ : ℕ => q) ≠ spike p q n := by
    intro h
    have hh := congrFun h n
    simp only [spike] at hh
    exact hpq hh.symm
  apply le_antisymm
  · by_contra hn
    have hh := PiNat.apply_eq_of_lt_firstDiff (Nat.lt_of_not_ge hn)
    simp only [spike] at hh
    exact hpq hh.symm
  · apply (PiNat.mem_cylinder_iff_le_firstDiff he n).mp
    intro j hj
    simp [spike, Nat.ne_of_lt hj]

/-- A single erroneous splice followed by an exact infinite orbit. -/
def defectOrbit (p q N : ℕ) : ℕ → Space
  | 0 => spike p q 0
  | i + 1 => (SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] (spike p q (N - 1))

theorem defect_initial_error (w : HeadWeights) (p q N : ℕ) (hpq : p ≠ q) :
    w.distance (SymbolicDynamics.FullShift.shift (1 : ℕ) (defectOrbit p q N 0))
      (defectOrbit p q N 1) = w.weight q (N - 1) := by
  have hs : SymbolicDynamics.FullShift.shift (1 : ℕ) (spike p q 0) = fun _ => q := by
    funext j
    simp [SymbolicDynamics.FullShift.shift_apply, spike]
  have he : (fun _ : ℕ => q) ≠ spike p q (N - 1) := by
    intro he
    have hh := congrFun he (N - 1)
    simp [spike] at hh
    exact hpq hh.symm
  simp only [defectOrbit, iterate_zero, id_eq, hs]
  rw [w.distance_of_ne he, firstDiff_constant_spike p q (N - 1) hpq]

theorem defect_later_error (w : HeadWeights) (p q N i : ℕ) :
    w.distance (SymbolicDynamics.FullShift.shift (1 : ℕ) (defectOrbit p q N (i + 1)))
      (defectOrbit p q N (i + 2)) = 0 := by
  simp only [defectOrbit, iterate_succ_apply', w.distance_self]

/-- An exact formula for every error, including all times after the marked symbol disappears. -/
theorem defect_pseudoOrbit (w : HeadWeights) (p q N : ℕ) (hpq : p ≠ q)
    {δ : ℝ} (hδ : w.weight q (N - 1) < δ) :
    @MetricPseudoOrbit Space w.rawMetric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) δ (defectOrbit p q N) := by
  intro i
  cases i with
  | zero =>
    change w.distance _ _ < δ
    rw [w.defect_initial_error p q N hpq]
    exact hδ
  | succ i =>
    change w.distance _ _ < δ
    rw [w.defect_later_error p q N i]
    exact (w.positive q (N - 1)).trans hδ

/-- Time zero and time N alone rule out a full tracer below the preferred-head weight. -/
theorem defect_no_tracer (w : HeadWeights) (p q N : ℕ) (hpq : p ≠ q) (hN : 2 ≤ N)
    {r : ℝ} (hr : r ≤ w.weight p N) (y : Space) :
    ¬ @MetricTraces Space w.rawMetric.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) r (defectOrbit p q N) y := by
  intro ht
  have hrone : r ≤ 1 := hr.trans (by simpa only [w.initial] using w.antitone p (Nat.zero_le N))
  have hzero : w.distance y (spike p q 0) < r := ht 0
  have hyhead : y 0 = p := by
    by_contra hh
    have hd := w.distance_of_head_ne (x := y) (y := spike p q 0) (by simpa [spike] using hh)
    rw [hd] at hzero
    exact (not_lt_of_ge hrone) hzero
  have hyN : y N = q := by
    have hd : w.distance y (spike p q 0) < w.weight (y 0) N := by
      rw [hyhead]; exact hzero.trans_le hr
    have hh := w.agree_of_distance_lt_weight N hd N le_rfl
    simpa [spike, show N ≠ 0 by omega] using hh
  have hzN : defectOrbit p q N N 0 = p := by
    conv_lhs => arg 4; rw [show N = (N - 1) + 1 by omega]
    rw [defectOrbit, shift_one_iterate_apply]
    simp [spike]
  have hd : w.distance ((SymbolicDynamics.FullShift.shift (1 : ℕ))^[N] y)
      (defectOrbit p q N N) = 1 := by
    apply w.distance_of_head_ne
    rw [shift_one_iterate_apply, Nat.add_zero, hyN, hzN]
    exact hpq.symm
  have hh := ht N
  change w.distance _ _ < r at hh
  rw [hd] at hh
  exact (not_lt_of_ge hrone) hh

#print axioms distance_ultra
#print axioms UniformBounds.uniformSpace_eq_product
#print axioms UniformBounds.metric_hasShadowing

end HeadWeights

/-- Every nonzero diagonal tracing error is less than half the strict edge bound. -/
theorem standard_product_diagonal_traces {δ : ℝ} (hδ : 0 < δ)
    (z : ℕ → ℕ → ℕ)
    (hz : @MetricPseudoOrbit (ℕ → ℕ) PiNat.metricSpaceNatNat.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) δ z) :
    @MetricTraces (ℕ → ℕ) PiNat.metricSpaceNatNat.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) (δ / 2) z (diagonalSplice z) := by
  let := PiNat.metricSpaceNatNat
  intro i
  classical
  by_cases he : (SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] (diagonalSplice z) = z i
  · rw [he, dist_self]; exact half_pos hδ
  let j := PiNat.firstDiff ((SymbolicDynamics.FullShift.shift (1 : ℕ))^[i] (diagonalSplice z)) (z i)
  have hm : diagonalSplice z (i + j) ≠ z i j := by
    simpa only [shift_one_iterate_apply] using PiNat.apply_firstDiff_ne he
  obtain ⟨t, k, _, _, hk, hne⟩ := diagonal_mismatch_edge z i j hm
  have hedge : SymbolicDynamics.FullShift.shift (1 : ℕ) (z t) ≠ z (t + 1) := by
    intro h
    exact hne (by simpa [SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using congrFun h k)
  let m := PiNat.firstDiff (SymbolicDynamics.FullShift.shift (1 : ℕ) (z t)) (z (t + 1))
  have hmk : m ≤ k := by
    by_contra hmk
    have hh := PiNat.apply_eq_of_lt_firstDiff (Nat.lt_of_not_ge hmk)
    exact hne (by simpa [SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using hh)
  have hb : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ (m + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hb' : 2 * (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ m := by
    rw [pow_succ] at hb
    linarith
  have ht := hz t
  rw [PiNat.dist_eq_of_ne hedge] at ht
  rw [PiNat.dist_eq_of_ne he]
  change (1 / 2 : ℝ) ^ j < δ / 2
  change (1 / 2 : ℝ) ^ m < δ at ht
  linarith

/-- The full countably infinite product shift has Lipschitz shadowing with L=1. -/
theorem standard_product_lipschitzShadowing :
    @HasLipschitzShadowing (ℕ → ℕ) PiNat.metricSpaceNatNat.toPseudoMetricSpace
      (SymbolicDynamics.FullShift.shift (1 : ℕ)) := by
  refine ⟨1, by norm_num, 1, by norm_num, fun δ hδ _ z hz => ?_⟩
  refine ⟨diagonalSplice z, fun i => ?_⟩
  have ht := standard_product_diagonal_traces hδ z hz i
  simp only [one_mul]
  exact ht.trans_le (by linarith)

#print axioms HeadWeights.defect_no_tracer
#print axioms standard_product_diagonal_traces
#print axioms standard_product_lipschitzShadowing

end D5.S1.Dynamics.Shadowing

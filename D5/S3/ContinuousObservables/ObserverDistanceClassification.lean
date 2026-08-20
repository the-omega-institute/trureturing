/- GID: D5/S3/ContinuousObservables/ObserverDistanceClassification
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/ObserverDistanceClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Update-leaf separation, cyclic shortest paths, and bounded integer paths classify observer distance. -/

import D5.S3.Observer.MetricGeometry.OrbitConnesDistance
import D5.S3.Observer.MetricGeometry.WindowObserverDistance

open Set
open scoped ENNReal

namespace D5.S3.ContinuousObservables.ObserverDistanceClassification

/- The admissibility predicate is the source cost model: bounded real readouts whose
one-step update defect is at most one. -/
def edgeAdmissible {I : Type*} (tau : Equiv.Perm I) (f : I → ℝ) : Prop :=
  Bornology.IsBounded (Set.range f) ∧
    ∀ i, ‖((f (tau i) : ℂ) - f i)‖ ≤ 1

/- The extended distance is the supremum over the source's admissible readouts. -/
noncomputable def observerDistance {I : Type*} (tau : Equiv.Perm I) (x y : I) : ℝ≥0∞ :=
  ⨆ f : {f : I → ℝ // edgeAdmissible tau f},
    ENNReal.ofReal (dist (f.1 x) (f.1 y))

private theorem scaled_separator_top {I : Type*} (tau : Equiv.Perm I) (x y : I)
    (f : I → ℝ) (hBound : Bornology.IsBounded (Set.range f))
    (hInvariant : ∀ i, f (tau i) = f i) (hSeparate : f x ≠ f y) :
    observerDistance tau x y = ⊤ := by
  classical
  have hdelta : 0 < dist (f x) (f y) := dist_pos.mpr hSeparate
  apply (iSup_eq_top).2
  intro b hb
  have hbne : b ≠ ⊤ := ne_of_lt hb
  obtain ⟨n, hn⟩ := exists_nat_gt (b.toReal / dist (f x) (f y))
  let fn : {f : I → ℝ // edgeAdmissible tau f} :=
    ⟨fun i => (n : ℝ) • f i, by
      constructor
      · rcases (Metric.isBounded_range_iff.mp hBound) with ⟨C, hC⟩
        rw [Metric.isBounded_range_iff]
        refine ⟨‖(n : ℝ)‖ * C, ?_⟩
        intro i j
        simp only [Real.dist_eq]
        simp only [smul_eq_mul]
        rw [show (n : ℝ) * f i - (n : ℝ) * f j =
          (n : ℝ) * (f i - f j) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_left (hC i j) (abs_nonneg _)
      · intro i
        have hEq : (n : ℝ) • f (tau i) = (n : ℝ) • f i := by rw [hInvariant]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [hEq]
        simp⟩
  have hnpos : 0 < (n : ℝ) * dist (f x) (f y) := by
    exact lt_of_le_of_lt ENNReal.toReal_nonneg ((div_lt_iff₀ hdelta).mp hn)
  have hdist : dist (fn.1 x) (fn.1 y) = (n : ℝ) * dist (f x) (f y) := by
    simp only [Real.dist_eq]
    rw [show (n : ℝ) • f x - (n : ℝ) • f y = (n : ℝ) * (f x - f y) by ring,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have hreal : b.toReal < (n : ℝ) * dist (f x) (f y) :=
    (div_lt_iff₀ hdelta).mp hn
  have hgap : b < ENNReal.ofReal (dist (fn.1 x) (fn.1 y)) := by
    rw [hdist, ← ENNReal.ofReal_toReal hbne]
    exact (ENNReal.ofReal_lt_ofReal_iff hnpos).2 hreal
  exact ⟨fn, hgap⟩

private theorem leaf_indicator_bounded {I Leaf : Type*} [DecidableEq Leaf]
    (leaf : I → Leaf) (x : I) :
    Bornology.IsBounded (Set.range (fun i => if leaf i = leaf x then (1 : ℝ) else 0)) := by
  classical
  apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
  rintro _ ⟨i, rfl⟩
  by_cases h : leaf i = leaf x <;> simp [h]

private theorem leaf_indicator_invariant {I Leaf : Type*} [DecidableEq Leaf]
    (tau : Equiv.Perm I) (leaf : I → Leaf)
    (hLeafInvariant : ∀ i, leaf (tau i) = leaf i) (x : I) :
    ∀ i,
      (if leaf (tau i) = leaf x then (1 : ℝ) else 0) =
        (if leaf i = leaf x then (1 : ℝ) else 0) := by
  classical
  intro i
  rw [hLeafInvariant i]

private theorem leaf_indicator_separates {I Leaf : Type*} [DecidableEq Leaf]
    (leaf : I → Leaf) {x y : I} (hDifferent : leaf x ≠ leaf y) :
    (if leaf x = leaf x then (1 : ℝ) else 0) ≠
      (if leaf y = leaf x then (1 : ℝ) else 0) := by
  classical
  simp [hDifferent, Ne.symm hDifferent]

/-- The three source clauses hold together: different update leaves are infinitely far,
finite cyclic leaves recover shortest-path distance, and bounded free integer leaves recover
absolute coordinate distance. -/
theorem permutation_observer_distance_classification
    {I Leaf : Type*} (tau : Equiv.Perm I) (leaf : I → Leaf)
    {x y : I} (hLeafInvariant : ∀ i, leaf (tau i) = leaf i)
    (hDifferent : leaf x ≠ leaf y)
    {M : ℕ} [NeZero M] (a b : ZMod M) (m n : ℤ) :
    observerDistance tau x y = ⊤ ∧
      D5.S3.Observer.MetricGeometry.WindowObserverDistance.windowObserverDistance M a b =
        D5.S3.Observer.MetricGeometry.WindowObserverDistance.windowCycleDist M a b ∧
      D5.S3.Observer.MetricGeometry.OrbitConnesDistance.orbitConnesDistance m n =
        |((n - m : ℤ) : ℝ)| := by
  classical
  have hIndicatorBound := leaf_indicator_bounded leaf x
  let indicator : I → ℝ := fun i => if leaf i = leaf x then 1 else 0
  have hIndicatorInvariant : ∀ i, indicator (tau i) = indicator i := by
    intro i
    exact leaf_indicator_invariant tau leaf hLeafInvariant x i
  have hIndicatorSeparate : indicator x ≠ indicator y := by
    exact leaf_indicator_separates leaf hDifferent
  refine ⟨scaled_separator_top tau x y indicator ?_ hIndicatorInvariant hIndicatorSeparate, ?_, ?_⟩
  · simpa [indicator] using hIndicatorBound
  · exact D5.S3.Observer.MetricGeometry.WindowObserverDistance.window_observer_distance_eq_cycle_distance M a b
  · rw [D5.S3.Observer.MetricGeometry.OrbitConnesDistance.orbit_connes_distance_eq,
      Int.dist_eq, Int.cast_sub, abs_sub_comm]

#print axioms permutation_observer_distance_classification

end D5.S3.ContinuousObservables.ObserverDistanceClassification

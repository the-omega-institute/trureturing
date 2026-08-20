/- GID: D5/S3/Axis/AxisOrbitMap
   generality: I
   mirror-B: D5/B/S3/Axis/AxisOrbitMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two trace recurrences are exactly one orbit of a four-dimensional polynomial map. -/

import D5.S3.Axis.AxisPartialSum

/- Library-search audit trail (2026-08-20):
   * Both recurrences already exist and are applied, not reproved:
     `AxisTraceRecurrence.axisWeight_succ_succ` (weight is multiplicatively Fibonacci) and
     `AxisPartialSum.axisPartialSum_succ_succ` (partial sum splits by highest digit).
   * The source clause also asserts double-exponential convergence of the orbit limit and
     carries numerical certificates (agreement to 2e-16, multiplicative closure PASS).
     Neither is covered here: the certificates are machine-checked numerics in the source,
     and the convergence needs an analytic argument this module does not attempt.
     What is proved is the structural half — that the pair of recurrences is precisely the
     orbit of the stated map, so no separate dynamical law is hiding in the pair.
-/

namespace D5.S3.Axis.AxisOrbitMap

open D5.S3.Axis.AxisTraceRecurrence D5.S3.Axis.AxisPartialSum

/-- The four-dimensional polynomial map of the source clause. -/
def orbitMap : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ × ℝ
  | (w₁, w₀, t₁, t₀) => (w₁ + t₁ * t₀ * w₀, w₁, t₁ * t₀, t₁)

/-- The axis state at depth `K`: the two latest partial sums and the two latest weights. -/
noncomputable def axisState (x y : ℝ) (K : ℕ) : ℝ × ℝ × ℝ × ℝ :=
  (axisPartialSum x y (K + 1), axisPartialSum x y K,
    axisWeight x y (K + 1), axisWeight x y K)

/-- One step of the map is one step of depth: the two recurrences supply one coordinate
each, and the remaining two are shifts. -/
theorem orbitMap_axisState (x y : ℝ) (K : ℕ) :
    orbitMap (axisState x y K) = axisState x y (K + 1) := by
  have hw : axisPartialSum x y (K + 2) =
      axisPartialSum x y (K + 1) + axisWeight x y (K + 2) * axisPartialSum x y K :=
    axisPartialSum_succ_succ x y K
  have ht : axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K :=
    axisWeight_succ_succ x y K
  simp only [orbitMap, axisState, hw, ht]

/-- The state at depth `K` is the `K`-th iterate of the map from the base state. -/
theorem axisState_eq_iterate (x y : ℝ) (K : ℕ) :
    axisState x y K = (orbitMap^[K]) (axisState x y 0) := by
  induction K with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih, orbitMap_axisState]

/-- The pair of trace recurrences is exactly one orbit of the four-dimensional polynomial
map: every depth is an iterate, and the map advances depth by one. -/
theorem trace_recurrences_are_one_orbit (x y : ℝ) :
    (∀ K : ℕ, orbitMap (axisState x y K) = axisState x y (K + 1)) ∧
      ∀ K : ℕ, axisState x y K = (orbitMap^[K]) (axisState x y 0) :=
  ⟨orbitMap_axisState x y, axisState_eq_iterate x y⟩

#print axioms trace_recurrences_are_one_orbit

end D5.S3.Axis.AxisOrbitMap

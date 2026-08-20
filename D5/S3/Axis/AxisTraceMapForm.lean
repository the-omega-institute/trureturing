/- GID: D5/S3/Axis/AxisTraceMapForm
   generality: I
   mirror-B: D5/B/S3/Axis/AxisTraceMapForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The four dimensional trace map has the stated form and carries the axis orbit. -/

import D5.S3.Axis.AxisOrbitMap

namespace D5.S3.Axis.AxisTraceMapForm

open D5.S3.Axis.AxisOrbitMap

/-- The map the source writes out, pinned coordinate by coordinate. Without this the orbit
statement holds of whatever `orbitMap` happens to be defined as; with it the reader can check
the definition against the source line. -/
theorem orbitMap_form (w₁ w₀ t₁ t₀ : ℝ) :
    orbitMap (w₁, w₀, t₁, t₀) = (w₁ + t₁ * t₀ * w₀, w₁, t₁ * t₀, t₁) :=
  rfl

/-- The trace map clause packaged: the map has the stated four coordinates, it carries the
axis state one depth forward, and every state is an iterate of the initial one.

The source also records doubly exponential convergence of the orbit, backed there by a
numerical certificate. That half is not claimed here. -/
theorem axis_trace_map_form_package (x y : ℝ) :
    (∀ w₁ w₀ t₁ t₀ : ℝ,
        orbitMap (w₁, w₀, t₁, t₀) = (w₁ + t₁ * t₀ * w₀, w₁, t₁ * t₀, t₁)) ∧
      (∀ K : ℕ, orbitMap (axisState x y K) = axisState x y (K + 1)) ∧
        ∀ K : ℕ, axisState x y K = (orbitMap^[K]) (axisState x y 0) :=
  ⟨orbitMap_form, (trace_recurrences_are_one_orbit x y).1,
    (trace_recurrences_are_one_orbit x y).2⟩

end D5.S3.Axis.AxisTraceMapForm

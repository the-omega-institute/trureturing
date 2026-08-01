/- GID: D5/S0/History/SpliceEquations
   generality: G
   mirror-B: D5/B/S0/History/SpliceEquations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The defining recursion of marker-history splicing, with a two-marker witness. -/

import D5.S0.History.HistoryCarrier

namespace D5.S0.History

/-- Splicing is fixed by its recursion on the second argument: the empty history acts as
the right unit, and prefixing a marker there prefixes the same marker on the result.
`splice` is defined through the free-monoid product, so these equations are what pin it
to the intended recursion rather than to an unexplained library alias. -/
theorem splice_recursion_equations :
    (∀ h : MarkerHistory, splice h 1 = h) ∧
      (∀ (ε : Marker) (h g : MarkerHistory),
        splice h (FreeMonoid.of ε * g) = FreeMonoid.of ε * splice h g) := by
  refine ⟨fun h => ?_, fun ε h g => ?_⟩
  · simp [splice]
  · simp [splice, mul_assoc]

-- Non-vacuity witness: splicing two one-marker histories yields the expected two-marker
-- history, with the second argument's marker in front.
example :
    splice (FreeMonoid.of Marker.E₀) (FreeMonoid.of Marker.E₁)
      = FreeMonoid.of Marker.E₁ * FreeMonoid.of Marker.E₀ := by
  rfl

end D5.S0.History

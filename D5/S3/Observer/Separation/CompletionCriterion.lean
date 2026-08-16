/- GID: D5/S3/Observer/Separation/CompletionCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/CompletionCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The kernel quotient fills the formal-family space exactly under realizability. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib and Loogle hit `Setoid.quotientKerEquivRange`
     identifies a function-kernel quotient with the function's realized range;
     it is imported and applied below.
   * Exact pinned-Mathlib and Loogle hit
     `Setoid.quotientKerEquivOfSurjective` identifies that quotient with the
     full codomain under realizability; it is imported and applied below.
   * Repository searches found special finite-itinerary and controlled-
     behavior instances, but no theorem stating both clauses for an arbitrary
     observation map.
   * LeanSearch's shaped query endpoint returned HTTP 404. -/

namespace D5.S3.Observer.Separation.CompletionCriterion

/-- The quotient by final observational indistinguishability is canonically
equivalent to the realized observation range. It is canonically equivalent to
the entire formal-family codomain exactly when every family is realized. -/
theorem completion_criterion {X L : Type*} (observe : X -> L) :
    (ExistsUnique fun rangeEquiv :
        Quotient (Setoid.ker observe) ≃ Set.range observe =>
      forall x,
        rangeEquiv (Quotient.mk'' x) = ⟨observe x, ⟨x, rfl⟩⟩) /\
    ((ExistsUnique fun limitEquiv : Quotient (Setoid.ker observe) ≃ L =>
        forall x, limitEquiv (Quotient.mk'' x) = observe x) <->
      forall family : L, exists x : X, observe x = family) := by
  classical
  constructor
  · refine ⟨Setoid.quotientKerEquivRange observe, ?_, ?_⟩
    · intro x
      rfl
    · intro other hother
      apply Equiv.ext
      intro state
      refine Quotient.inductionOn' state ?_
      intro x
      exact (hother x).trans (by rfl)
  · constructor
    · rintro ⟨equiv, hequiv, _⟩ family
      rcases equiv.surjective family with ⟨state, rfl⟩
      refine Quotient.inductionOn' state ?_
      intro x
      exact ⟨x, (hequiv x).symm⟩
    · intro hrealizable
      refine ⟨Setoid.quotientKerEquivOfSurjective observe hrealizable, ?_, ?_⟩
      · intro x
        rfl
      · intro other hother
        apply Equiv.ext
        intro state
        refine Quotient.inductionOn' state ?_
        intro x
        exact (hother x).trans (by rfl)

-- Unit data witnesses that the quantified domain and realizability clause are inhabited.
example : forall family : Unit, exists x : Unit, (id : Unit -> Unit) x = family := by
  intro family
  exact ⟨family, rfl⟩

#print axioms completion_criterion

end D5.S3.Observer.Separation.CompletionCriterion

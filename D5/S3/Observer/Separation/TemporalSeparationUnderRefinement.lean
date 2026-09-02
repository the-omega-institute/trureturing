/- GID: D5/S3/Observer/Separation/TemporalSeparationUnderRefinement
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/TemporalSeparationUnderRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refining a readout shrinks every finite future fiber and cannot
     delay any separation already visible to the coarser observer. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.Observer.Separation.FiniteFutureCongruence
import Mathlib

/-!
Library-first audit:
* `Refines` is the canonical Trueturning factorization order on readouts.
* `observedAt`, `finiteFutureRelation`, and `separationTime` are reused from the
  finite-future congruence owner.
* No parallel temporal fiber or break-depth definition is introduced.

The separation-time inequality is conditional on the coarse observer actually
separating the pair. The canonical `separationTime` returns zero when no
separation exists, so that case cannot carry the same order interpretation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Separation.TemporalSeparationUnderRefinement

open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.Observer.Separation.FiniteFutureCongruence

/-- Every finite future fiber of a finer readout is contained in the
corresponding fiber of a coarser factor readout. -/
theorem finite_future_relation_mono_of_refines
    {State Coarse Fine : Type*}
    (update : State → State) (coarse : State → Coarse)
    (fine : State → Fine) (hRefines : Refines coarse fine)
    (horizon : ℕ) :
    finiteFutureRelation update fine horizon ≤
      finiteFutureRelation update coarse horizon := by
  rcases hRefines with ⟨factor, hFactor⟩
  intro pair hFine time hTime
  have hAt := hFine time hTime
  simpa [observedAt, hFactor, Function.comp_apply] using
    congrArg factor hAt

/-- If the coarse observer distinguishes a pair at some finite time, then the
finer observer also distinguishes it. -/
theorem coarse_separation_implies_fine_separation
    {State Coarse Fine : Type*}
    (update : State → State) (coarse : State → Coarse)
    (fine : State → Fine) (hRefines : Refines coarse fine)
    (pair : State × State)
    (hCoarse : ∃ time,
      observedAt update coarse time pair.1 ≠
        observedAt update coarse time pair.2) :
    ∃ time,
      observedAt update fine time pair.1 ≠
        observedAt update fine time pair.2 := by
  rcases hRefines with ⟨factor, hFactor⟩
  obtain ⟨time, hTime⟩ := hCoarse
  refine ⟨time, ?_⟩
  intro hFine
  apply hTime
  simpa [observedAt, hFactor, Function.comp_apply] using
    congrArg factor hFine

/-- Observer refinement cannot delay the first separation time of a pair that
is already separable by the coarser observer. -/
theorem separation_time_le_of_refines
    {State Coarse Fine : Type*}
    (update : State → State) (coarse : State → Coarse)
    (fine : State → Fine) (hRefines : Refines coarse fine)
    (pair : State × State)
    (hCoarse : ∃ time,
      observedAt update coarse time pair.1 ≠
        observedAt update coarse time pair.2) :
    separationTime update fine pair ≤
      separationTime update coarse pair := by
  classical
  rcases hRefines with ⟨factor, hFactor⟩
  have hCoarseAt :
      observedAt update coarse (separationTime update coarse pair) pair.1 ≠
        observedAt update coarse (separationTime update coarse pair) pair.2 := by
    simp only [separationTime, dif_pos hCoarse]
    exact Nat.find_spec hCoarse
  have hFineAt :
      observedAt update fine (separationTime update coarse pair) pair.1 ≠
        observedAt update fine (separationTime update coarse pair) pair.2 := by
    intro hFine
    apply hCoarseAt
    simpa [observedAt, hFactor, Function.comp_apply] using
      congrArg factor hFine
  have hFine : ∃ time,
      observedAt update fine time pair.1 ≠
        observedAt update fine time pair.2 :=
    ⟨separationTime update coarse pair, hFineAt⟩
  have hFineAtFind :
      observedAt update fine (Nat.find hCoarse) pair.1 ≠
        observedAt update fine (Nat.find hCoarse) pair.2 := by
    simpa only [separationTime, dif_pos hCoarse] using hFineAt
  simp only [separationTime, dif_pos hFine, dif_pos hCoarse]
  exact Nat.find_min' hFine hFineAtFind

/-- Identity factorization realizes equality in the refinement inequality. -/
example {State Output : Type*} (update : State → State)
    (readout : State → Output) (pair : State × State)
    (hSeparates : ∃ time,
      observedAt update readout time pair.1 ≠
        observedAt update readout time pair.2) :
    separationTime update readout pair ≤
      separationTime update readout pair := by
  exact separation_time_le_of_refines update readout readout
    ⟨id, by funext state; rfl⟩ pair hSeparates

#print axioms finite_future_relation_mono_of_refines
#print axioms coarse_separation_implies_fine_separation
#print axioms separation_time_le_of_refines

end D5.S3.Observer.Separation.TemporalSeparationUnderRefinement

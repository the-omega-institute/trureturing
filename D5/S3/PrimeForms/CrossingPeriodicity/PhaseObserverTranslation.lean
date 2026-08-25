/- GID: D5/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation
   generality: I
   mirror-B: D5/B/S3/PrimeForms/CrossingPeriodicity/PhaseObserverTranslation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The winding-phase observer sends the crossing sandwich to translation by minus two. -/

import D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod
import Mathlib.Topology.Instances.AddCircle.Defs

/- Library-search audit trail (2026-08-24):
   * Exact family hits `PositiveMatrix`, `windingPhase`, and `crossingSandwich` come from
     `WindingOrbitZero`; `Admissible`, `admissible_sandwich`, and the exact displacement
     law `phase_sandwich_step` come from the imported `SandwichPhasePeriod` module.
   * The public theorem applies `phase_sandwich_step` directly. It constructs the source
     update on admissible matrices, the phase observer modulo an arbitrary rational `m`,
     and the target translation `z - 2` inline, rather than naming any object by the goal.
   * Pinned Mathlib provides `Function.Semiconj` and the exact quotient compatibility
     lemma `AddCircle.coe_sub`; simplification applies the latter after the phase law.
   * Repository searches found no existing public semiconjugacy from this phase observer
     to translation modulo arbitrary `m`. The related orbit module contains only a private
     fixed-modulus spelling and has a frozen declaration surface.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverTranslation

open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.Crossing.WindingOrbitZero
open D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod

/-- Reduction of the winding phase modulo `m` sends the admissible crossing-sandwich
update to the explicit translation `z |-> z - 2`. -/
theorem phase_observer_descends_to_translation (m : Rat) :
    Function.Semiconj
      (fun A : {A : PositiveMatrix // Admissible A} =>
        ((windingPhase A.1 : Rat) : AddCircle m))
      (fun A : {A : PositiveMatrix // Admissible A} =>
        ⟨crossingSandwich A.1, admissible_sandwich A.2⟩)
      (fun z : AddCircle m => z - ((2 : Rat) : AddCircle m)) := by
  intro A
  change
    ((windingPhase (crossingSandwich A.1) : Rat) : AddCircle m) =
      ((windingPhase A.1 : Rat) : AddCircle m) - ((2 : Rat) : AddCircle m)
  rw [phase_sandwich_step A.2]
  exact AddCircle.coe_sub m (windingPhase A.1) 2

#print axioms phase_observer_descends_to_translation

end D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverTranslation

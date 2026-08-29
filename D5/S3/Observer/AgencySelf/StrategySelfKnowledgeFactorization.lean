/- GID: D5/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/StrategySelfKnowledgeFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strategy self-knowledge factorization refines the current-state observation kernel. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.AgencySelf.StrategySelfKnowledgeFactorization

universe u v w

/-- When the strategy profile is readable from the current observer state,
current-state equality forces strategy-profile equality. -/
theorem factorization_refines_strategy_kernel
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (factor : Memory -> Profile)
    (factors : forall h, profile h = factor (current h))
    (x y : History) (sameCurrent : current x = current y) :
    profile x = profile y := by
  rw [factors x, factors y, sameCurrent]

/-- A visible strategy profile adds no extra separation to the current-state
readout. -/
theorem visible_profile_pair_equality
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (factor : Memory -> Profile)
    (factors : forall h, profile h = factor (current h))
    (x y : History) (sameCurrent : current x = current y) :
    (current x, profile x) = (current y, profile y) := by
  apply Prod.ext
  · exact sameCurrent
  · exact factorization_refines_strategy_kernel
      current profile factor factors x y sameCurrent

#print axioms factorization_refines_strategy_kernel
#print axioms visible_profile_pair_equality

end D5.S3.Observer.AgencySelf.StrategySelfKnowledgeFactorization

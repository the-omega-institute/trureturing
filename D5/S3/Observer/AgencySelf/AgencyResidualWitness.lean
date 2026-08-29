/- GID: D5/S3/Observer/AgencySelf/AgencyResidualWitness
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/AgencyResidualWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A hidden strategy difference is a concrete witness of agency residual. -/

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

namespace D5.S3.Observer.AgencySelf.AgencyResidualWitness

universe u v w

def AgencyResidual {History : Type u} {Memory : Type v}
    {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History) : Prop :=
  current x = current y ∧ profile x ≠ profile y

/-- Equal current states with unequal strategy profiles witness the part of
history that current-state observation alone cannot identify. -/
theorem hidden_strategy_difference_is_residual
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History)
    (sameCurrent : current x = current y)
    (differentProfile : profile x ≠ profile y) :
    AgencyResidual current profile x y :=
  ⟨sameCurrent, differentProfile⟩

/-- Any residual witness certifies that the paired agency completion separates
a pair collapsed by the current-state readout. -/
theorem residual_separated_by_pair
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History)
    (residual : AgencyResidual current profile x y) :
    (current x, profile x) ≠ (current y, profile y) := by
  intro pairEqual
  exact residual.2 (congrArg Prod.snd pairEqual)

#print axioms hidden_strategy_difference_is_residual
#print axioms residual_separated_by_pair

end D5.S3.Observer.AgencySelf.AgencyResidualWitness

/- GID: D5/S3/Observer/AgencySelf/AgencyResidualDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/AgencySelf/AgencyResidualDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The current-state kernel decomposes into completed and strategy-residual pairs. -/

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

namespace D5.S3.Observer.AgencySelf.AgencyResidualDecomposition

universe u v w

def SameUnder {History : Type u} {Output : Type v}
    (readout : History -> Output) (x y : History) : Prop :=
  readout x = readout y

def CompletionRelated {History : Type u} {Memory : Type v}
    {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History) : Prop :=
  SameUnder current x y ∧ SameUnder profile x y

def AgencyResidual {History : Type u} {Memory : Type v}
    {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History) : Prop :=
  SameUnder current x y ∧ ¬ SameUnder profile x y

/-- Every pair identified by the current-state readout is either identified by
the paired agency completion or lies in the strategy residual. -/
theorem current_relation_decomposition
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History) :
    SameUnder current x y ↔
      CompletionRelated current profile x y ∨
        AgencyResidual current profile x y := by
  constructor
  · intro sameCurrent
    by_cases sameProfile : SameUnder profile x y
    · exact Or.inl ⟨sameCurrent, sameProfile⟩
    · exact Or.inr ⟨sameCurrent, sameProfile⟩
  · intro split
    rcases split with completed | residual
    · exact completed.1
    · exact residual.1

/-- Completed pairs and residual pairs are logically disjoint. -/
theorem completion_residual_exclusive
    {History : Type u} {Memory : Type v} {Profile : Type w}
    (current : History -> Memory) (profile : History -> Profile)
    (x y : History) :
    ¬ (CompletionRelated current profile x y ∧
      AgencyResidual current profile x y) := by
  intro both
  exact both.2.2 both.1.2

#print axioms current_relation_decomposition
#print axioms completion_residual_exclusive

end D5.S3.Observer.AgencySelf.AgencyResidualDecomposition

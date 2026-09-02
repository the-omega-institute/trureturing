/- GID: D5/S0/Certificates/FiniteExhaustion
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteExhaustion
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Finite Boolean search results are reflected into exact universal validity and unsatisfiability statements. -/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Bool.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteExhaustion

universe u

/-- Exhaustively check that a Boolean predicate accepts every point of a finite type. -/
def exhaustiveValidityCheck {α : Type u} [Fintype α] (predicate : α → Bool) : Bool :=
  decide (∀ x, predicate x = true)

/-- Exhaustively check that a Boolean predicate rejects every point of a finite type. -/
def exhaustiveUnsatCheck {α : Type u} [Fintype α] (predicate : α → Bool) : Bool :=
  decide (∀ x, predicate x = false)

/-- The validity checker returns true exactly for universally true predicates. -/
@[simp]
theorem exhaustiveValidityCheck_eq_true_iff {α : Type u} [Fintype α]
    (predicate : α → Bool) :
    exhaustiveValidityCheck predicate = true ↔ ∀ x, predicate x = true := by
  simp [exhaustiveValidityCheck]

/-- The unsatisfiability checker returns true exactly when no finite assignment is accepted. -/
@[simp]
theorem exhaustiveUnsatCheck_eq_true_iff {α : Type u} [Fintype α]
    (predicate : α → Bool) :
    exhaustiveUnsatCheck predicate = true ↔ ∀ x, predicate x = false := by
  simp [exhaustiveUnsatCheck]

/-- A successful finite validity check can be eliminated as an exact universal theorem. -/
theorem valid_of_exhaustive_check {α : Type u} [Fintype α]
    {predicate : α → Bool} (checked : exhaustiveValidityCheck predicate = true) :
    ∀ x, predicate x = true :=
  (exhaustiveValidityCheck_eq_true_iff predicate).1 checked

/-- A successful finite refutation check excludes every satisfying assignment. -/
theorem unsatisfiable_of_exhaustive_check {α : Type u} [Fintype α]
    {predicate : α → Bool} (checked : exhaustiveUnsatCheck predicate = true) :
    ¬ ∃ x, predicate x = true := by
  rintro ⟨x, hx⟩
  have hfalse := (exhaustiveUnsatCheck_eq_true_iff predicate).1 checked x
  simpa [hx] using hfalse

#print axioms exhaustiveValidityCheck_eq_true_iff
#print axioms exhaustiveUnsatCheck_eq_true_iff
#print axioms unsatisfiable_of_exhaustive_check

end D5.S0.Certificates.FiniteExhaustion

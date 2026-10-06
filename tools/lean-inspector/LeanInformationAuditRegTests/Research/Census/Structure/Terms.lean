import Lean

namespace LeanInformationAudit.Tests.Census.Structure

-- Exact five-node contract: a's value has no constants at all.
theorem a : ∀ P : Prop, P → P := fun _ p => p
def h : ∀ P : Prop, P → P := a
theorem b : ∀ P : Prop, P → P := h
theorem c : ∀ P : Prop, P → P := a
theorem d : ∀ P : Prop, P → P := fun P p => b P (c P p)
theorem g : ∀ P : Prop, P → P := b

def aliasHelper : ∀ P : Prop, P → P := a
def substantiveHelper (n : Nat) : Nat := n + 1
theorem viaAlias : ∀ P : Prop, P → P := aliasHelper
theorem viaSubstantive (n : Nat) : substantiveHelper n = n + 1 := rfl

theorem suppliedEquality (P Q : Prop) (e : P = Q) (q : Q) : P := Eq.mpr e q
theorem newEquality : (2 : Nat) + 2 = 4 := rfl
theorem localInstance : True := by
  letI : Decidable True := isTrue True.intro
  exact of_decide_eq_true rfl

-- Untrusted axioms stay readable diagnostics. These are synthetic fixtures.
axiom fixtureAxiom : True
theorem usesAxiom : True := fixtureAxiom
theorem usesSorry : True := by sorry

end LeanInformationAudit.Tests.Census.Structure

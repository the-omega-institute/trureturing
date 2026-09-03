/- GID: D5/S0/Naming/MultiFiltrationNamingSystem
   generality: G
   mirror-B: D5/B/S0/Naming/MultiFiltrationNamingSystem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A primary naming filtration remains finite after imposing a secondary budget. -/

import D5.S0.Naming.NamingSystem

/- Library-search audit trail (2026-09-03):
   * D5 body-shape searches for a naming system with a secondary height and
     joint budget layers found only the single-height `NamingSystem` owner.
   * Pinned Mathlib has generic finite-set subset lemmas but no naming-system
     structure or multi-height filtration structure.
   * GitHub Lean code search for a matching naming-system wrapper returned no
     result. The structure below wraps the frozen Definition 2.1 owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming

open MeasureTheory

universe u v

/-- A two-height naming system has one primary `NamingSystem` and a secondary
height on the very same name carrier. The primary field retains the finite
sublevel proof from the canonical single-height owner. -/
structure MultiFiltrationNamingSystem (X : Type u) [MeasureSpace X] where
  primary : NamingSystem.{u, v} X
  secondaryHeight : primary.Name -> Nat

namespace MultiFiltrationNamingSystem

/-- Names satisfying both a primary and a secondary budget. -/
def jointLayer {X : Type u} [MeasureSpace X]
    (system : MultiFiltrationNamingSystem.{u, v} X)
    (primaryBudget secondaryBudget : Nat) : Set system.primary.Name :=
  {name | system.primary.height name <= primaryBudget /\
    system.secondaryHeight name <= secondaryBudget}

/-- A joint budget layer is finite because it is a subset of its primary
height layer. No finite-sublevel condition is imposed on the secondary height. -/
theorem joint_budget_layer_finite {X : Type u} [MeasureSpace X]
    (system : MultiFiltrationNamingSystem.{u, v} X)
    (primaryBudget secondaryBudget : Nat) :
    Set.Finite (system.jointLayer primaryBudget secondaryBudget) := by
  apply (system.primary.finite_layer primaryBudget).subset
  intro name bounds
  exact bounds.1

#print axioms joint_budget_layer_finite

end MultiFiltrationNamingSystem

end D5.S0.Naming

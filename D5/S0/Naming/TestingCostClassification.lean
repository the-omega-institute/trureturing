/- GID: D5/S0/Naming/TestingCostClassification
   generality: G
   mirror-B: D5/B/S0/Naming/TestingCostClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Code length filters testing names; fixed-size tables defeat execution cost alone. -/

import D5.S0.Naming.Conservation.TestingTowerMembership
import Mathlib.Data.Nat.Log

/- Library-search audit trail (2026-09-03):
   * D5 owns the exact `TestingName` carrier and its finite code-length theorem.
     The generic `ProgramCostFiltration` owner classifies realized program
     functions, not the finite-table-plus-program name carrier used here.
   * Pinned Mathlib supplies `Set.infinite_range_of_injective`,
     `Finset.singleton_injective`, and natural-number order facts.
   * GitHub Lean code search found no exact testing-name cost classification.
     The primary clause below applies the frozen D5 owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.TestingCostClassification

open D5.S0.Naming.Conservation.TestingTowerMembership

universe u

/-- Table lookup cost is modeled by the finite support size; program names use
the supplied execution cost. -/
def testingExecutionCost {Output : Type u} (programCost : Nat -> Nat) :
    TestingName Output -> Nat
  | Sum.inl table => table.1.card
  | Sum.inr program => programCost program

/-- The execution-cost sublevel at one already contains infinitely many tables
with singleton, self-selected supports. -/
theorem fixed_support_execution_sublevel_infinite {Output : Type u}
    (value : Output) (programCost : Nat -> Nat) :
    Set.Infinite {name : TestingName Output |
      testingExecutionCost programCost name <= 1} := by
  let singletonTable : Nat -> TestingName Output := fun index =>
    Sum.inl ⟨({index} : Finset Nat), fun _ => value⟩
  have singletonTableInjective : Function.Injective singletonTable := by
    intro left right equalNames
    have equalTables := Sum.inl.inj equalNames
    have equalSupports : ({left} : Finset Nat) = {right} :=
      congrArg Sigma.fst equalTables
    exact Finset.singleton_injective equalSupports
  apply (Set.infinite_range_of_injective singletonTableInjective).mono
  intro name inRange
  obtain ⟨index, rfl⟩ := inRange
  simp [singletonTable, testingExecutionCost]

/-- On the exact testing-name carrier, description length has finite sublevels,
execution cost alone has an infinite sublevel, and adding logarithmic execution
cost to description length restores finite sublevels. -/
theorem testing_cost_classification {Output : Type u}
    (value : Output)
    (selfDelimitingCode : TestingName Output -> List Bool)
    (codeInjective : Function.Injective selfDelimitingCode)
    (programCost : Nat -> Nat) :
    (forall Q : Nat, Set.Finite {name : TestingName Output |
      (selfDelimitingCode name).length <= Q}) /\
    Set.Infinite {name : TestingName Output |
      testingExecutionCost programCost name <= 1} /\
    (forall Q : Nat, Set.Finite {name : TestingName Output |
      (selfDelimitingCode name).length +
        Nat.log 2 (testingExecutionCost programCost name) <= Q}) := by
  have finiteCodeSublevel : forall Q : Nat, Set.Finite {name : TestingName Output |
      (selfDelimitingCode name).length <= Q} := by
    intro Q
    obtain ⟨primary, finiteSelected⟩ :=
      testing_tower_is_multi_filtration selfDelimitingCode codeInjective
        (fun name => (selfDelimitingCode name).length)
    simpa using finiteSelected Q
  refine ⟨finiteCodeSublevel,
    fixed_support_execution_sublevel_infinite value programCost, ?_⟩
  intro Q
  apply (finiteCodeSublevel Q).subset
  intro name mixedBound
  exact (Nat.le_add_right _ _).trans mixedBound

#print axioms fixed_support_execution_sublevel_infinite
#print axioms testing_cost_classification

end D5.S0.Naming.TestingCostClassification

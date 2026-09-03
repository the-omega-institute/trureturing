/- GID: D5/S0/Naming/TestingTowerStructureMembership
   generality: G
   mirror-B: D5/B/S0/Naming/TestingTowerStructureMembership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The testing tower satisfies all carrier, valuation, and cost-classification clauses. -/

import D5.S0.Naming.MultiFiltrationNamingSystem
import D5.S0.Naming.TestingCostClassification
import D5.S0.Naming.TestingTowerValuation
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/- Library-search audit trail (2026-09-03):
   * D5 searches found the canonical `NamingSystem`, `TestingName`, finite
     code-height owner, and dark-side measure theorem, but no theorem exposing
     all testing-tower membership clauses on one public carrier.
   * Pinned Mathlib supplies the Polish/Borel classes, countability instances,
     universal partial evaluator, halting theorem, and finite/infinite set facts
     used by the imported prerequisites.
   * GitHub Lean code search returned no exact theorem. This result constructs
     the source tower from those canonical primitives and applies each owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Naming.TestingTowerStructureMembership

open MeasureTheory
open D5.S0.Naming
open D5.S0.Naming.Conservation.TestingTowerMembership
open D5.S0.Naming.MultiFiltrationNamingSystem
open D5.S0.Naming.TestingCostClassification
open D5.S0.Naming.TestingTowerValuation

universe u

/-- The source testing tower, constructed on the sequence carrier from its
table/program assignment, injective description code, and two cost heights. -/
noncomputable def testingTower {Output : Type u} [MeasureSpace (Nat -> Output)]
    (defaultOutput : Output) (decodeBehavior : Nat -> Nat -> Output)
    (programInput : Nat)
    (selfDelimitingCode : TestingName Output -> List Bool)
    (codeInjective : Function.Injective selfDelimitingCode)
    (programCost : Nat -> Nat) :
    MultiFiltrationNamingSystem.{u, u} (Nat -> Output) where
  primary :=
    { Name := TestingName Output
      assignment := testingAssignment defaultOutput decodeBehavior programInput
      height := fun name => (selfDelimitingCode name).length
      finite_layer := (testing_cost_classification defaultOutput selfDelimitingCode
        codeInjective programCost).1 }
  secondaryHeight := testingExecutionCost programCost

/-- The testing tower has a finite nontrivial alphabet and an uncountable Polish
sequence carrier with an atomless sigma-finite measure. Its name type is
countable; table names use default extension; program-name definedness is the
noncomputable halting domain; code length is a primary filtration; table
execution cost alone is not; and the mixed cost has finite sublevels. -/
theorem testing_tower_has_multi_filtration_membership
    {Output : Type u} [Finite Output] [Nontrivial Output]
    [TopologicalSpace (Nat -> Output)] [PolishSpace (Nat -> Output)]
    [MeasurableSpace (Nat -> Output)] [BorelSpace (Nat -> Output)]
    [Uncountable (Nat -> Output)]
    (defaultOutput : Output) (decodeBehavior : Nat -> Nat -> Output)
    (programInput : Nat)
    (selfDelimitingCode : TestingName Output -> List Bool)
    (codeInjective : Function.Injective selfDelimitingCode)
    (programCost : Nat -> Nat)
    (μ : Measure (Nat -> Output)) [NullSingletonClass μ] [SigmaFinite μ] :
    letI : MeasureSpace (Nat -> Output) := ⟨μ⟩
    Countable (TestingName Output) /\
    (forall program : Nat,
      (testingAssignment defaultOutput decodeBehavior programInput
        (Sum.inr program)).isSome <->
        (Nat.Partrec.Code.eval
          (Denumerable.ofNat Nat.Partrec.Code program) programInput).Dom) /\
    (¬ ComputablePred (fun code : Nat.Partrec.Code =>
      (testingAssignment defaultOutput decodeBehavior programInput
        (Sum.inr (Nat.Partrec.Code.encodeCode code))).isSome)) /\
    (forall Q : Nat, Set.Finite {name : TestingName Output |
      (selfDelimitingCode name).length <= Q}) /\
    Set.Infinite {name : TestingName Output |
      testingExecutionCost programCost name <= 1} /\
    (forall Q : Nat, Set.Finite {name : TestingName Output |
      (selfDelimitingCode name).length +
        Nat.log 2 (testingExecutionCost programCost name) <= Q}) /\
    μ (testingTower defaultOutput decodeBehavior programInput selfDelimitingCode
      codeInjective programCost).primary.named = 0 := by
  letI : MeasureSpace (Nat -> Output) := ⟨μ⟩
  have classification := testing_cost_classification defaultOutput selfDelimitingCode
    codeInjective programCost
  refine ⟨inferInstance,
    program_assignment_defined_iff_halts defaultOutput decodeBehavior programInput,
    program_name_domain_not_computable defaultOutput decodeBehavior programInput,
    classification.1, classification.2.1, classification.2.2, ?_⟩
  change volume (testingTower defaultOutput decodeBehavior programInput selfDelimitingCode
    codeInjective programCost).primary.named = 0
  simpa using
    (@dark_side_conservation (Nat -> Output) _ _
      { measure_singleton := fun point => measure_singleton point } _ Unit _
      (fun _ => (testingTower defaultOutput decodeBehavior programInput selfDelimitingCode
        codeInjective programCost).primary))

#print axioms testing_tower_has_multi_filtration_membership

end D5.S0.Naming.TestingTowerStructureMembership

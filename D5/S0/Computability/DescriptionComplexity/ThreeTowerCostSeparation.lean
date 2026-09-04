/- GID: D5/S0/Computability/DescriptionComplexity/ThreeTowerCostSeparation
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/ThreeTowerCostSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compiler inclusions squeeze distances, with explicit exponential separations. -/

import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Log
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/- Library-search and duplication audit (2026-09-04):
   * Repository keyword, symbol-variant, and generalized searches found the testing-name
     filtration and generic transformation bounds, but no three-tower distance sandwich or
     either explicit exponential separation below.
   * The source atom remains residual-open. The retired formalization-receipt directory was not
     inspected. `origin/dev` has no module at this routed path.
   * The in-flight scan covered 465 modules and 269 absorbed atoms; neither this module nor the
     source atom occurs there. The all-lane commit log likewise has no three-tower candidate.
   * Pinned Mathlib supplies `Metric.infDist_le_infDist_of_subset`, `Nat.log_pow`, and
     `List.getD_eq_default`; these are applied directly rather than reproved.
   * `Metric.infDist` totalizes the empty-set case. The public theorem explicitly assumes the
     prefix affordable set is nonempty, and compiler images construct nonempty later sets.
   * Escape witness preregistered before implementation: a spike at `2^j` forces every literal
     prefix to have length at least `2^j + 1`, while its indexed name has cost `j + 1`; and the
     literal table `range (2^j)` has cost `2^j`, while its range-program name has cost `j + 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Computability.DescriptionComplexity.ThreeTowerCostSeparation

/-- A naming tower whose names carry a natural-number budget cost. -/
structure BudgetedNaming (X Name : Type*) where
  value : Name -> X
  cost : Name -> Nat

namespace BudgetedNaming

/-- Values denoted by names affordable at budget `budget`. -/
def affordable {X Name : Type*} (tower : BudgetedNaming X Name) (budget : Nat) : Set X :=
  {x | exists name, tower.cost name <= budget /\ tower.value name = x}

end BudgetedNaming

/-- A semantics-preserving compiler whose target cost has fixed additive overhead. -/
structure CostCompiler {X SourceName TargetName : Type*}
    (source : BudgetedNaming X SourceName) (target : BudgetedNaming X TargetName)
    (overhead : Nat) where
  compile : SourceName -> TargetName
  value_compile : forall name, target.value (compile name) = source.value name
  cost_compile : forall name, target.cost (compile name) <= source.cost name + overhead

private theorem affordable_subset_of_compiler
    {X SourceName TargetName : Type*}
    {source : BudgetedNaming X SourceName} {target : BudgetedNaming X TargetName}
    {overhead budget : Nat} (compiler : CostCompiler source target overhead) :
    source.affordable budget <= target.affordable (budget + overhead) := by
  intro x hx
  rcases hx with ⟨name, hcost, rfl⟩
  refine ⟨compiler.compile name, ?_, compiler.value_compile name⟩
  exact (compiler.cost_compile name).trans (Nat.add_le_add_right hcost overhead)

/-- The binary sequence with one nondefault coordinate. -/
def spike (index : Nat) : Nat -> Bool :=
  fun n => if n = index then true else false

/-- A literal prefix denotes the sequence obtained by extending it with `false`. -/
def prefixValue (bits : List Bool) : Nat -> Bool :=
  fun n => bits.getD n false

/-- The indexed testing name denotes its one-coordinate spike. -/
def indexedSpikeValue (index : Nat) : Nat -> Bool :=
  spike index

/-- The indexed testing name pays the binary length of its selected coordinate. -/
def indexedSpikeCost (index : Nat) : Nat :=
  Nat.log 2 index + 1

/-- A literal finite table denotes its explicitly listed support. -/
def explicitTableValue (support : Finset Nat) : Finset Nat :=
  support

/-- Literal table cost is the number of explicitly listed support coordinates. -/
def explicitTableCost (support : Finset Nat) : Nat :=
  support.card

/-- A range-program name computes an initial segment from its bound. -/
def rangeProgramValue (bound : Nat) : Finset Nat :=
  Finset.range bound

/-- The range-program name pays only the binary length of its bound. -/
def rangeProgramCost (bound : Nat) : Nat :=
  Nat.log 2 bound + 1

private theorem prefix_spike_length_lower_bound (index : Nat) (bits : List Bool)
    (hvalue : prefixValue bits = spike index) :
    index + 1 <= bits.length := by
  have hlt : index < bits.length := by
    by_contra hnot
    have hle : bits.length <= index := Nat.le_of_not_gt hnot
    have hat := congrFun hvalue index
    rw [prefixValue, List.getD_eq_default bits false hle] at hat
    simp [spike] at hat
  omega

private theorem succ_lt_two_pow_of_two_le (j : Nat) (hj : 2 <= j) :
    j + 1 < 2 ^ j := by
  refine Nat.le_induction (by norm_num) ?_ j hj
  intro n hn ih
  have hle : n + 2 <= 2 ^ n := by omega
  calc
    n + 1 + 1 = n + 2 := by omega
    _ <= 2 ^ n := hle
    _ < 2 ^ n + 2 ^ n := Nat.lt_add_of_pos_right (by positivity)
    _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- Three compiler inclusions squeeze the best approximation distance. The squeeze is
nonvacuous because the prefix affordable set is inhabited. Independently, explicit spike and
range-table families witness strict exponential gaps from prefix to testing names and from
literal testing tables to program names. -/
theorem three_tower_cost_sandwich_and_double_separation
    {X PrefixName TestName ProgramName : Type*} [PseudoMetricSpace X]
    (prefixTower : BudgetedNaming X PrefixName)
    (testTower : BudgetedNaming X TestName)
    (programTower : BudgetedNaming X ProgramName)
    (prefixTestOverhead testProgramOverhead : Nat)
    (prefixToTest : CostCompiler prefixTower testTower prefixTestOverhead)
    (testToProgram : CostCompiler testTower programTower testProgramOverhead)
    (x : X) (budget : Nat)
    (hPrefixNonempty : (prefixTower.affordable budget).Nonempty) :
    (Metric.infDist x
          (programTower.affordable (budget + prefixTestOverhead + testProgramOverhead)) <=
        Metric.infDist x (testTower.affordable (budget + prefixTestOverhead)) /\
      Metric.infDist x (testTower.affordable (budget + prefixTestOverhead)) <=
        Metric.infDist x (prefixTower.affordable budget)) /\
    (forall j : Nat,
      indexedSpikeValue (2 ^ j) = spike (2 ^ j) /\
      indexedSpikeCost (2 ^ j) = j + 1 /\
      indexedSpikeCost (2 ^ j) < 2 ^ j + 1 /\
      (forall bits : List Bool,
        prefixValue bits = spike (2 ^ j) -> 2 ^ j + 1 <= bits.length)) /\
    (forall j : Nat, 2 <= j ->
      explicitTableValue (Finset.range (2 ^ j)) = rangeProgramValue (2 ^ j) /\
      explicitTableCost (Finset.range (2 ^ j)) = 2 ^ j /\
      rangeProgramCost (2 ^ j) = j + 1 /\
      rangeProgramCost (2 ^ j) < explicitTableCost (Finset.range (2 ^ j))) := by
  have hPrefixTest :
      prefixTower.affordable budget <=
        testTower.affordable (budget + prefixTestOverhead) :=
    affordable_subset_of_compiler prefixToTest
  have hTestProgram :
      testTower.affordable (budget + prefixTestOverhead) <=
        programTower.affordable (budget + prefixTestOverhead + testProgramOverhead) :=
    affordable_subset_of_compiler testToProgram
  have hTestNonempty : (testTower.affordable (budget + prefixTestOverhead)).Nonempty :=
    hPrefixNonempty.mono hPrefixTest
  refine ⟨⟨Metric.infDist_le_infDist_of_subset hTestProgram hTestNonempty,
    Metric.infDist_le_infDist_of_subset hPrefixTest hPrefixNonempty⟩, ?_, ?_⟩
  · intro j
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [indexedSpikeCost, Nat.log_pow Nat.one_lt_two]
    · simp only [indexedSpikeCost, Nat.log_pow Nat.one_lt_two]
      exact Nat.add_lt_add_right j.lt_two_pow_self 1
    · intro bits hvalue
      exact prefix_spike_length_lower_bound (2 ^ j) bits hvalue
  · intro j hj
    refine ⟨rfl, by simp [explicitTableCost], ?_, ?_⟩
    · simp [rangeProgramCost, Nat.log_pow Nat.one_lt_two]
    · simp only [rangeProgramCost, explicitTableCost, Finset.card_range,
        Nat.log_pow Nat.one_lt_two]
      exact succ_lt_two_pow_of_two_le j hj

#print axioms three_tower_cost_sandwich_and_double_separation

end D5.S0.Computability.DescriptionComplexity.ThreeTowerCostSeparation

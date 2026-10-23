/- GID: D5/S0/Computability/BinaryMachine/StackCompile
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackCompile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackCompile supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackCompile.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackSimulation
public import D5.S0.Computability.BinaryMachine.StackInit
public import D5.S0.Computability.BinaryMachine.PolynomialBound
import Lean.Elab.Tactic.Omega

/-!
Compile a fixed finite Boolean-stack machine into the original single-tape
machine, including input initialization and output extraction. Polynomial
runtime transfer is proved from actual counted simulations and arithmetic bounds.
-/

@[expose] public section

namespace Complexity.StackCompile

open StackCompiler StackSimulation

def compile (S : StackMachine.Machine) : Machine :=
  sequenceMachine (StackInit.initMachine S.stacks) (compiledController S)

def budget (S : StackMachine.Machine) (inputLength fuel : Nat) : Nat :=
  StackInit.initBudget S.stacks inputLength +
    fuel * instructionBudget S (inputLength + fuel)

theorem simulate (S : StackMachine.Machine) (fuel : Nat) (input : Word)
    (result : Bool × StackMachine.Registers S.stacks)
    (hrun : StackMachine.runInput S fuel input = some result) :
    ∃ time tape, time ≤ budget S input.length fuel ∧
      runInput (compile S) time input = some (result.1, tape) ∧
      tape.output = result.2 0 := by
  have hroom : Room (StackMachine.initial S input).registers fuel (input.length + fuel) := by
    intro k
    by_cases hk : k = 0 <;> simp [StackMachine.initial, hk]
  have hi : (StackEncoding.homeTape (StackMachine.initial S input).registers).Equivalent
      (StackInit.initialTape S.stacks input) := by
    rw [StackEncoding.homeTape_initial]
    exact Tape.Equivalent.refl _
  obtain ⟨time, ⟨decision, tape⟩, ht, hr, hp⟩ :=
    controller_simulates S fuel (StackMachine.initial S input) result hrun
      (input.length + fuel) hroom (StackInit.initialTape S.stacks input) hi
  have hb : decision = result.1 := hp.1
  subst decision
  have hseq := sequence_run (StackInit.initMachine S.stacks) (compiledController S)
    (StackInit.initBudget S.stacks input.length) time
    (initial (StackInit.initMachine S.stacks) input) (StackInit.initialTape S.stacks input)
    (result.1, tape) (StackInit.initMachine_run S.stacks input)
    (by simp [StackInit.initialTape]) hr
  refine ⟨StackInit.initBudget S.stacks input.length + time, tape,
    Nat.add_le_add_left ht _, ?_, hp.2⟩
  exact hseq

theorem instructionBudget_mono (S : StackMachine.Machine) {n m : Nat} (h : n ≤ m) :
    instructionBudget S n ≤ instructionBudget S m := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4
    (Nat.add_le_add_right (Nat.mul_le_mul_left (S.stacks + 1) (Nat.add_le_add_right h 1)) 1)) 13

theorem budget_mono (S : StackMachine.Machine) (n : Nat) {fuel bound : Nat}
    (h : fuel ≤ bound) : budget S n fuel ≤ budget S n bound := by
  exact Nat.add_le_add_left
    (Nat.mul_le_mul h (instructionBudget_mono S (Nat.add_le_add_left h n))) _

theorem polynomialBound_budget (S : StackMachine.Machine) (bound : Nat → Nat)
    (hbound : PolynomialBound bound) : PolynomialBound (fun n => budget S n (bound n)) := by
  have hinit := ((PolynomialBound.constant 2).mul PolynomialBound.identity).add
    (PolynomialBound.constant (2 * S.stacks))
  have hinit' := hinit.add (PolynomialBound.constant 9)
  have hcap := (PolynomialBound.identity.add hbound).add (PolynomialBound.constant 1)
  have hins := ((PolynomialBound.constant 4).mul
    (((PolynomialBound.constant (S.stacks + 1)).mul hcap).add (PolynomialBound.constant 1))).add
    (PolynomialBound.constant 13)
  exact hinit'.add (hbound.mul hins)

/-- A proved bounded stack algorithm gives a polynomial-time transducer on the
original machine model. The computed output is read from physical tape cells. -/
theorem polyTime_of_stack (S : StackMachine.Machine) (bound : Nat → Nat)
    (hbound : PolynomialBound bound) {f : Word → Word}
    (hS : ∀ input, ∃ time registers, time ≤ bound input.length ∧
      StackMachine.runInput S time input = some (true, registers) ∧ registers 0 = f input) :
    PolyTime f := by
  obtain ⟨c, k, hpoly⟩ := polynomialBound_budget S bound hbound
  refine ⟨compile S, c, k, ?_⟩
  intro input
  obtain ⟨time, registers, ht, hr, ho⟩ := hS input
  obtain ⟨targetTime, tape, htarget, hrun, hout⟩ := simulate S time input (true, registers) hr
  exact ⟨targetTime, tape,
    Nat.le_trans htarget (Nat.le_trans (budget_mono S input.length ht) (hpoly input.length)),
    hrun, hout.trans ho⟩

/-- Total bounded stack computations, with either decision, compile to total
polynomial-time machines. -/
theorem polynomialTimeMachine_of_stack (S : StackMachine.Machine) (bound : Nat → Nat)
    (hbound : PolynomialBound bound)
    (hS : ∀ input, ∃ time decision registers, time ≤ bound input.length ∧
      StackMachine.runInput S time input = some (decision, registers)) :
    PolynomialTimeMachine (compile S) := by
  obtain ⟨c, k, hpoly⟩ := polynomialBound_budget S bound hbound
  refine ⟨c, k, ?_⟩
  intro input
  obtain ⟨time, decision, registers, ht, hr⟩ := hS input
  obtain ⟨targetTime, tape, htarget, hrun, _⟩ := simulate S time input (decision, registers) hr
  exact ⟨targetTime, decision, tape,
    Nat.le_trans htarget (Nat.le_trans (budget_mono S input.length ht) (hpoly input.length)), hrun⟩

/-- Acceptance is reflected as well as preserved for a total stack algorithm.
The reverse implication uses determinism of the original machine. -/
theorem accepts_iff (S : StackMachine.Machine) (input : Word)
    (htotal : ∃ time decision registers,
      StackMachine.runInput S time input = some (decision, registers)) :
    Accepts (compile S) input ↔
      ∃ time registers, StackMachine.runInput S time input = some (true, registers) := by
  constructor
  · intro ⟨targetTime, targetTape, htarget⟩
    obtain ⟨time, decision, registers, hr⟩ := htotal
    obtain ⟨t, tape, _, ht, _⟩ := simulate S time input (decision, registers) hr
    have heq := run_deterministic (compile S) (initial (compile S) input) htarget ht
    have hb : decision = true := (congrArg Prod.fst heq).symm
    subst decision
    exact ⟨time, registers, hr⟩
  · intro ⟨time, registers, hr⟩
    obtain ⟨t, tape, _, ht, _⟩ := simulate S time input (true, registers) hr
    exact ⟨t, tape, ht⟩

end Complexity.StackCompile

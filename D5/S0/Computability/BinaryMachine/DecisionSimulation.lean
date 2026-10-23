/- GID: D5/S0/Computability/BinaryMachine/DecisionSimulation
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/DecisionSimulation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Genuine accepting and rejecting tape executions survive stack preprocessing. -/

import D5.S0.Computability.BinaryMachine.TransducerPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.DecisionSimulation
open StackMachine (Registers)
open StackProgram

def source (M : Machine) := seq TapeToStacks.initializer (TapeToStacks.core M)
def program (M : Machine) := StackFrame.lift TransducerPair.simulationRegister (source M)
def encoding (M : Machine) := ((Encoding.fin 3).sum (Encoding.fin 5)).sum (TapeToStacks.labelEncoding M)

/-- The exact Boolean halt decision, including false, is preserved. The witness
is an actual counted execution in the finite program compiled to the tape model. -/
theorem exec_program (M : Machine) (fuel : Nat) (input : Word) (b : Bool) (out : Tape)
    (h : runInput M fuel input = some (b, out)) (r : Registers 6)
    (h₀ : r 0 = input) (h₂ : r 2 = []) (h₃ : r 3 = []) :
    ∃ time result, time ≤ 6 * (input.length + fuel + 1) ∧
      Exec (program M) (program M).start r time (b, result) := by
  obtain ⟨time, ht, he⟩ := TapeToStacks.simulate_core M fuel input b out h []
  have hi := TapeToStacks.exec_initializer input
  have hh := exec_seq TapeToStacks.initializer (TapeToStacks.core M) hi he
  have hp : StackFrame.pull TransducerPair.simulationRegister r = TapeToStacks.regs input [] [] := by
    funext j
    rcases TapeToStacks.fin_three_cases j with rfl | rfl | rfl <;>
      simp [StackFrame.pull, TransducerPair.simulationRegister, TapeToStacks.regs, h₀, h₂, h₃]
  obtain ⟨result, hr, _, _⟩ := StackFrame.exec_lift TransducerPair.simulationRegister
    TransducerPair.simulationRegister_injective _ hh r hp
  exact ⟨5 * input.length + 4 + time, result, by omega, hr⟩

end Complexity.DecisionSimulation

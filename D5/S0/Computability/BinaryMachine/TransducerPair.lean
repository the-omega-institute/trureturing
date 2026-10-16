/- GID: D5/S0/Computability/BinaryMachine/TransducerPair
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/TransducerPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common-input polynomial transducers execute both maps and construct their ordered pair. -/

import D5.S0.Computability.BinaryMachine.PairConstructor
import D5.S0.Computability.BinaryMachine.StackFrame
import D5.S0.Computability.BinaryMachine.StackCompile
import D5.S0.Computability.BinaryMachine.Composition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity.TransducerPair
open StackMachine (Registers)
open StackProgram

/-- Three simulation registers, leaving certificate and saved output untouched. -/
def simulationRegister (j : Fin 3) : Fin 7 := if j = 0 then 0 else if j = 1 then 2 else 3

theorem simulationRegister_injective : Function.Injective simulationRegister := by
  intro a b h
  rcases TapeToStacks.fin_three_cases a with rfl | rfl | rfl <;>
    rcases TapeToStacks.fin_three_cases b with rfl | rfl | rfl <;>
    simp_all [simulationRegister]

def normalized (M : Machine) := StackFrame.lift simulationRegister (TapeToStacks.normalized M)

/-- A normalized tape transducer can run in a larger frame without changing any
saved word. This theorem consumes the actual register-injection simulation. -/
theorem exec_normalized (M : Machine) (fuel : Nat) (input : Word) (out : Tape)
    (h : runInput M fuel input = some (true, out)) (r : Registers 6)
    (h₀ : r 0 = input) (h₂ : r 2 = []) (h₃ : r 3 = []) :
    ∃ time, time ≤ 18 * (input.length + fuel + 2) ∧
      Exec (normalized M) (normalized M).start r time (true, StackMachine.set r 0 out.output) := by
  obtain ⟨time, ht, he⟩ := TapeToStacks.exec_normalized M fuel input out h
  have hp : StackFrame.pull simulationRegister r = TapeToStacks.regs input [] [] := by
    funext j
    rcases TapeToStacks.fin_three_cases j with rfl | rfl | rfl <;>
      simp [StackFrame.pull, simulationRegister, TapeToStacks.regs, h₀, h₂, h₃]
  obtain ⟨result, hr, hout, hf⟩ := StackFrame.exec_lift simulationRegister
    simulationRegister_injective _ he r hp
  have hresult : result = StackMachine.set r 0 out.output := by
    funext a
    by_cases hzero : a = 0
    · subst a
      have hh := congrFun hout 0
      simpa [StackFrame.pull, simulationRegister] using hh
    · by_cases htwo : a = 2
      · subst a
        have hh := congrFun hout 1
        simpa [StackFrame.pull, simulationRegister, h₂] using hh
      · by_cases hthree : a = 3
        · subst a
          have hh := congrFun hout 2
          simpa [StackFrame.pull, simulationRegister, h₃] using hh
        · rw [hf a]
          · simp [hzero]
          · intro j
            rcases TapeToStacks.fin_three_cases j with rfl | rfl | rfl <;>
              simpa [simulationRegister] using (show a ≠ _ from by assumption)
  exact ⟨time, ht, by simpa [normalized, StackFrame.lift, hresult] using hr⟩

def program (first second : Machine) :=
  seq (StackWords.copy (k := 6) 0 1 2)
    (seq (normalized first)
      (seq (StackControl.moveWord (k := 6) 0 4 2)
        (seq (StackControl.moveWord (k := 6) 1 0 2)
          (seq (normalized second)
            (seq (StackControl.moveWord (k := 6) 0 1 2)
              (seq (StackControl.moveWord (k := 6) 4 0 2) PairConstructor.build))))))

def encoding (first second : Machine) := StackWords.copyMapEncoding.sum
  ((TapeToStacks.normalEncoding first).sum (StackControl.moveEncoding.sum
    (StackControl.moveEncoding.sum ((TapeToStacks.normalEncoding second).sum
      (StackControl.moveEncoding.sum (StackControl.moveEncoding.sum PairConstructor.buildEncoding))))))

/-- Two actual tape runs receive the same input. Their complete ordered output
is assembled before compilation, with a polynomial instruction budget. -/
theorem exec_program (first second : Machine) (firstFuel secondFuel : Nat)
    (input : Word) (firstOut secondOut : Tape)
    (hfirst : runInput first firstFuel input = some (true, firstOut))
    (hsecond : runInput second secondFuel input = some (true, secondOut)) :
    ∃ time, time ≤ 128 * (input.length + firstFuel + secondFuel + 1) ∧
      Exec (program first second) (program first second).start (StackPair.initial input) time
        (true, StackPair.initial (pairWords firstOut.output secondOut.output)) := by
  let r := StackPair.initial input
  let r₁ := StackMachine.set r 1 input
  let r₂ := StackMachine.set r₁ 0 firstOut.output
  let r₃ := StackMachine.set (StackMachine.set r₂ 0 []) 4 firstOut.output
  let r₄ := StackMachine.set (StackMachine.set r₃ 1 []) 0 input
  let r₅ := StackMachine.set r₄ 0 secondOut.output
  let r₆ := StackMachine.set (StackMachine.set r₅ 0 []) 1 secondOut.output
  let r₇ := StackMachine.set (StackMachine.set r₆ 4 []) 0 firstOut.output
  have h₁ := StackWords.exec_copy (k := 6) 0 1 2 (by decide) (by decide) (by decide) r (by rfl)
  have h₁' : Exec (StackWords.copy (k := 6) 0 1 2) (StackWords.copy (k := 6) 0 1 2).start r
      (5 * input.length + 6) (true, r₁) := by simpa [r, r₁, StackPair.initial, StackPair.input, StackWords.copy, StackWords.copyMap, StackWords.clear, seq] using h₁
  obtain ⟨t, ht, h₂⟩ := exec_normalized first firstFuel input firstOut hfirst r₁
    (by simp [r₁, r, StackPair.initial, StackPair.input]) (by simp [r₁, r, StackPair.initial, StackPair.input]) (by simp [r₁, r, StackPair.initial, StackPair.input])
  have h₃ := StackControl.exec_moveWord (k := 6) 0 4 2 (by decide) (by decide) (by decide) r₂
    (by simp [r₂, r₁, r, StackPair.initial, StackPair.input])
  have h₄ := StackControl.exec_moveWord (k := 6) 1 0 2 (by decide) (by decide) (by decide) r₃
    (by simp [r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
  obtain ⟨s, hs, h₅⟩ := exec_normalized second secondFuel input secondOut hsecond r₄
    (by simp [r₄]) (by simp [r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
    (by simp [r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
  have h₆ := StackControl.exec_moveWord (k := 6) 0 1 2 (by decide) (by decide) (by decide) r₅
    (by simp [r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
  have h₇ := StackControl.exec_moveWord (k := 6) 4 0 2 (by decide) (by decide) (by decide) r₆
    (by simp [r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
  have h₈ := PairConstructor.exec_build r₇
    (by simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
    (by simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input])
  have hh := exec_seq _ _ h₁' (exec_seq _ _ h₂ (exec_seq _ _ h₃
    (exec_seq _ _ h₄ (exec_seq _ _ h₅ (exec_seq _ _ h₆ (exec_seq _ _ h₇ h₈))))))
  have hout : StackMachine.set (StackMachine.set r₇ 0 (pairWords (r₇ 0) (r₇ 1))) 1 [] =
      StackPair.initial (pairWords firstOut.output secondOut.output) := by
    funext a
    by_cases h₀ : a = 0
    · subst a; simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input]
    · by_cases h₁ : a = 1
      · subst a; simp [StackPair.initial, StackPair.input]
      · by_cases h₄ : a = 4
        · subst a; simp [r₇, StackPair.initial, StackPair.input]
        · simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input, StackMachine.set, h₀, h₁, h₄]
  change Exec _ _ _ _ (true, _) at hh
  rw [hout] at hh
  have hfLen := runInput_output_length_le first firstFuel input (true, firstOut) hfirst
  have hgLen := runInput_output_length_le second secondFuel input (true, secondOut) hsecond
  change firstOut.output.length ≤ input.length + 2 * firstFuel at hfLen
  change secondOut.output.length ≤ input.length + 2 * secondFuel at hgLen
  refine ⟨_, ?_, hh⟩
  simp [r₇, r₆, r₅, r₄, r₃, r₂, r₁, r, StackPair.initial, StackPair.input,
    StackMachine.set]
  omega

/-- Polynomial pairing is an executed common-input construction in the original
single-tape model, rather than a closure assumption. -/
theorem polyTime_pair {f g : Word → Word} (hf : PolyTime f) (hg : PolyTime g) :
    PolyTime (fun x => pairWords (f x) (g x)) := by
  obtain ⟨first, c, k, hf⟩ := hf
  obtain ⟨second, d, l, hg⟩ := hg
  let bound := fun n => 128 * (n + powerBound c k n + powerBound d l n + 1)
  have hb : PolynomialBound bound := (PolynomialBound.constant 128).mul
    (((PolynomialBound.identity.add (PolynomialBound.power c k)).add
      (PolynomialBound.power d l)).add (PolynomialBound.constant 1))
  apply StackCompile.polyTime_of_stack (compile (program first second) (encoding first second)) bound hb
  intro input
  obtain ⟨t, firstOut, ht, hfirst, hout₁⟩ := hf input
  obtain ⟨s, secondOut, hs, hsecond, hout₂⟩ := hg input
  obtain ⟨time, htime, he⟩ := exec_program first second t s input firstOut secondOut hfirst hsecond
  refine ⟨time, StackPair.initial (pairWords firstOut.output secondOut.output), ?_, ?_, ?_⟩
  · unfold bound
    omega
  · exact compile_exec (encoding first second) he
  · simp [StackPair.initial, StackPair.input, hout₁, hout₂]

end Complexity.TransducerPair

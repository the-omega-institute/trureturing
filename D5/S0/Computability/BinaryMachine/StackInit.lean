/- GID: D5/S0/Computability/BinaryMachine/StackInit
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackInit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackInit supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackInit.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackCompiler
public import D5.S0.Computability.BinaryMachine.TapeEquiv
import Lean.Elab.Tactic.Omega

/-!
Initialize the concrete one-tape stack-register representation from raw binary
input. All control counters are finite states fixed by the register count.
-/

@[expose] public section

namespace Complexity.StackInit

open StackCompiler

/-- Preparation phases: 0 is halt; 1..count emit remaining separators; then
scan, prefix placement, and initial left move. -/
@[reducible] def prepare (stacks : Nat) : Machine where
  states := stacks + 4
  start := ⟨stacks + 4, by omega⟩
  code q a :=
    if q.val = stacks + 4 then .step a .left ⟨stacks + 3, by omega⟩
    else if q.val = stacks + 3 then .step .sep .right ⟨stacks + 2, by omega⟩
    else if q.val = stacks + 2 then
      if a = .blank then .step .sep .stay ⟨stacks + 1, by omega⟩
      else .step a .right ⟨stacks + 2, by omega⟩
    else if q.val = 0 then .halt true
    else if q.val = 1 then .step .sep .stay 0
    else .step .sep .right ⟨q.val - 1, by have := q.isLt; omega⟩


@[simp] theorem prepare_code_halt (stacks : Nat) (a : Symbol) :
    (prepare stacks).code 0 a = .halt true := by simp [prepare]

theorem prepare_code_emit (stacks : Nat) (q : Fin (stacks + 4 + 1))
    (hq : 0 < q.val) (hbound : q.val ≤ stacks + 1) (a : Symbol) :
    (prepare stacks).code q a =
      if q.val = 1 then .step .sep .stay 0
      else .step .sep .right ⟨q.val - 1, by change q.val - 1 < stacks + 4 + 1; have := q.isLt; omega⟩ := by
  have h4 : q.val ≠ stacks + 4 := by omega
  have h3 : q.val ≠ stacks + 3 := by omega
  have h2 : q.val ≠ stacks + 2 := by omega
  have h0 : q.val ≠ 0 := by omega
  simp only [prepare, h4, h3, h2, h0, ↓reduceIte]

/-- Emit `remaining` separators, ending with the head on the last. -/
theorem emit_run (stacks remaining : Nat) (hpos : 0 < remaining)
    (hrem : remaining ≤ stacks + 1) (left : List Symbol) (right : List Symbol)
    (hr : right = [] ∨ right = [.sep]) :
    run (prepare stacks) (remaining + 1)
      ⟨⟨remaining, by change remaining < stacks + 4 + 1; omega⟩, ⟨left, right⟩⟩ =
      some (true, ⟨List.replicate (remaining - 1) .sep ++ left, [.sep]⟩) := by
  induction remaining generalizing left right with
  | zero => omega
  | succ remaining ih =>
    rw [run]
    have h4 : remaining + 1 ≠ stacks + 4 := by omega
    have h3 : remaining + 1 ≠ stacks + 3 := by omega
    have h2 : remaining + 1 ≠ stacks + 2 := by omega
    simp only [prepare, h4, h3, h2, Nat.succ_ne_zero, ↓reduceIte]
    by_cases hz : remaining = 0
    · subst remaining
      rcases hr with rfl | rfl <;>
        simp [run, Tape.write, Tape.move]
    · have hne1 : remaining + 1 ≠ 1 := by omega
      simp only [hne1, ↓reduceIte]
      have hi := ih (by omega) (by omega) (.sep :: left) [] (Or.inl rfl)
      have hrepl : List.replicate remaining Symbol.sep ++ left =
          List.replicate (remaining - 1) Symbol.sep ++ .sep :: left := by
        conv => lhs; rw [show remaining = (remaining - 1) + 1 by omega]
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      rcases hr with rfl | rfl <;>
        simpa only [prepare, Tape.read, Tape.write, Tape.move, List.drop_nil, List.drop_cons,
          List.drop_zero, show List.drop 1 [Symbol.sep] = [] from rfl, List.cons_append, Nat.add_sub_cancel, hrepl] using hi


@[simp] theorem prepare_code_scan (stacks : Nat) (a : Symbol) :
    (prepare stacks).code ⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩ a =
      if a = .blank then .step .sep .stay ⟨stacks + 1, by change _ < stacks + 4 + 1; omega⟩
      else .step a .right ⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩ := by simp [prepare]

@[simp] theorem prepare_code_prefix (stacks : Nat) (a : Symbol) :
    (prepare stacks).code ⟨stacks + 3, by change _ < stacks + 4 + 1; omega⟩ a =
      .step .sep .right ⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩ := by simp [prepare]

@[simp] theorem prepare_code_start (stacks : Nat) (a : Symbol) :
    (prepare stacks).code (prepare stacks).start a =
      .step a .left ⟨stacks + 3, by change _ < stacks + 4 + 1; omega⟩ := by simp [prepare]

theorem scan_run (stacks : Nat) (word : List Bool) (left : List Symbol) :
    run (prepare stacks) (word.length + stacks + 3)
      ⟨⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩, ⟨left, word.map Symbol.bit⟩⟩ =
      some (true, ⟨List.replicate stacks .sep ++ (word.map Symbol.bit).reverse ++ left,
        [.sep]⟩) := by
  induction word generalizing left with
  | nil =>
    have he := emit_run stacks (stacks + 1) (by omega) (by omega) left [.sep] (Or.inr rfl)
    simp only [List.length_nil, Nat.zero_add, List.map_nil, List.reverse_nil]
    change run (prepare stacks) ((stacks + 2) + 1) _ = _
    rw [run]
    simpa [prepare, Tape.read, Tape.write, Tape.move] using he
  | cons bit word ih =>
    rw [List.length_cons, show word.length + 1 + stacks + 3 =
      (word.length + stacks + 3) + 1 by omega, run]
    simpa [prepare, Tape.read, Tape.write, Tape.move, List.reverse_cons,
      List.append_assoc] using ih (.bit bit :: left)


def inputCells : List Bool → List Symbol
  | [] => [.blank]
  | bit :: word => .bit bit :: word.map Symbol.bit

theorem startup_run (stacks fuel : Nat) (word : List Bool) :
    runInput (prepare stacks) (fuel + 2) word =
      run (prepare stacks) fuel
        ⟨⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩,
          ⟨[.sep], inputCells word⟩⟩ := by
  cases word <;> simp [runInput, initial, Tape.ofInput, run, prepare, Tape.read,
    Tape.write, Tape.move, inputCells]

theorem scan_blank_run (stacks : Nat) (left : List Symbol) :
    run (prepare stacks) (stacks + 3)
      ⟨⟨stacks + 2, by change _ < stacks + 4 + 1; omega⟩, ⟨left, [.blank]⟩⟩ =
      some (true, ⟨List.replicate stacks .sep ++ left, [.sep]⟩) := by
  have he := emit_run stacks (stacks + 1) (by omega) (by omega) left [.sep] (Or.inr rfl)
  rw [run]
  simpa [prepare, Tape.read, Tape.write, Tape.move] using he

theorem prepare_run (stacks : Nat) (word : List Bool) :
    runInput (prepare stacks) (word.length + stacks + 5) word =
      some (true, ⟨List.replicate stacks .sep ++ (word.map Symbol.bit).reverse ++ [.sep],
        [.sep]⟩) := by
  rw [show word.length + stacks + 5 = (word.length + stacks + 3) + 2 by omega,
    startup_run]
  cases word with
  | nil => simpa [inputCells] using scan_blank_run stacks [.sep]
  | cons bit word => exact scan_run stacks (bit :: word) [.sep]

def initMachine (stacks : Nat) : Machine := sequenceMachine (prepare stacks) rewindMachine

def initBudget (stacks inputLength : Nat) : Nat := 2 * inputLength + 2 * stacks + 9

/-- Canonical encoding: leading separator, register zero containing the input,
then one separator for each remaining empty register and the final boundary. -/
def initialTape (stacks : Nat) (word : List Bool) : Tape :=
  ⟨[.blank], .sep :: (word.map Symbol.bit ++ List.replicate (stacks + 1) .sep)⟩

theorem initMachine_run (stacks : Nat) (word : List Bool) :
    runInput (initMachine stacks) (initBudget stacks word.length) word =
      some (true, initialTape stacks word) := by
  let left := List.replicate stacks Symbol.sep ++ (word.map Symbol.bit).reverse ++ [.sep]
  have hn : ∀ a ∈ left, a ≠ .blank := by
    intro a ha
    simp only [left, List.mem_append, List.mem_replicate, List.mem_reverse,
      List.mem_map, List.mem_singleton] at ha
    rcases ha with (⟨_, rfl⟩ | ⟨b, _, rfl⟩) | rfl <;> simp
  have hr := rewind_run left .sep [] (by simp) hn
  have hlen : left.length = stacks + word.length + 1 := by simp [left, Nat.add_assoc]
  have heq : left.reverse ++ [.sep] =
      .sep :: (word.map Symbol.bit ++ List.replicate (stacks + 1) .sep) := by
    simp [left, List.reverse_append, List.append_assoc, List.replicate_succ']
  rw [hlen, heq] at hr
  have hseq := sequence_run (prepare stacks) rewindMachine
    (word.length + stacks + 5) (stacks + word.length + 1 + 3)
    (initial (prepare stacks) word) ⟨left, [.sep]⟩ (true, initialTape stacks word)
    (prepare_run stacks word) (by simp) hr
  have htime : word.length + stacks + 5 + (stacks + word.length + 1 + 3) =
      initBudget stacks word.length := by simp only [initBudget]; omega
  simpa only [htime, runInput, initial, initMachine, sequenceMachine] using hseq

theorem initMachine_correct (stacks : Nat) (word : List Bool) :
    ∃ out, runInput (initMachine stacks) (initBudget stacks word.length) word =
      some (true, out) ∧ out.Equivalent (initialTape stacks word) :=
  ⟨initialTape stacks word, initMachine_run stacks word, Tape.Equivalent.refl _⟩

end Complexity.StackInit

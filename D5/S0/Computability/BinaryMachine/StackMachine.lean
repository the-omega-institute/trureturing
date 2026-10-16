/- GID: D5/S0/Computability/BinaryMachine/StackMachine
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackMachine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackMachine supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackMachine.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.Machine
import Lean.Elab.Tactic.Omega

/-!
# Finite Boolean stack machines

All registers contain lists of bits. Each instruction inspects or changes at
most one stack cell; local control is finite. This model is an intermediate
programming language, not a replacement definition of polynomial time.
-/

@[expose] public section

namespace Complexity.StackMachine

abbrev Word := List Bool
abbrev Registers (stacks : Nat) := Fin (stacks + 1) → Word

inductive Instruction (stacks states : Nat) where
  | halt (decision : Bool)
  | goto (next : Fin (states + 1))
  | push (register : Fin (stacks + 1)) (value : Bool) (next : Fin (states + 1))
  | pop (register : Fin (stacks + 1)) (empty zero one : Fin (states + 1))
  | peek (register : Fin (stacks + 1)) (empty zero one : Fin (states + 1))
  deriving DecidableEq, Repr

structure Machine where
  stacks : Nat
  states : Nat
  start : Fin (states + 1)
  code : Fin (states + 1) → Instruction stacks states

structure Config (M : Machine) where
  state : Fin (M.states + 1)
  registers : Registers M.stacks

def set {stacks : Nat} (r : Registers stacks) (k : Fin (stacks + 1))
    (value : Word) : Registers stacks :=
  fun j => if j = k then value else r j

@[simp] theorem set_same {stacks : Nat} (r : Registers stacks)
    (k : Fin (stacks + 1)) (value : Word) : set r k value k = value := by
  simp [set]

@[simp] theorem set_other {stacks : Nat} (r : Registers stacks)
    {j k : Fin (stacks + 1)} (h : j ≠ k) (value : Word) : set r k value j = r j := by
  simp [set, h]

def branch {α : Type} (xs : Word) (empty zero one : α) : α :=
  match xs with
  | [] => empty
  | false :: _ => zero
  | true :: _ => one

def initial (M : Machine) (input : Word) : Config M :=
  ⟨M.start, fun j => if j = 0 then input else []⟩

def output {stacks : Nat} (r : Registers stacks) : Word := r 0

/-- One unit of fuel pays for one elementary finite-control instruction. -/
def run (M : Machine) : Nat → Config M → Option (Bool × Registers M.stacks)
  | 0, _ => none
  | fuel + 1, c =>
    match M.code c.state with
    | .halt b => some (b, c.registers)
    | .goto q => run M fuel ⟨q, c.registers⟩
    | .push k b q => run M fuel ⟨q, set c.registers k (b :: c.registers k)⟩
    | .pop k e z o =>
      run M fuel ⟨branch (c.registers k) e z o,
        set c.registers k (c.registers k).tail⟩
    | .peek k e z o => run M fuel ⟨branch (c.registers k) e z o, c.registers⟩

def runInput (M : Machine) (fuel : Nat) (input : Word) :
    Option (Bool × Registers M.stacks) := run M fuel (initial M input)

theorem run_add (M : Machine) (fuel extra : Nat) (c : Config M)
    (result : Bool × Registers M.stacks) (h : run M fuel c = some result) :
    run M (fuel + extra) c = some result := by
  induction fuel generalizing c with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : M.code c.state <;>
      simp only [run, hc] at h <;>
      simp only [Nat.succ_add, run, hc]
    · exact h
    all_goals exact ih _ h

theorem run_mono (M : Machine) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (c : Config M) (result : Bool × Registers M.stacks)
    (h : run M fuel c = some result) : run M fuel' c = some result := by
  have heq : fuel + (fuel' - fuel) = fuel' := by omega
  rw [← heq]
  exact run_add M fuel (fuel' - fuel) c result h

theorem run_deterministic (M : Machine) {fuel fuel' : Nat} (c : Config M)
    {result result' : Bool × Registers M.stacks}
    (h : run M fuel c = some result) (h' : run M fuel' c = some result') :
    result = result' := by
  have h₁ := run_mono M (Nat.le_max_left fuel fuel') c result h
  have h₂ := run_mono M (Nat.le_max_right fuel fuel') c result' h'
  exact Option.some.inj (h₁.symm.trans h₂)

/-- An individual stack can gain at most one bit per instruction. -/
theorem run_length_le (M : Machine) (fuel : Nat) (c : Config M)
    (result : Bool × Registers M.stacks) (h : run M fuel c = some result)
    (bound : Nat) (hb : ∀ k, (c.registers k).length ≤ bound) :
    ∀ k, (result.2 k).length ≤ bound + fuel := by
  induction fuel generalizing c bound with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : M.code c.state with
    | halt b =>
      simp only [run, hc, Option.some.injEq] at h
      rw [← h]
      intro k
      have hk := hb k
      simp only
      omega
    | goto q =>
      simp only [run, hc] at h
      intro k
      have hk := ih _ h bound hb k
      omega
    | push j b q =>
      simp only [run, hc] at h
      have hb' : ∀ k, (set c.registers j (b :: c.registers j) k).length ≤ bound + 1 := by
        intro k
        by_cases hk : k = j
        · subst k
          simpa using Nat.add_le_add_right (hb j) 1
        · simpa [hk] using Nat.le_trans (hb k) (Nat.le_succ bound)
      intro k
      have hk := ih _ h (bound + 1) hb' k
      omega
    | pop j e z o =>
      simp only [run, hc] at h
      have hb' : ∀ k, (set c.registers j (c.registers j).tail k).length ≤ bound := by
        intro k
        by_cases hk : k = j
        · subst k
          simp only [set_same, List.length_tail]
          have hj := hb j
          omega
        · simpa [hk] using hb k
      intro k
      have hk := ih _ h bound hb' k
      omega
    | peek j e z o =>
      simp only [run, hc] at h
      intro k
      have hk := ih _ h bound hb k
      omega

theorem runInput_length_le (M : Machine) (fuel : Nat) (input : Word)
    (result : Bool × Registers M.stacks) (h : runInput M fuel input = some result) :
    ∀ k, (result.2 k).length ≤ input.length + fuel := by
  apply run_length_le M fuel (initial M input) result h input.length
  intro k
  simp [initial]
  split <;> simp

end Complexity.StackMachine

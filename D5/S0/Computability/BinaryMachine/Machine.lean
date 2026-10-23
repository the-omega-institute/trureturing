/- GID: D5/S0/Computability/BinaryMachine/Machine
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Machine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine Machine supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/Machine.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import Init
import Lean.Elab.Tactic.Omega

/-!
A concrete deterministic one-tape Turing machine. Each `run` step executes one
finite-control instruction. The tape is infinite in both directions, with an
implicit blank beyond each stored list. The output convention is the consecutive
bits beginning at the final head position, ending at the first non-bit symbol.
-/

@[expose] public section

namespace Complexity

/-- Tape symbols: the blank, the two bits, and a separator `sep` (a work symbol). -/
inductive Symbol where
  | blank | bit (value : Bool) | sep
  deriving DecidableEq, Repr

/-- A head movement: one cell left, none, or one cell right. -/
inductive Move where
  | left | stay | right
  deriving DecidableEq, Repr

/-- A two-way infinite tape: `right` is the scanned cell and the cells to its right,
`left` the cells to its left, nearest first; all other cells are blank. -/
structure Tape where
  left : List Symbol
  right : List Symbol
  deriving DecidableEq, Repr

namespace Tape

/-- The scanned symbol (blank beyond the stored cells). -/
def read (t : Tape) : Symbol := t.right.headD .blank

/-- Overwrite the scanned cell with `a`. -/
def write (a : Symbol) (t : Tape) : Tape :=
  { t with right := a :: t.right.drop 1 }

/-- Move the head by `d`, storing a blank cell when it moves past the stored cells. -/
def move (d : Move) (t : Tape) : Tape :=
  match d with
  | .stay => t
  | .left =>
    match t.left with
    | [] => ⟨[], .blank :: t.right⟩
    | a :: rest => ⟨rest, a :: t.right⟩
  | .right =>
    match t.right with
    | [] => ⟨.blank :: t.left, []⟩
    | a :: rest => ⟨a :: t.left, rest⟩

/-- The tape holding `input` as bits, head on its first cell, blank elsewhere. -/
def ofInput (input : List Bool) : Tape := ⟨[], input.map Symbol.bit⟩

/-- The longest prefix of a symbol list made of bits, as a binary word. -/
def bits : List Symbol → List Bool
  | .bit b :: rest => b :: bits rest
  | _ => []

/-- The output: the bits from the head rightwards, up to the first non-bit cell. -/
def output (t : Tape) : List Bool := bits t.right

/-- Number of explicitly represented cells; this includes stored blank cells. -/
def size (t : Tape) : Nat := t.left.length + t.right.length

@[simp] theorem read_write (a : Symbol) (t : Tape) :
    (write a t).read = a := by
  simp [read, write]

@[simp] theorem size_ofInput (input : List Bool) :
    (ofInput input).size = input.length := by
  simp [ofInput, size]

theorem bits_length_le (xs : List Symbol) : (bits xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih =>
    cases x <;> simp [bits] <;> omega

theorem output_length_le (t : Tape) : t.output.length ≤ t.size := by
  have h := bits_length_le t.right
  simp only [output, size]
  omega

theorem write_size_le (a : Symbol) (t : Tape) :
    (t.write a).size ≤ t.size + 1 := by
  cases t with
  | mk left right =>
    cases right <;> simp [write, size] <;> omega

theorem move_size_le (d : Move) (t : Tape) :
    (t.move d).size ≤ t.size + 1 := by
  cases t with
  | mk left right =>
    cases d with
    | stay => simp [move]
    | left => cases left <;> simp [move, size] <;> omega
    | right => cases right <;> simp [move, size] <;> omega

theorem move_write_size_le (a : Symbol) (d : Move) (t : Tape) :
    ((t.write a).move d).size ≤ t.size + 2 := by
  have hw := write_size_le a t
  have hm := move_size_le d (t.write a)
  omega

end Tape

/-- An instruction: `halt b` (`true` accepts), or write, move, and enter state `next`. -/
inductive Instruction (states : Nat) where
  | halt (decision : Bool)
  | step (write : Symbol) (move : Move) (next : Fin states)
  deriving DecidableEq, Repr

/-- Relabel finite-control states, leaving every physical tape operation and
the Boolean halting result unchanged. -/
def Instruction.mapState {n m : Nat} (rename : Fin n → Fin m) :
    Instruction n → Instruction m
  | .halt b => .halt b
  | .step a d q => .step a d (rename q)

/-- A deterministic single-tape Turing machine: control states `Fin (states + 1)`,
a start state, and an instruction for every control state and scanned symbol. -/
structure Machine where
  states : Nat
  start : Fin (states + 1)
  code : Fin (states + 1) → Symbol → Instruction (states + 1)

/-- A configuration of `M`: control state and tape (with head). -/
structure Config (M : Machine) where
  state : Fin (M.states + 1)
  tape : Tape

/-- The initial configuration on `input`: start state, input tape (`Tape.ofInput`). -/
def initial (M : Machine) (input : List Bool) : Config M :=
  ⟨M.start, Tape.ofInput input⟩

/-- One step from `c`: `.inl (b, tape)` on `halt b`, else the next configuration. -/
def step (M : Machine) (c : Config M) : (Bool × Tape) ⊕ Config M :=
  match M.code c.state c.tape.read with
  | .halt b => .inl (b, c.tape)
  | .step a d q => .inr ⟨q, (c.tape.write a).move d⟩

/-- `run M fuel c` executes at most `fuel` steps from `c`. It is `some (b, t)` if
the machine executes `halt b` within these steps (halting counts as a step),
`t` being the final tape, and `none` if it has not halted after `fuel` steps. -/
def run (M : Machine) : Nat → Config M → Option (Bool × Tape)
  | 0, _ => none
  | fuel + 1, c =>
    match M.code c.state c.tape.read with
    | .halt b => some (b, c.tape)
    | .step a d q => run M fuel ⟨q, (c.tape.write a).move d⟩

/-- `run` from the initial configuration on `input`. -/
def runInput (M : Machine) (fuel : Nat) (input : List Bool) :
    Option (Bool × Tape) := run M fuel (initial M input)

/-- The fuel interpreter executes precisely one local instruction at a time. -/
theorem run_succ (M : Machine) (fuel : Nat) (c : Config M) :
    run M (fuel + 1) c =
      match step M c with
      | .inl result => some result
      | .inr next => run M fuel next := by
  cases h : M.code c.state c.tape.read <;> simp [run, step, h]

/-- A state relabelling preserving every transition simulates a machine with
exactly the same fuel. This includes nonhalting computations and the final tape;
there is no unproved instruction-cost abstraction. -/
theorem run_rename (M N : Machine)
    (rename : Fin (M.states + 1) → Fin (N.states + 1))
    (hcode : ∀ q a, N.code (rename q) a = (M.code q a).mapState rename)
    (fuel : Nat) (c : Config M) :
    run N fuel ⟨rename c.state, c.tape⟩ = run M fuel c := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, hcode]
    cases hc : M.code c.state c.tape.read with
    | halt b => rfl
    | step a d q => exact ih ⟨q, (c.tape.write a).move d⟩

/-- Additional fuel preserves an already observed halt and its complete tape. -/
theorem run_add (M : Machine) (fuel extra : Nat) (c : Config M)
    (result : Bool × Tape) (h : run M fuel c = some result) :
    run M (fuel + extra) c = some result := by
  induction fuel generalizing c with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : M.code c.state c.tape.read with
    | halt b =>
      simpa [run, hc, Nat.succ_add] using h
    | step a d q =>
      simp only [run, hc] at h
      simpa [run, hc, Nat.succ_add] using ih _ h

/-- Fuel monotonicity in its usual order formulation. -/
theorem run_mono (M : Machine) {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (c : Config M) (result : Bool × Tape)
    (h : run M fuel c = some result) : run M fuel' c = some result := by
  have heq : fuel + (fuel' - fuel) = fuel' := by omega
  rw [← heq]
  exact run_add M fuel (fuel' - fuel) c result h

/-- Two halting observations of one initial configuration agree, even when
they use different time bounds. -/
theorem run_deterministic (M : Machine) {fuel fuel' : Nat} (c : Config M)
    {result result' : Bool × Tape}
    (h : run M fuel c = some result) (h' : run M fuel' c = some result') :
    result = result' := by
  have h₁ := run_mono M (Nat.le_max_left fuel fuel') c result h
  have h₂ := run_mono M (Nat.le_max_right fuel fuel') c result' h'
  exact Option.some.inj (h₁.symm.trans h₂)

/-- A run can store at most two additional cells per executed instruction.
This deliberately loose bound follows directly from local tape operations. -/
theorem run_size_le (M : Machine) (fuel : Nat) (c : Config M)
    (result : Bool × Tape) (h : run M fuel c = some result) :
    result.2.size ≤ c.tape.size + 2 * fuel := by
  induction fuel generalizing c with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hc : M.code c.state c.tape.read with
    | halt b =>
      simp only [run, hc, Option.some.injEq] at h
      rw [← h]
      simp
    | step a d q =>
      simp only [run, hc] at h
      have hr := ih _ h
      have hs := c.tape.move_write_size_le a d
      simp only at hr
      omega

/-- Every returned output has linear size in input length plus elapsed time. -/
theorem runInput_output_length_le (M : Machine) (fuel : Nat) (input : List Bool)
    (result : Bool × Tape) (h : runInput M fuel input = some result) :
    result.2.output.length ≤ input.length + 2 * fuel := by
  have hr := run_size_le M fuel (initial M input) result h
  have ho := result.2.output_length_le
  simp only [initial, Tape.size_ofInput] at hr
  omega

end Complexity

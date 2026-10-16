/- GID: D5/S0/Computability/BinaryMachine/StackCompiler
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackCompiler
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackCompiler supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackCompiler.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackMachine
import Lean.Elab.Tactic.Omega

/-!
# Elementary tape macros for a stack-machine compiler

These are concrete finite transition tables in `Complexity.Machine`, with
proved instruction counts. They are building blocks for a compiler; this file
does not yet assert a general stack-to-tape simulation.
-/

@[expose] public section

namespace Complexity.StackCompiler

def symbolState : Symbol → Fin 5
  | .blank => 0
  | .bit false => 1
  | .bit true => 2
  | .sep => 3

def stateSymbol (q : Fin 5) : Symbol :=
  if q = 0 then .blank else if q = 1 then .bit false else
    if q = 2 then .bit true else .sep

@[simp] theorem stateSymbol_symbolState (a : Symbol) :
    stateSymbol (symbolState a) = a := by
  cases a with
  | blank => rfl
  | bit b => cases b <;> rfl
  | sep => rfl

@[simp] theorem symbolState_ne_halt (a : Symbol) : symbolState a ≠ (4 : Fin 5) := by
  cases a with
  | blank => decide
  | bit b => cases b <;> decide
  | sep => decide

/-- Carry one symbol rightward, shifting every nonblank symbol one cell right.
The first blank is filled, and the machine halts on that final cell. -/
def insertMachine (first : Symbol) : Machine where
  states := 4
  start := symbolState first
  code q a :=
    if q = 4 then .halt true
    else if a = .blank then .step (stateSymbol q) .stay 4
    else .step (stateSymbol q) .right (symbolState a)

/-- The exact final tape of the right-shifting insertion macro. -/
def insertedTape (carry : Symbol) (left : List Symbol) : List Symbol → Tape
  | [] => ⟨left, [carry]⟩
  | a :: rest => insertedTape a (carry :: left) rest

/-- Inserting one cell into a nonblank suffix takes its length plus two
instructions, including the terminal halt instruction. -/
theorem insert_run (first carry : Symbol) (left right : List Symbol)
    (h : ∀ a ∈ right, a ≠ .blank) :
    run (insertMachine first) (right.length + 2)
      ⟨symbolState carry, ⟨left, right⟩⟩ =
        some (true, insertedTape carry left right) := by
  induction right generalizing carry left with
  | nil =>
    simp [run, insertMachine, Tape.read, Tape.write, Tape.move, insertedTape]
  | cons a rest ih =>
    have ha : a ≠ .blank := h a (by simp)
    have hr : ∀ b ∈ rest, b ≠ .blank := by
      intro b hb
      exact h b (by simp [hb])
    simpa [run, insertMachine, Tape.read, Tape.write, Tape.move, insertedTape,
      ha, Nat.add_assoc] using ih a (carry :: left) hr

theorem insertedTape_size (carry : Symbol) (left right : List Symbol) :
    (insertedTape carry left right).size = left.length + right.length + 1 := by
  induction right generalizing carry left with
  | nil => simp [insertedTape, Tape.size]
  | cons a rest ih =>
    simp only [insertedTape, ih, List.length_cons]
    omega

/-- The insertion macro preserves the linear tape contents and adds its carry
at the original head position. Only the final head position changes. -/
theorem insertedTape_contents (carry : Symbol) (left right : List Symbol) :
    (insertedTape carry left right).left.reverse ++
        (insertedTape carry left right).right = left.reverse ++ carry :: right := by
  induction right generalizing carry left with
  | nil => simp [insertedTape]
  | cons a rest ih =>
    simpa [insertedTape, List.reverse_cons, List.append_assoc] using
      ih a (carry :: left)

/-- Return to the left end of a contiguous nonblank region. -/
def rewindMachine : Machine where
  states := 1
  start := 0
  code q a :=
    if q = 1 then .halt true
    else if a = .blank then .step .blank .right 1
    else .step a .left 0

@[simp] theorem rewind_code_scan (a : Symbol) :
    rewindMachine.code 0 a =
      (if a = .blank then .step .blank .right 1 else .step a .left 0) := rfl

@[simp] theorem rewind_code_halt (a : Symbol) :
    rewindMachine.code 1 a = .halt true := rfl

theorem rewind_run (left : List Symbol) (head : Symbol) (right : List Symbol)
    (hh : head ≠ .blank) (hl : ∀ a ∈ left, a ≠ .blank) :
    run rewindMachine (left.length + 3) ⟨0, ⟨left, head :: right⟩⟩ =
      some (true, ⟨[.blank], left.reverse ++ head :: right⟩) := by
  induction left generalizing head right with
  | nil =>
    simp [run, Tape.read, Tape.write, Tape.move, hh]
  | cons a rest ih =>
    have ha : a ≠ .blank := hl a (by simp)
    have hr : ∀ b ∈ rest, b ≠ .blank := by
      intro b hb
      exact hl b (by simp [hb])
    simpa [run, Tape.read, Tape.write, Tape.move, hh,
      List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      ih a (head :: right) ha hr

/-- The same rewind contract when the left boundary blank is explicitly
represented; cells beyond that boundary are retained. -/
theorem rewind_boundary_run (left : List Symbol) (head : Symbol)
    (right back : List Symbol) (hh : head ≠ .blank)
    (hl : ∀ a ∈ left, a ≠ .blank) :
    run rewindMachine (left.length + 3)
      ⟨0, ⟨left ++ .blank :: back, head :: right⟩⟩ =
      some (true, ⟨.blank :: back, left.reverse ++ head :: right⟩) := by
  induction left generalizing head right with
  | nil => simp [run, Tape.read, Tape.write, Tape.move, hh]
  | cons a rest ih =>
    have ha : a ≠ .blank := hl a (by simp)
    have hr : ∀ b ∈ rest, b ≠ .blank := by
      intro b hb
      exact hl b (by simp [hb])
    simpa [run, Tape.read, Tape.write, Tape.move, hh,
      List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      ih a (head :: right) ha hr

theorem insertedTape_left_length (carry : Symbol) (left right : List Symbol) :
    (insertedTape carry left right).left.length = left.length + right.length := by
  induction right generalizing carry left with
  | nil => simp [insertedTape]
  | cons a rest ih => simp [insertedTape, ih, Nat.add_comm, Nat.add_left_comm]

theorem insertedTape_append_left (carry : Symbol) (left right back : List Symbol) :
    insertedTape carry (left ++ back) right =
      ⟨(insertedTape carry left right).left ++ back,
        (insertedTape carry left right).right⟩ := by
  induction right generalizing carry left with
  | nil => rfl
  | cons a rest ih => simpa [insertedTape] using ih a (carry :: left)

theorem insertedTape_nonblank (carry : Symbol) (left right : List Symbol)
    (hc : carry ≠ .blank) (hl : ∀ a ∈ left, a ≠ .blank)
    (hr : ∀ a ∈ right, a ≠ .blank) :
    (∀ a ∈ (insertedTape carry left right).left, a ≠ .blank) ∧
      ∃ a, a ≠ .blank ∧ (insertedTape carry left right).right = [a] := by
  induction right generalizing carry left with
  | nil => exact ⟨hl, carry, hc, rfl⟩
  | cons a rest ih =>
    apply ih a (carry :: left) (hr a (by simp))
    · intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · simpa [hb] using hc
      · exact hl b hb
    · intro b hb
      exact hr b (by simp [hb])

def deleteCarryState : Symbol → Fin 9
  | .blank => 5
  | .bit false => 6
  | .bit true => 7
  | .sep => 8

def deleteCarrySymbol (q : Fin 9) : Symbol :=
  if q = 5 then .blank else if q = 6 then .bit false else
    if q = 7 then .bit true else .sep

/-- Remove the current cell by shifting the subsequent nonblank suffix left.
The machine finishes on the newly blank final cell. -/
def deleteMachine : Machine where
  states := 8
  start := 0
  code q a :=
    if q = 0 then .step a .right 1
    else if q = 1 then
      if a = .blank then .step .blank .left 3
      else .step a .left (deleteCarryState a)
    else if q = 2 then .step a .right 1
    else if q = 3 then .step .blank .stay 4
    else if q = 4 then .halt true
    else .step (deleteCarrySymbol q) .right 2

@[simp] theorem delete_code_start (a : Symbol) :
    deleteMachine.code 0 a = .step a .right 1 := rfl

@[simp] theorem delete_code_read (a : Symbol) :
    deleteMachine.code 1 a =
      (if a = .blank then .step .blank .left 3
        else .step a .left (deleteCarryState a)) := rfl

@[simp] theorem delete_code_advance (a : Symbol) :
    deleteMachine.code 2 a = .step a .right 1 := rfl

@[simp] theorem delete_code_clear (a : Symbol) :
    deleteMachine.code 3 a = .step .blank .stay 4 := rfl

@[simp] theorem delete_code_halt (a : Symbol) :
    deleteMachine.code 4 a = .halt true := rfl

@[simp] theorem delete_code_carry (carry a : Symbol) :
    deleteMachine.code (deleteCarryState carry) a = .step carry .right 2 := by
  cases carry with
  | blank => rfl
  | bit b => cases b <;> rfl
  | sep => rfl

theorem delete_shift_run (placeholder : Symbol) (left right : List Symbol)
    (h : ∀ a ∈ right, a ≠ .blank) :
    run deleteMachine (3 * right.length + 3) ⟨1, ⟨placeholder :: left, right⟩⟩ =
      some (true, ⟨right.reverse ++ left, [.blank, .blank]⟩) := by
  induction right generalizing placeholder left with
  | nil => simp [run, Tape.read, Tape.write, Tape.move]
  | cons a rest ih =>
    have ha : a ≠ .blank := h a (by simp)
    have hr : ∀ b ∈ rest, b ≠ .blank := by
      intro b hb
      exact h b (by simp [hb])
    simpa [run, Tape.read, Tape.write, Tape.move, ha, Nat.mul_add,
      List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      ih a (a :: left) hr

/-- Exact execution time for deleting a cell before a nonblank suffix. -/
theorem delete_run (head : Symbol) (left right : List Symbol)
    (h : ∀ a ∈ right, a ≠ .blank) :
    run deleteMachine (3 * right.length + 4) ⟨0, ⟨left, head :: right⟩⟩ =
      some (true, ⟨right.reverse ++ left, [.blank, .blank]⟩) := by
  simpa [run, Tape.read, Tape.write, Tape.move, Nat.add_assoc] using
    delete_shift_run head left right h

theorem write_read_of_nonempty (t : Tape) (h : t.right ≠ []) :
    t.write t.read = t := by
  cases t with
  | mk left right =>
    cases right with
    | nil => simp at h
    | cons a rest => rfl

/-- Redirect successful termination to another finite control state; every
redirect is one genuine tape instruction. -/
def continueInstruction {m n : Nat} (rename : Fin m → Fin n)
    (next : Fin n) (read : Symbol) : Instruction m → Instruction n
  | .halt true => .step read .stay next
  | .halt false => .halt false
  | .step a d q => .step a d (rename q)

/-- Link a successful macro execution to a continuation without altering its
tape. A represented head cell is required because writing an implicit blank
materializes that blank in this tape representation. -/
theorem run_continue (M N : Machine)
    (rename : Fin (M.states + 1) → Fin (N.states + 1))
    (next : Fin (N.states + 1))
    (hcode : ∀ q a, N.code (rename q) a =
      continueInstruction rename next a (M.code q a))
    (fuel : Nat) (c : Config M) (t : Tape)
    (hrun : run M fuel c = some (true, t)) (ht : t.right ≠ [])
    (nextFuel : Nat) (result : Bool × Tape)
    (hnext : run N nextFuel ⟨next, t⟩ = some result) :
    run N (fuel + nextFuel) ⟨rename c.state, c.tape⟩ = some result := by
  induction fuel generalizing c with
  | zero => simp [run] at hrun
  | succ fuel ih =>
    cases hc : M.code c.state c.tape.read with
    | halt decision =>
      cases decision with
      | false => simp [run, hc] at hrun
      | true =>
        have hct : c.tape = t := by simpa [run, hc] using hrun
        have hw : c.tape.write c.tape.read = t := by
          rw [hct]
          exact write_read_of_nonempty t ht
        have hext := run_mono N (Nat.le_add_left nextFuel fuel) ⟨next, t⟩ result hnext
        simpa [Nat.succ_add, run, hcode, hc, continueInstruction, hw, Tape.move] using hext
    | step a d q =>
      simp only [run, hc] at hrun
      simpa [Nat.succ_add, run, hcode, hc, continueInstruction] using
        ih ⟨q, (c.tape.write a).move d⟩ hrun

def sequenceLeft (M N : Machine) (q : Fin (M.states + 1)) :
    Fin (M.states + N.states + 1 + 1) :=
  ⟨q.val, by have := q.isLt; omega⟩

def sequenceRight (M N : Machine) (q : Fin (N.states + 1)) :
    Fin (M.states + N.states + 1 + 1) :=
  ⟨M.states + 1 + q.val, by have := q.isLt; omega⟩

/-- A concrete finite machine that runs `M`, then starts `N` on `M`'s final
tape if `M` succeeds. A rejecting halt of `M` is preserved. -/
def sequenceMachine (M N : Machine) : Machine where
  states := M.states + N.states + 1
  start := sequenceLeft M N M.start
  code q a :=
    if h : q.val < M.states + 1 then
      continueInstruction (sequenceLeft M N) (sequenceRight M N N.start) a
        (M.code ⟨q.val, h⟩ a)
    else
      (N.code ⟨q.val - (M.states + 1), by have := q.isLt; omega⟩ a).mapState
        (sequenceRight M N)

theorem sequence_code_left (M N : Machine) (q : Fin (M.states + 1)) (a : Symbol) :
    (sequenceMachine M N).code (sequenceLeft M N q) a =
      continueInstruction (sequenceLeft M N) (sequenceRight M N N.start) a (M.code q a) := by
  simp [sequenceMachine, sequenceLeft, q.isLt]

theorem sequence_code_right (M N : Machine) (q : Fin (N.states + 1)) (a : Symbol) :
    (sequenceMachine M N).code (sequenceRight M N q) a =
      (N.code q a).mapState (sequenceRight M N) := by
  have h : ¬ M.states + 1 + q.val < M.states + 1 := by omega
  simp [sequenceMachine, sequenceRight, h]

/-- Sequential composition with an additive instruction budget. -/
theorem sequence_run (M N : Machine) (fuel nextFuel : Nat) (c : Config M)
    (t : Tape) (result : Bool × Tape)
    (hrun : run M fuel c = some (true, t)) (ht : t.right ≠ [])
    (hnext : run N nextFuel ⟨N.start, t⟩ = some result) :
    run (sequenceMachine M N) (fuel + nextFuel)
      ⟨sequenceLeft M N c.state, c.tape⟩ = some result := by
  apply run_continue M (sequenceMachine M N) (sequenceLeft M N)
    (sequenceRight M N N.start) (sequence_code_left M N) fuel c t hrun ht nextFuel result
  rw [run_rename N (sequenceMachine M N) (sequenceRight M N)
    (sequence_code_right M N) nextFuel ⟨N.start, t⟩]
  exact hnext

def insertRewindMachine (carry : Symbol) : Machine :=
  sequenceMachine (insertMachine carry) rewindMachine

/-- A linked insertion-and-rewind machine, starting inside a nonblank region
whose left boundary blank is represented explicitly. -/
theorem insert_rewind_run (carry : Symbol) (left right back : List Symbol)
    (hc : carry ≠ .blank) (hl : ∀ a ∈ left, a ≠ .blank)
    (hr : ∀ a ∈ right, a ≠ .blank) :
    run (insertRewindMachine carry)
      ((right.length + 2) + (left.length + right.length + 3))
      ⟨(insertRewindMachine carry).start, ⟨left ++ .blank :: back, right⟩⟩ =
      some (true, ⟨.blank :: back, left.reverse ++ carry :: right⟩) := by
  let t := insertedTape carry left right
  obtain ⟨htleft, a, ha, htright⟩ := insertedTape_nonblank carry left right hc hl hr
  have hins := insert_run carry carry (left ++ .blank :: back) right hr
  rw [insertedTape_append_left] at hins
  have hrew := rewind_boundary_run t.left a [] back ha htleft
  have hcontents : t.left.reverse ++ [a] = left.reverse ++ carry :: right := by
    rw [← htright]
    exact insertedTape_contents carry left right
  rw [hcontents] at hrew
  have hlen : t.left.length = left.length + right.length :=
    insertedTape_left_length carry left right
  rw [hlen, ← htright] at hrew
  exact sequence_run (insertMachine carry) rewindMachine (right.length + 2)
    (left.length + right.length + 3) ⟨symbolState carry, ⟨left ++ .blank :: back, right⟩⟩
    ⟨t.left ++ .blank :: back, t.right⟩ _ hins (by simp [t, htright]) hrew

/-- Skip a fixed number of separators, retaining only a finite counter. -/
@[reducible] def seekMachine (register : Nat) : Machine where
  states := register + 1
  start := ⟨register + 1, by omega⟩
  code q a :=
    if q.val = 0 then .halt true
    else match a with
    | .blank => .halt false
    | .bit b => .step (.bit b) .right q
    | .sep => .step .sep .right ⟨q.val - 1, by have := q.isLt; omega⟩

theorem seek_code_bit (register : Nat) (q : Fin (register + 1 + 1))
    (hq : q ≠ 0) (b : Bool) :
      (seekMachine register).code q (.bit b) = .step (.bit b) .right q := by
  have hv : q.val ≠ 0 := fun h => hq (Fin.ext h)
  simp [seekMachine, hv]

@[simp] theorem seek_code_halt (register : Nat) (a : Symbol) :
    (seekMachine register).code 0 a = .halt true := by
  simp [seekMachine]

theorem seek_code_separator (register : Nat) (q : Fin (register + 1 + 1))
    (hq : q ≠ 0) :
    (seekMachine register).code q .sep =
      .step .sep .right (⟨q.val - 1, by have := q.isLt; omega⟩ : Fin (register + 1 + 1)) := by
  have hv : q.val ≠ 0 := fun h => hq (Fin.ext h)
  simp [seekMachine, hv]

theorem seek_separator_run (register : Nat) (q : Fin (register + 1 + 1))
    (hq : q ≠ 0) (left right : List Symbol) (fuel : Nat) :
    run (seekMachine register) (fuel + 1) ⟨q, ⟨left, .sep :: right⟩⟩ =
    run (seekMachine register) fuel
      ⟨⟨q.val - 1, by change q.val - 1 < register + 1 + 1; have := q.isLt; omega⟩,
        ⟨.sep :: left, right⟩⟩ := by
  simp [run, Tape.read, Tape.write, Tape.move, hq]

/-- Scanning a run of bits preserves the finite separator counter and costs
one machine instruction per bit. -/
theorem seek_bits_run (register : Nat) (q : Fin (register + 1 + 1))
    (hq : q ≠ 0) (bits : List Bool) (left right : List Symbol) (fuel : Nat) :
    run (seekMachine register) (bits.length + fuel)
      ⟨q, ⟨left, bits.map Symbol.bit ++ right⟩⟩ =
    run (seekMachine register) fuel
      ⟨q, ⟨(bits.map Symbol.bit).reverse ++ left, right⟩⟩ := by
  induction bits generalizing left with
  | nil => simp
  | cons b rest ih =>
    simpa [Nat.succ_add, run, Tape.read, Tape.write, Tape.move,
      hq, List.reverse_cons, List.append_assoc] using
      ih (Symbol.bit b :: left)

/-- The region preceding a chosen stack: each earlier stack has a separator
followed by its bits. The chosen stack's separator follows this region. -/
def stackPrefix : List (List Bool) → List Symbol
  | [] => []
  | bits :: rest => .sep :: (bits.map Symbol.bit ++ stackPrefix rest)

theorem seek_run (register : Nat) (before : List (List Bool))
    (hbound : before.length + 1 < register + 1 + 1)
    (left right : List Symbol) :
    run (seekMachine register) ((stackPrefix before).length + 2)
      ⟨⟨before.length + 1, hbound⟩, ⟨left, stackPrefix before ++ .sep :: right⟩⟩ =
      some (true, ⟨.sep :: ((stackPrefix before).reverse ++ left), right⟩) := by
  induction before generalizing left with
  | nil =>
    simp [stackPrefix, run, Tape.read, Tape.write, Tape.move]
  | cons bits rest ih =>
    have hrest : rest.length + 1 < register + 1 + 1 := by simp at hbound; omega
    have hq : (⟨rest.length + 1, hrest⟩ : Fin (register + 1 + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hq' : (⟨(bits :: rest).length + 1, hbound⟩ : Fin (register + 1 + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hskip := seek_bits_run register ⟨rest.length + 1, hrest⟩ hq bits
      (.sep :: left) (stackPrefix rest ++ .sep :: right) ((stackPrefix rest).length + 2)
    have hresult := hskip.trans (ih hrest ((bits.map Symbol.bit).reverse ++ .sep :: left))
    have htime : (stackPrefix (bits :: rest)).length + 2 =
        (bits.length + ((stackPrefix rest).length + 2)) + 1 := by
      simp [stackPrefix]
      omega
    rw [htime]
    simp only [stackPrefix, List.cons_append, List.append_assoc]
    rw [seek_separator_run register _ hq']
    simpa [stackPrefix, List.reverse_cons, List.reverse_append, List.append_assoc] using hresult

theorem stackPrefix_nonblank (before : List (List Bool)) :
    ∀ a ∈ stackPrefix before, a ≠ .blank := by
  induction before with
  | nil => simp [stackPrefix]
  | cons bits rest ih =>
    intro a ha
    simp only [stackPrefix, List.mem_cons, List.mem_append, List.mem_map] at ha
    rcases ha with ha | ⟨b, _, hb⟩ | ha
    · subst a
      simp
    · subst a
      simp
    · exact ih a ha

/-- Push one bit onto a specified stack in the separator-delimited tape
representation, then return to its left boundary. -/
def pushMachine (register : Nat) (value : Bool) : Machine :=
  sequenceMachine (seekMachine register) (insertRewindMachine (.bit value))

theorem push_register_run_general (capacity : Nat) (before : List (List Bool))
    (hcapacity : before.length ≤ capacity) (value : Bool)
    (right : List Symbol) (hr : ∀ a ∈ right, a ≠ .blank) (hne : right ≠ []) :
    run (pushMachine capacity value)
      (2 * ((stackPrefix before).length + 1 + right.length) + 6)
      ⟨sequenceLeft (seekMachine capacity) (insertRewindMachine (.bit value))
          ⟨before.length + 1, by change before.length + 1 < capacity + 1 + 1; omega⟩,
        ⟨[.blank], stackPrefix before ++ .sep :: right⟩⟩ =
      some (true, ⟨[.blank], stackPrefix before ++ .sep :: .bit value :: right⟩) := by
  have hseek := seek_run capacity before (by omega) [.blank] right
  have hl : ∀ a ∈ .sep :: (stackPrefix before).reverse, a ≠ .blank := by
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      decide
    · exact stackPrefix_nonblank before a (by simpa using ha)
  have hins := insert_rewind_run (.bit value) (.sep :: (stackPrefix before).reverse)
    right [] (by simp) hl hr
  have hnext :
      run (insertRewindMachine (.bit value))
        ((right.length + 2) + ((stackPrefix before).length + 1 + right.length + 3))
        ⟨(insertRewindMachine (.bit value)).start,
          ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), right⟩⟩ =
      some (true, ⟨[.blank], stackPrefix before ++ .sep :: .bit value :: right⟩) := by
    simpa [List.reverse_cons, List.append_assoc] using hins
  have hseq := sequence_run (seekMachine capacity) (insertRewindMachine (.bit value))
    ((stackPrefix before).length + 2)
    ((right.length + 2) + ((stackPrefix before).length + 1 + right.length + 3))
    ⟨⟨before.length + 1, by change before.length + 1 < capacity + 1 + 1; omega⟩,
      ⟨[.blank], stackPrefix before ++ .sep :: right⟩⟩
    ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), right⟩ _ hseek hne hnext
  have htime : (stackPrefix before).length + 2 +
      (right.length + 2 + ((stackPrefix before).length + 1 + right.length + 3)) =
      2 * ((stackPrefix before).length + 1 + right.length) + 6 := by omega
  rw [htime] at hseq
  exact hseq

theorem push_register_run (before : List (List Bool)) (value : Bool)
    (right : List Symbol) (hr : ∀ a ∈ right, a ≠ .blank) (hne : right ≠ []) :
    run (pushMachine before.length value)
      (2 * ((stackPrefix before).length + 1 + right.length) + 6)
      ⟨(pushMachine before.length value).start,
        ⟨[.blank], stackPrefix before ++ .sep :: right⟩⟩ =
      some (true, ⟨[.blank], stackPrefix before ++ .sep :: .bit value :: right⟩) :=
  push_register_run_general before.length before (Nat.le_refl _) value right hr hne

end Complexity.StackCompiler

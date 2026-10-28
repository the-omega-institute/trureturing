/- GID: D5/S0/Computability/BinaryMachine/StackPop
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackPop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine StackPop supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/StackPop.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.StackCompiler
public import D5.S0.Computability.BinaryMachine.TapeEquiv
import Lean.Elab.Tactic.Omega

/-!
Concrete deletion and return-to-boundary macros for the stack-machine compiler.
The controller inspects the stack's top cell before entering these macros, so
the removed bit and the continuation branch are already in finite control.
-/

@[expose] public section

namespace Complexity.StackCompiler

set_option backward.isDefEq.respectTransparency false

@[simp] theorem sequenceMachine_start (M N : Machine) :
    (sequenceMachine M N).start = sequenceLeft M N M.start := rfl

@[simp] theorem deleteMachine_start : deleteMachine.start = 0 := rfl

@[simp] theorem rewindMachine_start : rewindMachine.start = 0 := rfl

/-- Move one cell left, preserving the scanned cell, then halt successfully. -/
def moveLeftMachine : Machine where
  states := 1
  start := 0
  code q a := if q = 0 then .step a .left 1 else .halt true

theorem moveLeft_run (head previous : Symbol) (left right : List Symbol) :
    run moveLeftMachine 2 ⟨moveLeftMachine.start, ⟨previous :: left, head :: right⟩⟩ =
      some (true, ⟨left, previous :: head :: right⟩) := by
  simp [moveLeftMachine, run, Tape.read, Tape.write, Tape.move]

/-- From the first blank after a nonblank region, return to its beginning. -/
def rewindFromBlankMachine : Machine := sequenceMachine moveLeftMachine rewindMachine

theorem rewind_from_blank_run (beforeCells back right : List Symbol)
    (hp : beforeCells ≠ []) (hn : ∀ a ∈ beforeCells, a ≠ .blank) :
    run rewindFromBlankMachine (beforeCells.length + 4)
      ⟨rewindFromBlankMachine.start, ⟨beforeCells ++ .blank :: back, .blank :: right⟩⟩ =
      some (true, ⟨.blank :: back, beforeCells.reverse ++ .blank :: right⟩) := by
  cases beforeCells with
  | nil => simp at hp
  | cons a rest =>
    have ha := hn a (by simp)
    have hr : ∀ b ∈ rest, b ≠ .blank := fun b hb => hn b (by simp [hb])
    have hm := moveLeft_run .blank a (rest ++ .blank :: back) right
    have hw := rewind_boundary_run rest a (.blank :: right) back ha hr
    have hs := sequence_run moveLeftMachine rewindMachine 2 (rest.length + 3)
      ⟨moveLeftMachine.start, ⟨a :: (rest ++ .blank :: back), .blank :: right⟩⟩
      ⟨rest ++ .blank :: back, a :: .blank :: right⟩ _ hm (by simp) hw
    simpa [rewindFromBlankMachine, List.reverse_cons, List.append_assoc,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- Delete one cell, shift the suffix left, and return to the boundary. -/
def deleteRewindMachine : Machine := sequenceMachine deleteMachine rewindFromBlankMachine

/-- The exact tape after deletion has two explicit trailing blanks. Its
nonblank contents are precisely the original contents with the head removed. -/
theorem delete_rewind_run (head : Symbol) (beforeCells suffix : List Symbol)
    (hp : beforeCells ≠ []) (hbeforeCells : ∀ a ∈ beforeCells, a ≠ .blank)
    (hsuffix : ∀ a ∈ suffix, a ≠ .blank) :
    run deleteRewindMachine (beforeCells.length + 4 * suffix.length + 8)
      ⟨deleteRewindMachine.start, ⟨beforeCells ++ [.blank], head :: suffix⟩⟩ =
      some (true, ⟨[.blank], beforeCells.reverse ++ suffix ++ [.blank, .blank]⟩) := by
  have hd := delete_run head (beforeCells ++ [.blank]) suffix hsuffix
  rw [← deleteMachine_start] at hd
  have hn : ∀ a ∈ suffix.reverse ++ beforeCells, a ≠ .blank := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hsuffix a (by simpa using ha)
    · exact hbeforeCells a ha
  have hne : suffix.reverse ++ beforeCells ≠ [] := by
    intro h
    exact hp (List.append_eq_nil_iff.mp h).2
  have hw := rewind_from_blank_run (suffix.reverse ++ beforeCells) [] [.blank] hne hn
  have hs := sequence_run deleteMachine rewindFromBlankMachine
    (3 * suffix.length + 4) ((suffix.reverse ++ beforeCells).length + 4)
    ⟨deleteMachine.start, ⟨beforeCells ++ [.blank], head :: suffix⟩⟩
    ⟨suffix.reverse ++ (beforeCells ++ [.blank]), [.blank, .blank]⟩ _ hd (by simp)
    (by simpa only [List.append_assoc] using hw)
  have htime : (3 * suffix.length + 4) + ((suffix.reverse ++ beforeCells).length + 4) =
      beforeCells.length + 4 * suffix.length + 8 := by
    simp only [List.length_append, List.length_reverse]
    omega
  rw [htime] at hs
  simpa only [deleteRewindMachine, sequenceMachine_start, List.reverse_append, List.reverse_reverse,
    List.append_assoc] using hs

/-- Explicit trailing blanks in the macro's output are semantically invisible. -/
theorem delete_rewind_equivalent (beforeCells suffix : List Symbol) :
    (⟨[.blank], beforeCells.reverse ++ suffix ++ [.blank, .blank]⟩ : Tape).Equivalent
      ⟨[.blank], beforeCells.reverse ++ suffix⟩ := by
  exact ⟨BlankEq.refl _, BlankEq.append_blanks _ 2⟩

/-- A deletion from any equivalent tape representation has the same bounded
behavior and returns a tape equivalent to the canonical updated encoding. -/
theorem delete_rewind_of_equivalent (head : Symbol) (beforeCells suffix : List Symbol)
    (hp : beforeCells ≠ []) (hbeforeCells : ∀ a ∈ beforeCells, a ≠ .blank)
    (hsuffix : ∀ a ∈ suffix, a ≠ .blank) (t : Tape)
    (ht : (⟨beforeCells ++ [.blank], head :: suffix⟩ : Tape).Equivalent t) :
    ∃ out, run deleteRewindMachine (beforeCells.length + 4 * suffix.length + 8)
      ⟨deleteRewindMachine.start, t⟩ = some (true, out) ∧
      out.Equivalent ⟨[.blank], beforeCells.reverse ++ suffix⟩ := by
  obtain ⟨out, hr, he⟩ := run_some_of_equivalent deleteRewindMachine
    (beforeCells.length + 4 * suffix.length + 8) deleteRewindMachine.start
    ⟨beforeCells ++ [.blank], head :: suffix⟩ t ht true
    ⟨[.blank], beforeCells.reverse ++ suffix ++ [.blank, .blank]⟩
    (delete_rewind_run head beforeCells suffix hp hbeforeCells hsuffix)
  exact ⟨out, hr, he.symm.trans (delete_rewind_equivalent beforeCells suffix)⟩

/-- Returning after a peek or an empty-stack test leaves the register encoding
unchanged. The current head may be a bit or the next separator. -/
theorem rewind_register_run (before : List (List Bool)) (head : Symbol)
    (right : List Symbol) (hh : head ≠ .blank) :
    run rewindMachine ((stackPrefix before).length + 4)
      ⟨rewindMachine.start,
        ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), head :: right⟩⟩ =
      some (true, ⟨[.blank], stackPrefix before ++ .sep :: head :: right⟩) := by
  have hn : ∀ a ∈ .sep :: (stackPrefix before).reverse, a ≠ .blank := by
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      decide
    · exact stackPrefix_nonblank before a (by simpa using ha)
  have h := rewind_boundary_run (.sep :: (stackPrefix before).reverse) head right [] hh hn
  simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, rewindMachine] using h

/-- Specialization of deletion to a nonempty stack immediately after seeking
its separator. All earlier stacks are restored unchanged. -/
theorem pop_register_run (before : List (List Bool)) (bit : Bool)
    (suffix : List Symbol) (hsuffix : ∀ a ∈ suffix, a ≠ .blank) :
    run deleteRewindMachine ((stackPrefix before).length + 4 * suffix.length + 9)
      ⟨deleteRewindMachine.start,
        ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), .bit bit :: suffix⟩⟩ =
      some (true,
        ⟨[.blank], stackPrefix before ++ .sep :: (suffix ++ [.blank, .blank])⟩) := by
  have hn : ∀ a ∈ .sep :: (stackPrefix before).reverse, a ≠ .blank := by
    intro a ha
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      decide
    · exact stackPrefix_nonblank before a (by simpa using ha)
  have h := delete_rewind_run (.bit bit) (.sep :: (stackPrefix before).reverse)
    suffix (by simp) hn hsuffix
  have htime : (.sep :: (stackPrefix before).reverse).length + 4 * suffix.length + 8 =
      (stackPrefix before).length + 4 * suffix.length + 9 := by
    simp only [List.length_cons, List.length_reverse]
    omega
  rw [htime] at h
  simpa only [List.reverse_cons, List.reverse_reverse, List.singleton_append,
    List.cons_append, List.append_assoc, List.nil_append] using h

theorem push_register_of_equivalent (before : List (List Bool)) (value : Bool)
    (right : List Symbol) (hr : ∀ a ∈ right, a ≠ .blank) (hne : right ≠ [])
    (t : Tape)
    (ht : (⟨[.blank], stackPrefix before ++ .sep :: right⟩ : Tape).Equivalent t) :
    ∃ out, run (pushMachine before.length value)
      (2 * ((stackPrefix before).length + 1 + right.length) + 6)
      ⟨(pushMachine before.length value).start, t⟩ = some (true, out) ∧
      out.Equivalent ⟨[.blank], stackPrefix before ++ .sep :: .bit value :: right⟩ := by
  obtain ⟨out, hrun, he⟩ := run_some_of_equivalent (pushMachine before.length value)
    (2 * ((stackPrefix before).length + 1 + right.length) + 6)
    (pushMachine before.length value).start
    ⟨[.blank], stackPrefix before ++ .sep :: right⟩ t ht true
    ⟨[.blank], stackPrefix before ++ .sep :: .bit value :: right⟩
    (push_register_run before value right hr hne)
  exact ⟨out, hrun, he.symm⟩

theorem rewind_register_of_equivalent (before : List (List Bool)) (head : Symbol)
    (right : List Symbol) (hh : head ≠ .blank) (t : Tape)
    (ht : (⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), head :: right⟩ : Tape).Equivalent t) :
    ∃ out, run rewindMachine ((stackPrefix before).length + 4)
      ⟨rewindMachine.start, t⟩ = some (true, out) ∧
      out.Equivalent ⟨[.blank], stackPrefix before ++ .sep :: head :: right⟩ := by
  obtain ⟨out, hrun, he⟩ := run_some_of_equivalent rewindMachine
    ((stackPrefix before).length + 4) rewindMachine.start
    ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), head :: right⟩ t ht true
    ⟨[.blank], stackPrefix before ++ .sep :: head :: right⟩
    (rewind_register_run before head right hh)
  exact ⟨out, hrun, he.symm⟩

theorem pop_register_of_equivalent (before : List (List Bool)) (bit : Bool)
    (suffix : List Symbol) (hsuffix : ∀ a ∈ suffix, a ≠ .blank) (t : Tape)
    (ht : (⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), .bit bit :: suffix⟩ : Tape).Equivalent t) :
    ∃ out, run deleteRewindMachine ((stackPrefix before).length + 4 * suffix.length + 9)
      ⟨deleteRewindMachine.start, t⟩ = some (true, out) ∧
      out.Equivalent ⟨[.blank], stackPrefix before ++ .sep :: suffix⟩ := by
  obtain ⟨out, hrun, he⟩ := run_some_of_equivalent deleteRewindMachine
    ((stackPrefix before).length + 4 * suffix.length + 9) deleteRewindMachine.start
    ⟨.sep :: ((stackPrefix before).reverse ++ [.blank]), .bit bit :: suffix⟩ t ht true
    ⟨[.blank], stackPrefix before ++ .sep :: (suffix ++ [.blank, .blank])⟩
    (pop_register_run before bit suffix hsuffix)
  have hblank : (⟨[.blank], stackPrefix before ++ .sep :: (suffix ++ [.blank, .blank])⟩ : Tape).Equivalent
      ⟨[.blank], stackPrefix before ++ .sep :: suffix⟩ := by
    have hb := BlankEq.append_blanks (stackPrefix before ++ .sep :: suffix) 2
    exact ⟨BlankEq.refl _, by simpa [List.append_assoc] using hb⟩
  exact ⟨out, hrun, he.symm.trans hblank⟩

end Complexity.StackCompiler

/- GID: D5/S0/Computability/BinaryMachine/UnaryWords
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/UnaryWords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed unary-prefix and finite paired-word decoding supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4, revision
3e603e795b44fedcf7d6dd65b7d1e30547ead925. Apache-2.0; see
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Original proof bodies are preserved. UnaryWords retains only unary-prefix
declarations from SAT and SATBounds; no SAT language or classification is ported.
-/

public import D5.S0.Computability.BinaryMachine.Classes
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace Complexity.SAT

/-- Binary words (the same type as `Complexity.Word`). -/
abbrev Word := List Bool

/-- A parser reads a value from the front of a word and returns it together with
the rest of the word, or fails. -/
abbrev Parser (α : Type) := Word → Option (α × Word)

/-- The unary code of `n`: `n` ones followed by a zero. -/
def writeNat : Nat → Word
  | 0 => [false]
  | n + 1 => true :: writeNat n

/-- Parse a unary code, as written by `writeNat`. -/
def readNat : Parser Nat
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (n, tail) ← readNat rest
      pure (n + 1, tail)

@[simp] theorem readNat_writeNat (n : Nat) (rest : Word) :
    readNat (writeNat n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, readNat, ih]

/-- A successful unary parser determines exactly the consumed prefix. -/
theorem readNat_eq_some {input : Word} {n : Nat} {rest : Word}
    (h : readNat input = some (n, rest)) : input = writeNat n ++ rest := by
  induction input generalizing n with
  | nil => simp [readNat] at h
  | cons bit input ih =>
    cases bit with
    | false =>
      simp only [readNat, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hp : readNat input with
      | none => simp [readNat, hp] at h
      | some pair =>
        rcases pair with ⟨m, tail⟩
        simp [readNat, hp] at h
        rcases h with ⟨rfl, rfl⟩
        simp [writeNat, ih hp]


end Complexity.SAT

namespace Complexity.SATBounds
open Complexity.SAT

@[simp] theorem writeNat_length (n : Nat) : (writeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [writeNat, ih, Nat.add_assoc]


end Complexity.SATBounds

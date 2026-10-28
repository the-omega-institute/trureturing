/- GID: D5/S0/Computability/BinaryMachine/StackParse
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackParse
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

public import D5.S0.Computability.BinaryMachine.StackWords
public import D5.S0.Computability.BinaryMachine.UnaryWords
import Lean.Elab.Tactic.Omega

/-!
# Unary parsing by a finite Boolean stack program

The only data operations are one-bit pops and pushes.  The destination is
cleared before parsing; a missing false terminator is rejected.  Counts include
the clearing loop, the connecting jump, the terminating pop, and the halt.
-/

@[expose] public section

namespace Complexity.StackParse

open Complexity.StackMachine (Registers branch)
open Complexity.StackProgram Complexity.StackWords

/-- Consume a unary numeral, adding its true bits to the destination. -/
def readUnaryLoop {k : Nat} (src dst : Fin (k + 1)) : Program k (Fin 4) where
  start := 0
  code := fun q => if q = 0 then .pop src 1 2 3
    else if q = 1 then .halt false
    else if q = 2 then .halt true
    else .push dst true 0

/-- Parse a unary natural number into a freshly emptied unary register. -/
def readUnary {k : Nat} (src dst : Fin (k + 1)) : Program k (Sum Bool (Fin 4)) :=
  seq (clear dst) (readUnaryLoop src dst)

def readUnaryEncoding : Encoding (Sum Bool (Fin 4)) :=
  Encoding.bool.sum (Encoding.fin 3)

theorem writeNat_eq (n : Nat) :
    SAT.writeNat n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [SAT.writeNat, List.replicate_succ, ih]

/-- A common execution lemma covers both a terminator and end-of-input. -/
theorem exec_readUnaryLoop {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (n m : Nat) (success : Bool) (rest : List Bool) (r : Registers k)
    (hs : r src = List.replicate n true ++ (if success then false :: rest else []))
    (hd : r dst = List.replicate m true) :
    Exec (readUnaryLoop src dst) 0 r (2 * n + 2)
      (success, StackMachine.set (StackMachine.set r src (if success then rest else [])) dst
        (List.replicate (n + m) true)) := by
  induction n generalizing r m with
  | zero =>
    have hout : StackMachine.set (StackMachine.set r src (if success then rest else [])) dst
        (List.replicate m true) = StackMachine.set r src (if success then rest else []) := by
      rw [← hd]
      have hr : (StackMachine.set r src (if success then rest else [])) dst = r dst := by
        simp [Ne.symm hne]
      rw [← hr, set_unchanged]
    simp only [Nat.mul_zero, Nat.zero_add, hout]
    cases success with
    | false =>
      apply Exec.next (q' := 1) (r' := StackMachine.set r src [])
      · simp [StackProgram.step, readUnaryLoop, hs, branch]
      · exact .halt (by simp [StackProgram.step, readUnaryLoop])
    | true =>
      apply Exec.next (q' := 2) (r' := StackMachine.set r src rest)
      · simp [StackProgram.step, readUnaryLoop, hs, branch]
      · exact .halt (by simp [StackProgram.step, readUnaryLoop])
  | succ n ih =>
    let tail := List.replicate n true ++ (if success then false :: rest else [])
    let r' := StackMachine.set (StackMachine.set r src tail) dst (List.replicate (m + 1) true)
    have hs' : r' src = tail := by simp [r', hne]
    have hd' : r' dst = List.replicate (m + 1) true := by simp [r']
    have ht := ih (m + 1) r' hs' hd'
    have hpop : StackProgram.step (readUnaryLoop src dst) 0 r =
        .inr (3, StackMachine.set r src tail) := by
      simp [StackProgram.step, readUnaryLoop, hs, List.replicate_succ, branch, tail]
    have hpush : StackProgram.step (readUnaryLoop src dst) 3 (StackMachine.set r src tail) =
        .inr (0, r') := by
      simp [StackProgram.step, readUnaryLoop, r', Ne.symm hne, hd, List.replicate_succ]
    have hout : StackMachine.set (StackMachine.set r' src (if success then rest else [])) dst
        (List.replicate (n + (m + 1)) true) =
        StackMachine.set (StackMachine.set r src (if success then rest else [])) dst
        (List.replicate (n + 1 + m) true) := by
      funext a
      by_cases had : a = dst
      · subst a; simp [Nat.add_comm, Nat.add_left_comm]
      · by_cases has : a = src
        · subst a; simp [had]
        · simp [r', StackMachine.set, had, has]
    have hh := Exec.next hpop (Exec.next hpush ht)
    rw [hout] at hh
    simpa [Nat.mul_add, Nat.add_assoc] using hh

/-- Successful parsing, including all unchanged registers, with an exact cost. -/
theorem exec_readUnary_encoded {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (n : Nat) (rest : List Bool) (r : Registers k) (hs : r src = SAT.writeNat n ++ rest) :
    Exec (readUnary src dst) (.inl false) r ((r dst).length + 2 * n + 4)
      (true, StackMachine.set (StackMachine.set r src rest) dst (List.replicate n true)) := by
  let r₀ := StackMachine.set r dst []
  have hs₀ : r₀ src = List.replicate n true ++ (if true then false :: rest else []) := by
    simp [r₀, hne, hs, writeNat_eq, List.append_assoc]
  have hloop := exec_readUnaryLoop src dst hne n 0 true rest r₀ hs₀ (by simp [r₀])
  have hh := exec_seq (clear dst) (readUnaryLoop src dst) (exec_clear dst r) hloop
  have hout : StackMachine.set (StackMachine.set r₀ src rest) dst (List.replicate n true) =
      StackMachine.set (StackMachine.set r src rest) dst (List.replicate n true) := by
    funext a
    by_cases had : a = dst
    · subst a; simp
    · by_cases has : a = src
      · subst a; simp [had]
      · simp [r₀, StackMachine.set, had, has]
  have hcost : (r dst).length + 2 + (2 * n + 2) = (r dst).length + 2 * n + 4 := by omega
  rw [hcost] at hh
  simpa [readUnary, hout] using hh

/-- All-true input is malformed and is rejected after consuming every bit. -/
theorem exec_readUnary_malformed {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (n : Nat) (r : Registers k) (hs : r src = List.replicate n true) :
    Exec (readUnary src dst) (.inl false) r ((r dst).length + 2 * n + 4)
      (false, StackMachine.set (StackMachine.set r src []) dst (List.replicate n true)) := by
  let r₀ := StackMachine.set r dst []
  have hs₀ : r₀ src = List.replicate n true ++ (if false then false :: [] else []) := by
    simp [r₀, hne, hs]
  have hloop := exec_readUnaryLoop src dst hne n 0 false [] r₀ hs₀ (by simp [r₀])
  have hh := exec_seq (clear dst) (readUnaryLoop src dst) (exec_clear dst r) hloop
  have hout : StackMachine.set (StackMachine.set r₀ src []) dst (List.replicate n true) =
      StackMachine.set (StackMachine.set r src []) dst (List.replicate n true) := by
    funext a
    by_cases had : a = dst
    · subst a; simp
    · by_cases has : a = src
      · subst a; simp [had]
      · simp [r₀, StackMachine.set, had, has]
  have hcost : (r dst).length + 2 + (2 * n + 2) = (r dst).length + 2 * n + 4 := by omega
  rw [hcost] at hh
  simpa [readUnary, hout] using hh

theorem readNat_none_eq {input : List Bool} (h : SAT.readNat input = none) :
    input = List.replicate input.length true := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    cases b with
    | false => simp [SAT.readNat] at h
    | true =>
      cases hp : SAT.readNat input with
      | none =>
        simp only [List.length_cons, List.replicate_succ]
        exact congrArg (fun xs => true :: xs) (ih hp)
      | some result =>
        obtain ⟨n, rest⟩ := result
        simp [SAT.readNat, hp] at h

@[simp] theorem readNat_replicate (n : Nat) :
    SAT.readNat (List.replicate n true) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, SAT.readNat, ih]

theorem readNat_none_iff (input : List Bool) :
    SAT.readNat input = none ↔ input = List.replicate input.length true := by
  constructor
  · exact readNat_none_eq
  · intro h
    exact (congrArg SAT.readNat h).trans (readNat_replicate input.length)

/-- The complete register-level specification, on all input words. -/
def readUnaryResult {k : Nat} (src dst : Fin (k + 1)) (r : Registers k) :
    Bool × Registers k :=
  match SAT.readNat (r src) with
  | none => (false, StackMachine.set (StackMachine.set r src []) dst
      (List.replicate (r src).length true))
  | some (n, rest) => (true, StackMachine.set (StackMachine.set r src rest) dst
      (List.replicate n true))

/-- Exact instruction count; a failed parse consumes the entire source. -/
def readUnaryTime {k : Nat} (src dst : Fin (k + 1)) (r : Registers k) : Nat :=
  (r dst).length + 2 * (match SAT.readNat (r src) with
    | none => (r src).length
    | some (n, _) => n) + 4

theorem exec_readUnary {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (r : Registers k) :
    Exec (readUnary src dst) (readUnary src dst).start r (readUnaryTime src dst r)
      (readUnaryResult src dst r) := by
  cases hp : SAT.readNat (r src) with
  | none =>
    simpa [readUnary, seq, clear, readUnaryTime, readUnaryResult, hp] using
      exec_readUnary_malformed src dst hne (r src).length r (readNat_none_eq hp)
  | some result =>
    obtain ⟨n, rest⟩ := result
    simpa [readUnary, seq, clear, readUnaryTime, readUnaryResult, hp] using
      exec_readUnary_encoded src dst hne n rest r (Complexity.SAT.readNat_eq_some hp)

theorem readUnaryTime_le {k : Nat} (src dst : Fin (k + 1)) (r : Registers k) :
    readUnaryTime src dst r ≤ (r dst).length + 2 * (r src).length + 4 := by
  cases hp : SAT.readNat (r src) with
  | none => simp [readUnaryTime, hp]
  | some result =>
    obtain ⟨n, rest⟩ := result
    have hs := Complexity.SAT.readNat_eq_some hp
    have hlen := congrArg List.length hs
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    simp only [readUnaryTime, hp]
    omega

/-- Total correctness and a uniform linear bound for the actual stack instructions. -/
theorem readUnary_runs {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (r : Registers k) :
    ∃ t, t ≤ (r dst).length + 2 * (r src).length + 4 ∧
      Exec (readUnary src dst) (readUnary src dst).start r t (readUnaryResult src dst r) :=
  ⟨readUnaryTime src dst r, readUnaryTime_le src dst r, exec_readUnary src dst hne r⟩

/-- Compiling into explicit finite labels preserves the exact successful parse run. -/
theorem compiled_readUnary_encoded {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (n : Nat) (rest : List Bool) (r : Registers k) (hs : r src = SAT.writeNat n ++ rest) :
    StackMachine.run (compile (readUnary src dst) readUnaryEncoding)
      ((r dst).length + 2 * n + 4)
      ⟨(compile (readUnary src dst) readUnaryEncoding).start, r⟩ =
      some (true, StackMachine.set (StackMachine.set r src rest) dst (List.replicate n true)) :=
  compile_exec readUnaryEncoding (exec_readUnary_encoded src dst hne n rest r hs)

/-- A fixed linear fuel bound works for every input, including malformed words. -/
theorem compiled_readUnary_runs {k : Nat} (src dst : Fin (k + 1)) (hne : src ≠ dst)
    (r : Registers k) :
    StackMachine.run (compile (readUnary src dst) readUnaryEncoding)
      ((r dst).length + 2 * (r src).length + 4)
      ⟨(compile (readUnary src dst) readUnaryEncoding).start, r⟩ =
      some (readUnaryResult src dst r) := by
  apply StackMachine.run_mono _ (readUnaryTime_le src dst r)
  exact compile_exec readUnaryEncoding (exec_readUnary src dst hne r)

theorem readUnaryResult_frame {k : Nat} (src dst a : Fin (k + 1))
    (hs : a ≠ src) (hd : a ≠ dst) (r : Registers k) :
    (readUnaryResult src dst r).2 a = r a := by
  unfold readUnaryResult
  split <;> simp [hs, hd]

end Complexity.StackParse

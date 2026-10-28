/- GID: D5/S0/Computability/BinaryMachine/StackPair
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/StackPair
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

public import D5.S0.Computability.BinaryMachine.StackParse
public import D5.S0.Computability.BinaryMachine.Classes
import Lean.Elab.Tactic.Omega

/-! Primitive finite-control unpacking of the verifier's paired input word. -/

@[expose] public section

namespace Complexity.StackPair

open Complexity.StackProgram
open Complexity.StackMachine (Registers branch)
open Complexity.StackWords (set_overwrite set_unchanged)

abbrev R := Registers 6
def input : Fin 7 := 0
def certificate : Fin 7 := 1
def counter : Fin 7 := 2
def work : Fin 7 := 4
def scratch : Fin 7 := 5

def initial (word : List Bool) : R := fun j => if j = input then word else []
def unpacked (x y : List Bool) : R := fun j => if j = input then x else if j = certificate then y else []

def takeOne : Program 6 (Fin 5) where
  start := 0
  code := fun q => if q = 0 then .pop input 1 2 3
    else if q = 1 then .halt false
    else if q = 2 then .push work false 4
    else if q = 3 then .push work true 4
    else .halt true

theorem exec_takeOne_cons (r : R) (b : Bool) (tail : List Bool) (hr : r input = b :: tail) :
    Exec takeOne 0 r 3 (true, StackMachine.set (StackMachine.set r input tail) work (b :: r work)) := by
  have hp : StackProgram.step takeOne 0 r = .inr ((if b then 3 else 2), StackMachine.set r input tail) := by
    cases b <;> simp [StackProgram.step, takeOne, hr, branch]
  have hs : StackProgram.step takeOne (if b then 3 else 2) (StackMachine.set r input tail) =
      .inr (4, StackMachine.set (StackMachine.set r input tail) work (b :: r work)) := by
    cases b <;> simp [StackProgram.step, takeOne, work, input]
  exact .next hp (.next hs (.halt (by simp [StackProgram.step, takeOne])))

theorem exec_takeOne_empty (r : R) (hr : r input = []) : Exec takeOne 0 r 2 (false, r) := by
  have hset : StackMachine.set r input [] = r := by rw [← hr, set_unchanged]
  apply Exec.next (q' := 1) (r' := r)
  · simp [StackProgram.step, takeOne, hr, branch, hset]
  · exact .halt (by simp [StackProgram.step, takeOne])

def gather := whileCounter counter takeOne
def gatherEncoding := Encoding.bool.sum (Encoding.fin 4)

def gathered (r : R) (xs rest : List Bool) : R :=
  StackMachine.set (StackMachine.set (StackMachine.set r input rest) counter []) work (xs.reverse ++ r work)

theorem exec_gather (xs rest : List Bool) (r : R)
    (hi : r input = xs ++ rest) (hc : r counter = List.replicate xs.length true) :
    Exec gather gather.start r (4 * xs.length + 2) (true, gathered r xs rest) := by
  induction xs generalizing r with
  | nil =>
    have hh := exec_whileCounter_done counter takeOne r (by simpa using hc)
    have hout : gathered r [] rest = r := by
      funext a
      by_cases hw : a = work
      · subst a; simp [gathered]
      · by_cases hcounter : a = counter
        · subst a; simp [gathered, hw, hc]
        · by_cases hinput : a = input
          · subst a; simp [gathered, hw, hcounter, hi]
          · simp [gathered, StackMachine.set, hw, hcounter, hinput]
    simpa [gather, whileCounter, hout] using hh
  | cons b xs ih =>
    let r₀ := StackMachine.set r counter (List.replicate xs.length true)
    let r₁ := StackMachine.set (StackMachine.set r₀ input (xs ++ rest)) work (b :: r work)
    have hi₀ : r₀ input = b :: (xs ++ rest) := by simpa [r₀, input, counter] using hi
    have hbody := exec_takeOne_cons r₀ b (xs ++ rest) hi₀
    have hbody' : Exec takeOne takeOne.start r₀ 3 (true, r₁) := by
      simpa [takeOne, r₁, r₀, work, counter] using hbody
    have hi₁ : r₁ input = xs ++ rest := by simp [r₁, input, work]
    have hc₁ : r₁ counter = List.replicate xs.length true := by simp [r₁, r₀, input, work, counter]
    have hrest := ih r₁ hi₁ hc₁
    have hh := exec_whileCounter_next counter takeOne
      (by simpa [List.replicate_succ] using hc) hbody' hrest
    have hout : gathered r₁ xs rest = gathered r (b :: xs) rest := by
      funext a
      by_cases hw : a = work
      · subst a; simp [gathered, r₁, List.reverse_cons, List.append_assoc]
      · by_cases hcounter : a = counter
        · subst a; simp [gathered, hw]
        · by_cases hinput : a = input
          · subst a; simp [gathered, hw, hcounter]
          · simp [gathered, r₁, r₀, StackMachine.set, hw, hcounter, hinput]
    rw [hout] at hh
    have hcost : 3 + (4 * xs.length + 2) + 1 = 4 * (b :: xs).length + 2 := by simp; omega
    rw [hcost] at hh
    exact hh

theorem exec_gather_short (xs : List Bool) (n : Nat) (r : R)
    (hi : r input = xs) (hc : r counter = List.replicate n true) (hn : xs.length < n) :
    ∃ out, Exec gather gather.start r (4 * xs.length + 3) (false, out) := by
  induction xs generalizing n r with
  | nil =>
    cases n with
    | zero => simp at hn
    | succ n =>
      let r₀ := StackMachine.set r counter (List.replicate n true)
      have he := exec_takeOne_empty r₀ (by simpa [r₀, input, counter] using hi)
      have hh := exec_whileCounter_failure counter takeOne
        (by simpa [List.replicate_succ] using hc) he
      exact ⟨r₀, hh⟩
  | cons b xs ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      let r₀ := StackMachine.set r counter (List.replicate n true)
      let r₁ := StackMachine.set (StackMachine.set r₀ input xs) work (b :: r work)
      have hb := exec_takeOne_cons r₀ b xs (by simpa [r₀, input, counter] using hi)
      have hb' : Exec takeOne takeOne.start r₀ 3 (true, r₁) := by simpa [takeOne, r₁, r₀, work, counter] using hb
      obtain ⟨out, ht⟩ := ih n r₁ (by simp [r₁, input, work])
        (by simp [r₁, r₀, input, work, counter]) (by simpa using hn)
      have hh := exec_whileCounter_next counter takeOne
        (by simpa [List.replicate_succ] using hc) hb' ht
      refine ⟨out, ?_⟩
      have hcost : 3 + (4 * xs.length + 3) + 1 = 4 * (b :: xs).length + 3 := by simp; omega
      rw [hcost] at hh
      exact hh

def finish := seq (Complexity.StackWords.transfer input scratch)
  (seq (Complexity.StackWords.transfer scratch certificate) (Complexity.StackWords.transfer work input))
def finishEncoding := (Encoding.fin 3).sum ((Encoding.fin 3).sum (Encoding.fin 3))

def unpack := seq (Complexity.StackParse.readUnary input counter) (seq gather finish)
def unpackEncoding := Complexity.StackParse.readUnaryEncoding.sum (gatherEncoding.sum finishEncoding)

def afterGather (x y : List Bool) : R :=
  fun j => if j = input then y else if j = work then x.reverse else []

theorem exec_finish (x y : List Bool) :
    Exec finish finish.start (afterGather x y) (2 * x.length + 4 * y.length + 6) (true, unpacked x y) := by
  let r₀ := afterGather x y
  let r₁ := StackMachine.set (StackMachine.set r₀ input []) scratch ((r₀ input).reverse ++ r₀ scratch)
  let r₂ := StackMachine.set (StackMachine.set r₁ scratch []) certificate ((r₁ scratch).reverse ++ r₁ certificate)
  let r₃ := StackMachine.set (StackMachine.set r₂ work []) input ((r₂ work).reverse ++ r₂ input)
  have h₁ := Complexity.StackWords.exec_transfer input scratch (by decide) r₀
  have h₂ := Complexity.StackWords.exec_transfer scratch certificate (by decide) r₁
  have h₃ := Complexity.StackWords.exec_transfer work input (by decide) r₂
  have hh := exec_seq (Complexity.StackWords.transfer input scratch)
    (seq (Complexity.StackWords.transfer scratch certificate) (Complexity.StackWords.transfer work input)) h₁
    (exec_seq (Complexity.StackWords.transfer scratch certificate) (Complexity.StackWords.transfer work input) h₂ h₃)
  have hout : r₃ = unpacked x y := by
    funext a
    by_cases hi : a = input
    · subst a; simp [r₃, r₂, r₁, r₀, afterGather, unpacked, input, certificate, work, scratch]
    · by_cases hc : a = certificate
      · subst a; simp [r₃, r₂, r₁, r₀, afterGather, unpacked, input, certificate, work, scratch]
      · by_cases hw : a = work
        · subst a; simp [r₃, r₂, r₁, r₀, afterGather, unpacked, input, certificate, work, scratch]
        · by_cases hs : a = scratch
          · subst a; simp [r₃, r₂, r₁, r₀, afterGather, unpacked, input, certificate, work, scratch]
          · simp [r₃, r₂, r₁, r₀, afterGather, unpacked, StackMachine.set, hi, hc, hw, hs]
  change Exec _ _ _ _ (true, r₃) at hh
  rw [hout] at hh
  have hcost : 2 * (r₀ input).length + 2 +
      (2 * (r₁ scratch).length + 2 + (2 * (r₂ work).length + 2)) =
      2 * x.length + 4 * y.length + 6 := by
    simp [r₂, r₁, r₀, afterGather, input, certificate, work, scratch]
    omega
  rw [hcost] at hh
  exact hh

theorem exec_unpack_pair (x y : List Bool) :
    Exec unpack unpack.start (initial (pairWords x y)) (8 * x.length + 4 * y.length + 12)
      (true, unpacked x y) := by
  let r := initial (pairWords x y)
  let r₁ := StackMachine.set (StackMachine.set r input (x ++ y)) counter (List.replicate x.length true)
  have hp := Complexity.StackParse.exec_readUnary_encoded input counter (by decide) x.length (x ++ y) r
    (by simp [r, initial, pairWords, Complexity.StackParse.writeNat_eq, List.append_assoc])
  have hg := exec_gather x y r₁ (by simp [r₁, input, counter]) (by simp [r₁])
  have hmid : gathered r₁ x y = afterGather x y := by
    funext a
    by_cases hi : a = input
    · subst a; simp [gathered, afterGather, input, work, counter]
    · by_cases hw : a = work
      · subst a; simp [gathered, r₁, r, initial, afterGather, input, work, counter]
      · by_cases hc : a = counter
        · subst a; simp [gathered, afterGather, input, work, counter]
        · simp [gathered, r₁, r, initial, afterGather, StackMachine.set, hi, hw, hc]
  rw [hmid] at hg
  have hh := exec_seq (Complexity.StackParse.readUnary input counter) (seq gather finish) hp
    (exec_seq gather finish hg (exec_finish x y))
  have hcost : (r counter).length + 2 * x.length + 4 +
      (4 * x.length + 2 + (2 * x.length + 4 * y.length + 6)) =
      8 * x.length + 4 * y.length + 12 := by
    simp [r, initial, input, counter]
    omega
  rw [hcost] at hh
  exact hh

def decodePair (word : List Bool) : Option (List Bool × List Bool) :=
  match SAT.readNat word with
  | none => none
  | some (n, rest) => if n ≤ rest.length then some (rest.take n, rest.drop n) else none

theorem decodePair_eq_some_iff (word x y : List Bool) :
    decodePair word = some (x, y) ↔ word = pairWords x y := by
  constructor
  · intro h
    cases hn : SAT.readNat word with
    | none => simp [decodePair, hn] at h
    | some result =>
      obtain ⟨n, rest⟩ := result
      by_cases hle : n ≤ rest.length
      · have hp : rest.take n = x ∧ rest.drop n = y := by simpa [decodePair, hn, hle] using h
        rcases hp with ⟨rfl, rfl⟩
        have hlen : (rest.take n).length = n := by simp [List.length_take, Nat.min_eq_left hle]
        rw [Complexity.SAT.readNat_eq_some hn]
        simp [pairWords, Complexity.StackParse.writeNat_eq, hlen, List.append_assoc]
      · simp [decodePair, hn, hle] at h
  · rintro rfl
    have hpair : pairWords x y = SAT.writeNat x.length ++ (x ++ y) := by
      simp [pairWords, Complexity.StackParse.writeNat_eq, List.append_assoc]
    rw [hpair]
    simp [decodePair]

@[simp] theorem decodePair_pairWords (x y : List Bool) : decodePair (pairWords x y) = some (x, y) :=
  (decodePair_eq_some_iff _ x y).mpr rfl

theorem unpack_failure (word : List Bool) (h : decodePair word = none) :
    ∃ t out, t ≤ 4 * word.length + 8 ∧ Exec unpack unpack.start (initial word) t (false, out) := by
  cases hn : SAT.readNat word with
  | none =>
    have hall := Complexity.StackParse.readNat_none_eq hn
    have hp := Complexity.StackParse.exec_readUnary_malformed input counter (by decide) word.length (initial word)
      (by simpa [initial] using hall)
    have hh := exec_seq_failure (Complexity.StackParse.readUnary input counter) (seq gather finish) hp
    refine ⟨(initial word counter).length + 2 * word.length + 4, _, ?_, hh⟩
    simp [initial, input, counter]
    omega
  | some result =>
    obtain ⟨n, rest⟩ := result
    have hnlarge : rest.length < n := by
      by_cases hle : n ≤ rest.length
      · simp [decodePair, hn, hle] at h
      · omega
    let r := initial word
    let r₁ := StackMachine.set (StackMachine.set r input rest) counter (List.replicate n true)
    have hp := Complexity.StackParse.exec_readUnary_encoded input counter (by decide) n rest r
      (by simpa [r, initial] using Complexity.SAT.readNat_eq_some hn)
    obtain ⟨out, hg⟩ := exec_gather_short rest n r₁
      (by simp [r₁, input, counter]) (by simp [r₁]) hnlarge
    have hg' := exec_seq_failure gather finish hg
    have hh := exec_seq (Complexity.StackParse.readUnary input counter) (seq gather finish) hp hg'
    refine ⟨(r counter).length + 2 * n + 4 + (4 * rest.length + 3), out, ?_, hh⟩
    have hlen := congrArg List.length (Complexity.SAT.readNat_eq_some hn)
    simp only [List.length_append, SATBounds.writeNat_length] at hlen
    simp [r, initial, input, counter]
    omega

theorem unpack_runs (word : List Bool) :
    ∃ t out, t ≤ 4 * word.length + 8 ∧
      Exec unpack unpack.start (initial word) t ((decodePair word).isSome, out) ∧
      ∀ x y, decodePair word = some (x, y) → out = unpacked x y := by
  cases hp : decodePair word with
  | none =>
    obtain ⟨t, out, ht, he⟩ := unpack_failure word hp
    exact ⟨t, out, ht, by simpa [hp] using he, by intro x y hxy; simp at hxy⟩
  | some result =>
    obtain ⟨x, y⟩ := result
    have hword := (decodePair_eq_some_iff word x y).mp hp
    refine ⟨8 * x.length + 4 * y.length + 12, unpacked x y, ?_, ?_, ?_⟩
    · simp [hword, pairWords]
      omega
    · simpa [hword] using exec_unpack_pair x y
    · intro x' y' hxy
      have heq : x = x' ∧ y = y' := by simpa [hp] using hxy
      rcases heq with ⟨rfl, rfl⟩
      rfl

/-- Total paired-input decoding with an actual linear instruction budget. -/
theorem compiled_unpack_runs (word : List Bool) :
    ∃ out, StackMachine.runInput (compile unpack unpackEncoding) (4 * word.length + 8) word =
      some ((decodePair word).isSome, out) ∧
      ∀ x y, decodePair word = some (x, y) → out = unpacked x y := by
  obtain ⟨t, out, ht, he, hout⟩ := unpack_runs word
  refine ⟨out, ?_, hout⟩
  have hh := StackMachine.run_mono _ ht _ _ (compile_exec unpackEncoding he)
  exact hh

end Complexity.StackPair

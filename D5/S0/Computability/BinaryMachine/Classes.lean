/- GID: D5/S0/Computability/BinaryMachine/Classes
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/Classes
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine Classes supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/Classes.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.Machine

/-!
Machine-based complexity definitions over binary words. All time bounds count
the local instructions of `Machine.run`; no Lean function is assigned a cost by
assertion. The coefficients and exponents are uniform over all inputs.

This module fixes the foundation independently of SAT. Later modules prove
polynomial-time composition and Cook–Levin for these same concrete definitions.
-/

@[expose] public section

namespace Complexity

/-- Binary words. -/
abbrev Word := List Bool

/-- A language (decision problem): a set of binary words. -/
abbrev Language := Word → Prop

/-- The bound `c * (n + 1) ^ k`. Every polynomial in `n` with natural coefficients
is at most such a bound, so these bounds express polynomial time and length.
`Nat.pow` is written out so that this term is the same when Mathlib is imported. -/
def powerBound (coefficient exponent inputSize : Nat) : Nat :=
  coefficient * Nat.pow (inputSize + 1) exponent

/-- `powerBound` in the usual notation. -/
theorem powerBound_eq (coefficient exponent inputSize : Nat) :
    powerBound coefficient exponent inputSize = coefficient * (inputSize + 1) ^ exponent := rfl

/-- The pair `(x, y)` as one word, `|x|` ones, a zero, `x`, `y`: how NP verifiers get input. -/
def pairWords (x y : Word) : Word :=
  List.replicate x.length true ++ false :: (x ++ y)

/-- `M` accepts `input`: its run on `input` halts with decision `true`. -/
def Accepts (M : Machine) (input : Word) : Prop :=
  ∃ time tape, runInput M time input = some (true, tape)

/-- `M` halts, accepting or rejecting, within `c * (n + 1) ^ k` steps on every input. -/
def PolynomialTimeMachine (M : Machine) : Prop :=
  ∃ coefficient exponent, ∀ input : Word,
    ∃ time decision tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (decision, tape)

/-- `f` is computable in polynomial time: one machine, on every input `x` of
length `n`, halts with decision `true` within `c * (n + 1) ^ k` steps, with
`f x` as the output (`Tape.output`) of its final tape. -/
def PolyTime (f : Word → Word) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent, ∀ input : Word,
    ∃ time tape,
      time ≤ powerBound coefficient exponent input.length ∧
      runInput M time input = some (true, tape) ∧
      tape.output = f input

/-- Deterministic polynomial-time decision of a binary-word language. -/
def InP (L : Language) : Prop :=
  ∃ M : Machine, PolynomialTimeMachine M ∧
    ∀ input, L input ↔ Accepts M input

/-- NP, in its certificate (verifier) form: some polynomial-time machine `M` and
bound `p n = c * (n + 1) ^ k` satisfy, for every word `x`: `x ∈ L` iff `M`
accepts `pairWords x w` for some certificate `w` with `|w| ≤ p |x|`. -/
def InNP (L : Language) : Prop :=
  ∃ M : Machine, ∃ coefficient exponent,
    PolynomialTimeMachine M ∧
    ∀ input, L input ↔
      ∃ witness : Word,
        witness.length ≤ powerBound coefficient exponent input.length ∧
        Accepts M (pairWords input witness)

/-- Karp reducibility: a polynomial-time `f` with `x ∈ A ↔ f x ∈ B` for every word `x`. -/
def PolyRed (A B : Language) : Prop :=
  ∃ f : Word → Word, PolyTime f ∧ ∀ input, A input ↔ B (f input)

/-- `L` is NP-hard: every language in NP reduces to `L`. -/
def NPHard (L : Language) : Prop :=
  ∀ A : Language, InNP A → PolyRed A L

/-- `L` is NP-complete: `L` is in NP and is NP-hard. -/
def NPComplete (L : Language) : Prop :=
  InNP L ∧ NPHard L

/-- Halting immediately preserves the input as the output. -/
def identityMachine : Machine where
  states := 0
  start := ⟨0, by decide⟩
  code := fun _ _ => .halt true

@[simp] theorem Tape.bits_map_bit (input : Word) :
    Tape.bits (input.map Symbol.bit) = input := by
  induction input with
  | nil => rfl
  | cons b input ih => simp [Tape.bits, ih]

@[simp] theorem Tape.output_ofInput (input : Word) :
    (Tape.ofInput input).output = input := by
  simp [Tape.ofInput, Tape.output]

theorem polyTime_id : PolyTime (fun input => input) := by
  refine ⟨identityMachine, 1, 0, ?_⟩
  intro input
  refine ⟨1, Tape.ofInput input, ?_, ?_, ?_⟩
  · simp [powerBound_eq]
  · rfl
  · exact Tape.output_ofInput input

theorem polyRed_refl (A : Language) : PolyRed A A :=
  ⟨fun input => input, polyTime_id, fun _ => Iff.rfl⟩

theorem polyTime_congr {f g : Word → Word}
    (hfg : ∀ input, f input = g input) (hf : PolyTime f) : PolyTime g := by
  obtain ⟨M, coefficient, exponent, hM⟩ := hf
  refine ⟨M, coefficient, exponent, ?_⟩
  intro input
  obtain ⟨time, tape, ht, hr, ho⟩ := hM input
  exact ⟨time, tape, ht, hr, ho.trans (hfg input)⟩

theorem inNP_congr {A B : Language}
    (hAB : ∀ input, A input ↔ B input) (hA : InNP A) : InNP B := by
  obtain ⟨M, coefficient, exponent, hM, hA⟩ := hA
  exact ⟨M, coefficient, exponent, hM,
    fun input => (hAB input).symm.trans (hA input)⟩

theorem polyRed_congr {A A' B B' : Language}
    (hA : ∀ input, A input ↔ A' input)
    (hB : ∀ input, B input ↔ B' input)
    (h : PolyRed A B) : PolyRed A' B' := by
  obtain ⟨f, hf, h⟩ := h
  exact ⟨f, hf, fun input =>
    (hA input).symm.trans ((h input).trans (hB (f input)))⟩

end Complexity

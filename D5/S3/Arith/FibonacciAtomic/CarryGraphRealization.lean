/- GID: D5/S3/Arith/FibonacciAtomic/CarryGraphRealization
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CarryGraphRealization
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Fixed-label carry columns drive a bit-charged prefix-tree execution. -/

import D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
import D5.S0.Tower.DBonacci.TerminalSampling
import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CarryGraphRealization

open scoped BigOperators ENNReal
open CarryGraphEmbedding MeasureTheory
open D5.S0.Tower.DBonacci.TerminalSampling (Tape fairTape fairBit)

/-- The fixed one-label interval, using zero-based indices for labels. -/
def labelSet (m : ℕ) (γ : Path) (d : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    if (γ.action d).b = 1 then (i.val : ℤ) < (γ.state d).e + (γ.action d).c
    else (γ.state d).e - (γ.action d).h ≤ (i.val : ℤ) ∧
      (i.val : ℤ) < (γ.state d).e + (γ.action d).c

/-- Each column emits its selected labels in increasing order. -/
def labels (m : ℕ) (γ : Path) (d : ℕ) : List (Fin m) :=
  (labelSet m γ d).sort (· ≤ ·)

/-- The zero-or-one digit belonging to a fixed output label. -/
def labelDigit {m : ℕ} (γ : Path) (i : Fin m) (d : ℕ) : Fin 2 :=
  if i ∈ labelSet m γ d then 1 else 0

/-- The output law determined by the complete, possibly noncanonical digits. -/
noncomputable def labelLaw {m : ℕ} (γ : Path) (i : Fin m) : ℝ :=
  Real.ofDigits (labelDigit γ i)

/-- Read the next source bit only while active. A left state records the returned
label and the number of charged reads; a right state is a continuing slot. -/
def scan (m : ℕ) (γ : Path) (tape : Tape) : ℕ → Sum (Fin m × ℕ) ℕ
  | 0 => .inr 0
  | d + 1 => match scan m γ tape d with
    | .inl returned => .inl returned
    | .inr j =>
      let z := 2 * j + (tape d).toNat
      if hz : z < (labels m γ d).length then
        .inl ((labels m γ d)[z], d + 1)
      else .inr (z - (labels m γ d).length)

/-- Children are ordered by their parent slot, then by false before true. -/
def children (words : List (List Bool)) : List (List Bool) :=
  words.flatMap fun w => [w ++ [false], w ++ [true]]

/-- The actual continuing words; selected children become leaves and are removed. -/
def continuing (m : ℕ) (γ : Path) : ℕ → List (List Bool)
  | 0 => [[]]
  | d + 1 => (children (continuing m γ d)).drop (labels m γ d).length

/-- The selected children are paired with the corresponding fixed labels. -/
def stopping (m : ℕ) (γ : Path) (d : ℕ) : List (List Bool × Fin m) :=
  (children (continuing m γ d)).zip (labels m γ d)

/-- The first finite return, or exceptional absence of any finite return. -/
noncomputable def sample (m : ℕ) (γ : Path) (tape : Tape) : Option (Fin m × ℕ) := by
  classical
  exact if h : ∃ d, (scan m γ tape d).isLeft then
    (scan m γ tape (Nat.find h)).getLeft?
  else none

/-- Every active scan step contributes one charged read, including divergent tapes. -/
noncomputable def bill (m : ℕ) (γ : Path) (tape : Tape) : ℝ≥0∞ :=
  ∑' d : ℕ, if (scan m γ tape d).isRight then 1 else 0

end D5.S3.Arith.FibonacciAtomic.CarryGraphRealization

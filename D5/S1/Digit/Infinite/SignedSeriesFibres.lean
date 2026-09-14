/- GID: D5/S1/Digit/Infinite/SignedSeriesFibres
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SignedSeriesFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed golden series has exactly two streams over each uniquely indexed seam and one stream over every other value in its interval. -/

import D5.S1.Digit.Infinite.SignedSeriesRange
import D5.S0.Automata.BinaryZeckendorfBlockSkeletonCore

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SignedSeriesFibres

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S0.Automata.BinaryZeckendorfBlockSkeleton

/-- The alphabet consisting of the return blocks zero and one followed by zero. -/
abbrev Block := ReturnBlock

/-- The Boolean digits of a finite word of return blocks. -/
def digitsOf (w : List Block) : List Bool :=
  (expand w .recurrent).map (fun d => decide (d = 1))

/-- The digit length of a finite block word. -/
def len (w : List Block) : ℕ := (digitsOf w).length

private def prependBlock (c : Block) (x : LegalDigits) : LegalDigits :=
  match c with
  | .zero => ⟨fun n => match n with | 0 => false | k + 1 => x.val k, by
      intro j; cases j with
      | zero => simp
      | succ j => exact x.property j⟩
  | .oneZero => ⟨fun n => match n with | 0 => true | 1 => false | k + 2 => x.val k, by
      intro j; cases j with
      | zero => simp
      | succ j => cases j with
        | zero => simp
        | succ j => exact x.property j⟩

/-- Prepend a finite block word to an infinite legal stream. -/
def prependWord : List Block → LegalDigits → LegalDigits
  | [], x => x
  | c :: w, x => prependBlock c (prependWord w x)

/-- The signed contraction ratio. -/
noncomputable def r : ℝ := -alpha

/-- The finite signed digit sum evaluated in increasing digit order. -/
noncomputable def S (w : List Block) : ℝ :=
  (digitsOf w).foldr (fun d z => -alpha ^ 2 * (if d then 1 else 0) + r * z) 0

/-- The affine action of a finite block word on series values. -/
noncomputable def f (w : List Block) (t : ℝ) : ℝ := S w + r ^ len w * t

/-- The common boundary value of the first two block intervals. -/
noncomputable def q : ℝ := -(alpha ^ 3)

/-- The seam value indexed by a finite block word. -/
noncomputable def seam (w : List Block) : ℝ := f w q

/-- The stream obtained by appending the zero block and the upper alternating stream. -/
def leftStream (w : List Block) : LegalDigits := prependWord (w ++ [.zero]) v

/-- The stream obtained by appending the one-zero block and the upper alternating stream. -/
def rightStream (w : List Block) : LegalDigits := prependWord (w ++ [.oneZero]) v

/-- Each seam has exactly its two displayed streams, the indexing word is unique,
and each other value in the closed interval has exactly one stream. -/
theorem signed_series_fibres :
    (∀ w : List Block, leftStream w ≠ rightStream w ∧
      (∀ x : LegalDigits, signedValue x = seam w ↔
        x = leftStream w ∨ x = rightStream w)) ∧
    Function.Injective seam ∧
    (∀ t ∈ Set.Icc a b, t ∉ Set.range seam → ∃! x : LegalDigits, signedValue x = t) := by
  sorry

end D5.S1.Digit.Infinite.SignedSeriesFibres

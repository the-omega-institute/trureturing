/- GID: D5/S1/Digit/SquaresThreeDigitsPrefixRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/SquaresThreeDigitsPrefixRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Nat.Digits.Defs]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.claim; result=D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.result; claim=D5/S1/Digit/SquaresThreeDigitsPrefixRefutation.claim
   digest: A decimal square-digit solution has a prefix whose square contains digit one. -/

import Mathlib.Data.Nat.Digits.Defs

/-!
The decimal-word encoding and square-digit predicate are literal.
A fifteen-block counterexample contradicts prefix closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.SquaresThreeDigitsPrefixRefutation

/-- The source's decimal word, written with the most significant digit first. -/
def decimalWord (runs : List ℕ) : List ℕ :=
  runs.flatMap (fun a => 4 :: List.replicate a 9) ++ [5]

/-- The ordinary natural number encoded by the decimal word. -/
def encode (runs : List ℕ) : ℕ :=
  Nat.ofDigits 10 (decimalWord runs).reverse

/-- Every actual decimal digit of the ordinary integer square is in {0,2,5}. -/
def GoodSquare (n : ℕ) : Prop :=
  (Nat.digits 10 (n ^ 2)).all (fun d => d == 0 || d == 2 || d == 5) = true

/-- Conjecture 1 of arXiv:2112.00444, with all nonnegative runs and no bounds. -/
def claim : Prop :=
  ∀ runs : List ℕ, 2 ≤ runs.length →
    GoodSquare (encode runs) → GoodSquare (encode runs.dropLast)

/-- A fifteen-block tuple whose final block has two nines. -/
def counterexample : List ℕ :=
  [0, 1, 3, 7, 15, 31, 63, 127, 2, 6, 14, 62, 14, 6, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The full tuple satisfies the source predicate, while deleting its last block fails it. -/
theorem result : ¬ claim := by
  intro h
  have hgood : GoodSquare (encode counterexample) := by
    unfold GoodSquare
    decide +kernel
  have hOne : 1 ∈ Nat.digits 10 ((encode counterexample.dropLast) ^ 2) := by
    decide +kernel
  have hbad : ¬ GoodSquare (encode counterexample.dropLast) := by
    intro hg
    have hf := List.all_eq_true.mp hg 1 hOne
    simp at hf
  exact hbad (h counterexample (by decide) hgood)

#print axioms result

end D5.S1.Digit.SquaresThreeDigitsPrefixRefutation

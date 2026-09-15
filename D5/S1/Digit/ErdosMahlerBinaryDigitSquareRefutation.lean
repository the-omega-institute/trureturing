/- GID: D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation
   generality: I
   mirror-B: D5/B/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Group.Finset.Basic, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.claim; result=D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.result; claim=D5/S1/Digit/ErdosMahlerBinaryDigitSquareRefutation.claim
   digest: A base-12 square refutes uniqueness of Mahler's nontrivial binary-digit example. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ErdosMahlerBinaryDigitSquareRefutation

/-!
Erdos reported Mahler's suggestion that the base-7 identity
`7^3 + 7^2 + 7 + 1 = 20^2` could be the only nontrivial square with 0/1
digits in a base greater than four. The exponent set includes zero, as that
printed identity does. Here "trivial" means the two-digit family `x^2 = k + 1`,
and coprimality excludes representations obtained by shifting all digits.

The base-12 identity `12^5 + 12^4 + 12^3 + 12^2 + 1 = 521^2` refutes only
that uniqueness suggestion. It does not address finiteness for any fixed base
greater than four or infinitude in bases two, three, and four.
-/

/-- A square whose base-`k` expansion has a one exactly at each exponent in `S`. -/
def BinaryBaseSquare (k x : ℕ) (S : Finset ℕ) : Prop :=
  Nat.Coprime k x ∧ ∑ i ∈ S, k ^ i = x ^ 2

/-- Mahler's reported suggestion, with the stated trivial family excluded. -/
def claim : Prop :=
  ∀ (k x : ℕ) (S : Finset ℕ),
    5 ≤ k → 1 < x → BinaryBaseSquare k x S →
      (k = 7 ∧ x = 20) ∨ k = x ^ 2 - 1

/-- The coprime base-12 square with root 521 refutes `claim`. -/
theorem result : ¬ claim := by
  intro h
  have hSquare : BinaryBaseSquare 12 521 {0, 2, 3, 4, 5} := by
    unfold BinaryBaseSquare
    decide
  have hClassification := h 12 521 {0, 2, 3, 4, 5} (by norm_num) (by norm_num) hSquare
  norm_num at hClassification

#print axioms result

end D5.S1.Digit.ErdosMahlerBinaryDigitSquareRefutation

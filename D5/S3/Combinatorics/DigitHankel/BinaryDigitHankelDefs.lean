/- GID: D5/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/BinaryDigitHankelDefs
   mirror-E: none(waiver:fixed-binary-digit-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Data.Nat.Digits.Defs]
   utility: none
   digest: The support of the binary digit-sum Hankel determinants at t = -2. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Digits.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelDefs

/-! Fixed public statement: Sobolewski and Ulas, *Hankel determinants of weighted binary sums of
    digits*, arXiv:2607.09376v1, §5.1, the case `d = 2` of Conjecture 5.7, stated right after it:
    `H(n, -2) = 0` if and only if `n ≠ n_k - 1, n_k, n_k + 1`.  For `u = ∑ⱼ εⱼ 2ʲ`,
    `S(u, t) = ∑ⱼ εⱼ tʲ`, `H(n, t) = det [S(i + j, t)]_{0 ≤ i, j < n}` and
    `n_k = ⌈2^{k+2} / 3⌉`.  The statement concerns `n ≥ 2`. -/

/-- The weighted binary digit sum `S(u, t)`. -/
def digitSum (u : ℕ) (t : ℤ) : ℤ :=
  ((Nat.digits 2 u).mapIdx fun j d => (d : ℤ) * t ^ j).sum

/-- The Hankel determinant `H(n, t)`. -/
def hankel (n : ℕ) (t : ℤ) : ℤ :=
  (Matrix.of fun i j : Fin n => digitSum (i + j) t).det

/-- `n_k = ⌈2^{k+2} / 3⌉`. -/
def threshold (k : ℕ) : ℕ := (2 ^ (k + 2) + 2) / 3

/-- The `d = 2` case of Conjecture 5.7. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (hankel n (-2) ≠ 0 ↔
      ∃ k : ℕ, n + 1 = threshold k ∨ n = threshold k ∨ n = threshold k + 1)

end D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelDefs

/- GID: D5/S3/Combinatorics/CylindricPartition/LiUncuDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CylindricPartition/LiUncuDefs
   mirror-E: none(waiver:finite-andrews-gordon-companion-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Basic, mathlib/module/Mathlib.Data.Fintype.Pi, mathlib/module/Mathlib.Data.Int.Interval]
   utility: none
   digest: Li and Uncu's finite Andrews-Gordon companion identity for k at least five. -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CylindricPartition.LiUncuDefs

open Polynomial

/-! Fixed public statement: Li and Uncu, *A MacMahon Analysis View of Cylindric Partitions*,
    arXiv:2501.19272v1, §1, Conjecture 1.3, equation (1.5).  For integers `n ≥ 0`, `k ≥ 5` and
    `k > i ≥ 1`,
    `∑_{n₁ ≥ ⋯ ≥ n_{k-1} ≥ n_k = 0} q^{n₁² + ⋯ + n_{k-1}² + n_i + ⋯ + n_{k-1}}`
    `  · ∏_{j=1}^{k-1} [2n - 2∑_{ℓ<j} n_ℓ - n_j - n_{j+1} - 2α_{ij} ; n_j - n_{j+1}]'_q`
    `= ∑_{r ∈ ℤ} (-1)^r q^{r((2k+1)r+2k-2i+1)/2}`
    `  · [2n ; n - (2k+1)r/2 + (2k-2i+1)((-1)^r-1)/4]_q`,
    with `α_{ij} = max(j - i + 1, 0)`.  The Gaussian binomial `[a ; b]_q` is zero unless
    `0 ≤ b ≤ a`, and the primed one agrees with it except that `[a ; 0]'_q = 1` for `a < 0`.

    Only finitely many terms are nonzero.  On the left, a tuple with `n₁ > n` contributes zero:
    following `n₁ ≥ n₂ ≥ ⋯` to the first strict descent, the factor there has a positive lower
    index and a negative upper index.  Hence the sum runs over nonincreasing tuples with values at
    most `n`.  On the right, the lower index lies in `[0, 2n]` only when `|r| ≤ n + 1`, and the
    exponent `r((2k+1)r + 2k - 2i + 1)/2` is a nonnegative integer for every integer `r`. -/

/-- The Gaussian binomial `[a ; b]_q`, by the q-Pascal recurrence
    `[a+1 ; b+1] = [a ; b+1] + q^{a-b} [a ; b]`; it vanishes for `b > a`. -/
noncomputable def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | a + 1, b + 1 => gauss a (b + 1) + X ^ (a - b) * gauss a b

/-- `[a ; b]_q` for integer arguments: zero when `a < 0` or `b < 0`. -/
noncomputable def gaussInt (a b : ℤ) : ℤ[X] :=
  if a < 0 ∨ b < 0 then 0 else gauss a.toNat b.toNat

/-- The primed Gaussian binomial: `[a ; 0]'_q = 1` for every integer `a`. -/
noncomputable def gaussPrime (a b : ℤ) : ℤ[X] :=
  if b = 0 then 1 else gaussInt a b

/-- `α_{ij} = max(j - i + 1, 0)`. -/
def alpha (i j : ℕ) : ℤ := max ((j : ℤ) - i + 1) 0

/-- The entry `n_j` (`1 ≤ j ≤ k - 1`) of a tuple `v`, and `n_j = 0` otherwise. -/
def entry {k n : ℕ} (v : Fin (k - 1) → Fin (n + 1)) (j : ℕ) : ℤ :=
  if h : 1 ≤ j ∧ j ≤ k - 1 then ((v ⟨j - 1, by omega⟩ : ℕ) : ℤ) else 0

/-- The summand of the left side for a tuple `n₁ ≥ ⋯ ≥ n_{k-1}` with values at most `n`. -/
noncomputable def leftTerm (n k i : ℕ) (v : Fin (k - 1) → Fin (n + 1)) : ℤ[X] :=
  X ^ ((∑ j ∈ Finset.Icc 1 (k - 1), entry v j ^ 2 + ∑ j ∈ Finset.Icc i (k - 1), entry v j).toNat) *
    ∏ j ∈ Finset.Icc 1 (k - 1),
      gaussPrime (2 * n - 2 * ∑ l ∈ Finset.Ico 1 j, entry v l - entry v j - entry v (j + 1)
          - 2 * alpha i j)
        (entry v j - entry v (j + 1))

/-- The left side of (1.5). -/
noncomputable def lhs (n k i : ℕ) : ℤ[X] :=
  ∑ v ∈ (Finset.univ : Finset (Fin (k - 1) → Fin (n + 1))).filter
      (fun v => ∀ a b : Fin (k - 1), a ≤ b → v b ≤ v a),
    leftTerm n k i v

/-- The summand of the right side of (1.5) for an integer `r`. -/
noncomputable def rightTerm (n k i : ℕ) (r : ℤ) : ℤ[X] :=
  let parity : ℤ := if Even r then 0 else -1
  (-1) ^ r.natAbs * X ^ ((r * ((2 * k + 1) * r + 2 * k - 2 * i + 1)) / 2).toNat *
    gaussInt (2 * n) ((2 * n - (2 * k + 1) * r + (2 * k - 2 * i + 1) * parity) / 2)

/-- The right side of (1.5). -/
noncomputable def rhs (n k i : ℕ) : ℤ[X] :=
  ∑ r ∈ Finset.Icc (-(n + 1 : ℤ)) (n + 1), rightTerm n k i r

/-- Conjecture 1.3: equation (1.5) for every `n ≥ 0`, `k ≥ 5` and `1 ≤ i < k`. -/
def claim : Prop :=
  ∀ n k i : ℕ, 5 ≤ k → 1 ≤ i → i < k → lhs n k i = rhs n k i

end D5.S3.Combinatorics.CylindricPartition.LiUncuDefs

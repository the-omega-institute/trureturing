/- GID: D5/S3/Combinatorics/Nonnesting/NonnestingDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Nonnesting/NonnestingDefs
   mirror-E: none(waiver:fixed-nonnesting-avoider-definitions)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Nonnesting permutations of the doubled multiset avoiding sets of patterns. -/

import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Nonnesting.NonnestingDefs

open PowerSeries D5.S3.Combinatorics

/-! Fixed public statements: Elizalde–Luo, arXiv:2412.00336v6, §5, Table 4 (conjectured enumerations
    of nonnesting permutations avoiding further patterns). Words are lists of natural numbers; a pattern
    `σ` on the letters `1, …, k` occurs in `w` when letters `x 1 < ⋯ < x k` of `w` appear in the order
    `σ.map x`, which records equalities as well as the relative order. -/

/-- The number of distinct letters `k` of a pattern on the letters `1, …, k`. -/
def letters (σ : List ℕ) : ℕ := σ.foldr max 0

/-- `w` contains the pattern `σ`. -/
def Occurs (σ w : List ℕ) : Prop := ArrowWilfDefs.Contains σ [] (letters σ) w

/-- `𝒞_n(Λ)`: permutations of `{1, 1, 2, 2, …, n, n}` avoiding `1221`, `2112` and every pattern in `Λ`. -/
def avoiders (n : ℕ) (Λ : List (List ℕ)) : Set (List ℕ) :=
  {w | w.Perm ((List.range' 1 n).flatMap fun i => [i, i]) ∧ ¬ Occurs [1, 2, 2, 1] w ∧
    ¬ Occurs [2, 1, 1, 2] w ∧ ∀ σ ∈ Λ, ¬ Occurs σ w}

/-- `∑ₙ |𝒞_n(Λ)| xⁿ`. -/
noncomputable def gf (Λ : List (List ℕ)) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((avoiders n Λ).ncard : ℤ)

/-- Table 4, `Λ = {1322}`: `|𝒞_n(1322)| = (1/n) ∑_{k=0}^{n-1} C(3n,k) C(2n-k-2, n-1)` for `n ≥ 1`. -/
def claim1322 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n * (avoiders n [[1, 3, 2, 2]]).ncard =
    ∑ k ∈ Finset.range n, (3 * n).choose k * (2 * n - k - 2).choose (n - 1)

/-- The generating function of Table 4, rows `{1132, 2213}` and `{1233, 1322}`:
    `R = ((1-x)² - √((1-x)⁴ - 4x(1-x)²))/(2x)`, i.e. the power series with `x R² - (1-x)² R + (1-x)² = 0`. -/
def IsRoyalRoot (R : PowerSeries ℤ) : Prop := X * R ^ 2 - (1 - X) ^ 2 * R + (1 - X) ^ 2 = 0

/-- Table 4, `Λ = {1132, 2213}`. -/
def claim1132 : Prop := IsRoyalRoot (gf [[1, 1, 3, 2], [2, 2, 1, 3]])

/-- Table 4, `Λ = {1233, 1322}`. -/
def claim1233 : Prop := IsRoyalRoot (gf [[1, 2, 3, 3], [1, 3, 2, 2]])

/-- Table 4, `Λ = {1231, 1312, 2231, 3221}`: OGF `(1 - 3x + 2x²)/((1 - 3x)(1 - x - x²))`. -/
def claimFour : Prop :=
  gf [[1, 2, 3, 1], [1, 3, 1, 2], [2, 2, 3, 1], [3, 2, 2, 1]] * ((1 - 3 * X) * (1 - X - X ^ 2)) =
    1 - 3 * X + 2 * X ^ 2

end D5.S3.Combinatorics.Nonnesting.NonnestingDefs

/- GID: D5/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RestrictedSchur/RestrictedSchurDefs
   mirror-E: none(waiver:gaiser-open-question-six-two-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin, mathlib/module/Mathlib.Data.Finset.Card, mathlib/module/Mathlib.Data.Nat.Lattice]
   utility: none
   digest: Gaiser's Open Question 6.2 on the restricted generalized Schur number S_3(k;2). -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RestrictedSchur.RestrictedSchurDefs

/-! Fixed public statement: C. Gaiser, *Restricted generalized Schur numbers*, arXiv:2608.08789v1.
    For `k ≥ 2`, `S_r(k; ℓ)` is the smallest `n` such that every `r`-colouring of `{1, …, n}` has a
    monochromatic solution `S` of `x_1 + ⋯ + x_k = x_{k+1}` whose number of distinct integers
    `c(S)` is exactly `ℓ + 1`.  Proposition 6.1 proves `S_3(k; 2) ≥ k^3 + 3k^2 + k − 1` for
    `k ≥ 2`, and Section 6 asks: "Open Question 6.2. Is it true that S_3(k; 2) = k^3 + 3k^2 + k − 1
    for all large enough k?"  A colouring of `{1, …, n}` is any map `ℕ → Fin r`; only its values on
    `1, …, n` matter.  The least such `n` is taken as `sInf`. -/

/-- The colouring `c` has a monochromatic solution in `{1, …, n}` of `x_1 + ⋯ + x_k = x_{k+1}`
    with exactly `ℓ + 1` distinct integers. -/
def HasMonochromaticSolution (r k ℓ n : ℕ) (c : ℕ → Fin r) : Prop :=
  ∃ x : Fin (k + 1) → ℕ, (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
    (∑ i : Fin k, x i.castSucc) = x (Fin.last k) ∧
    (Finset.univ.image x).card = ℓ + 1 ∧ ∀ i j, c (x i) = c (x j)

/-- The restricted generalized Schur number `S_r(k; ℓ)`. -/
noncomputable def schur (r k ℓ : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ c : ℕ → Fin r, HasMonochromaticSolution r k ℓ n c}

/-- Open Question 6.2, as asked. -/
def claim : Prop := ∃ K : ℕ, ∀ k ≥ K, schur 3 k 2 = k ^ 3 + 3 * k ^ 2 + k - 1

end D5.S3.Combinatorics.RestrictedSchur.RestrictedSchurDefs

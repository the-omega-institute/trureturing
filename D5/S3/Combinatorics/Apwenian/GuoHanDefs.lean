/- GID: D5/S3/Combinatorics/Apwenian/GuoHanDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Apwenian/GuoHanDefs
   mirror-E: none(waiver:automatic-apwenian-classification-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Finset.Basic]
   utility: none
   digest: Guo and Han's classification of purely automatic apwenian sequences over an alphabet with one odd letter. -/

import Mathlib.Data.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Apwenian.GuoHanDefs

/-! Fixed public statement: Guo and Han, *On a family of automatic apwenian sequences*,
    Discrete Math. 348 (2025) 114399, Conjecture 2 (author version, §4).  A sequence `a` over `ℕ`
    is apwenian if `a 0 = 1` and `a n ≡ a (2n+1) + a (2n+2) (mod 2)` for every `n`.  A purely
    automatic sequence over a finite alphabet `Σ` is a fixed point of a `p`-uniform morphism
    `σ : Σ → Σ^p` with `p ≥ 2`, that is `σ (a n) = a (np) a (np+1) ⋯ a (np+p-1)` for every `n`.
    The period-doubling sequence is the fixed point of `1 ↦ 10, 0 ↦ 11`; equivalently `P 0 = 1`,
    `P (2n) = 1` and `P (2n+1) = 1 - P n`.  Conjecture 2: if the only odd letter of `Σ` is `1`,
    then a purely automatic sequence over `Σ` is apwenian if and only if `a n ≡ P n (mod 2)` for
    every `n`. -/

/-- The apwenian property. -/
def IsApwenian (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, a n % 2 = (a (2 * n + 1) + a (2 * n + 2)) % 2

/-- The period-doubling sequence, by `P (2n) = 1` and `P (2n+1) = 1 - P n`. -/
def periodDoubling : ℕ → ℕ
  | n => if h : n % 2 = 0 then 1 else 1 - periodDoubling (n / 2)
decreasing_by omega

/-- Conjecture 2. -/
def claim : Prop :=
  ∀ (Sigma : Finset ℕ), 1 ∈ Sigma → (∀ x ∈ Sigma, x % 2 = 1 → x = 1) →
    ∀ (p : ℕ) (σ : ℕ → Fin p → ℕ) (a : ℕ → ℕ), 2 ≤ p →
      (∀ s ∈ Sigma, ∀ r : Fin p, σ s r ∈ Sigma) →
      (∀ n : ℕ, a n ∈ Sigma) →
      (∀ (n : ℕ) (r : Fin p), a (n * p + r) = σ (a n) r) →
      (IsApwenian a ↔ ∀ n : ℕ, a n % 2 = periodDoubling n)

end D5.S3.Combinatorics.Apwenian.GuoHanDefs

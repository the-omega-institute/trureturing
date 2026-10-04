/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdDefs
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdDefs
   mirror-E: none(waiver:balanced-critical-exponent-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.ENNReal.Inv]
   utility: none
   digest: The odd-alphabet case of the conjectured least critical exponent of balanced sequences. -/

import Mathlib.Data.ENNReal.Inv
import D5.S1.Words.Complexity.MorseHedlund

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

open scoped ENNReal

/-! Fixed public statement: L. Dvořáková, D. Opočenská, E. Pelantová and A. M. Shur, *On minimal
    critical exponent of balanced sequences*, Theoret. Comput. Sci. 922 (2022) 158–169,
    arXiv:2112.02854.  An infinite word over a finite alphabet is balanced when the numbers of
    occurrences of any letter in two factors of equal length differ by at most one; its critical
    exponent is the supremum of `n / p` over factors of length `n` having period `p`.  The paper
    proves that every balanced sequence over `d ≥ 11` letters has critical exponent at least
    `(d − 1)/(d − 2)`, constructs sequences attaining this bound for every even `d ≥ 12`, and
    conjectures that the least critical exponent equals `(d − 1)/(d − 2)` for every `d ≥ 11`; an
    attaining sequence for `d = 11` was later found.  The remaining case of the conjecture is the
    existence of an attaining balanced sequence over exactly `d` letters for every odd `d ≥ 13`.
    Windows are the repository factors `D5.S1.Words.Complexity.wordFactor`. -/

open D5.S1.Words.Complexity

/-- The number of occurrences of the letter `a` in the length-`n` window of `x` starting at `i`. -/
noncomputable def letterCount {A : Type*} [Fintype A] [DecidableEq A] (x : ℕ → A) (a : A)
    (n i : ℕ) : ℕ :=
  (Finset.univ.filter fun k : Fin n => wordFactor x n i k = a).card

/-- Balance: in two windows of equal length every letter occurs a number of times differing by
    at most one. -/
def Balanced {A : Type*} [Fintype A] [DecidableEq A] (x : ℕ → A) : Prop :=
  ∀ (a : A) (n i j : ℕ), letterCount x a n i ≤ letterCount x a n j + 1

/-- The length-`n` window of `x` starting at `i` has period `p`. -/
def HasPeriod {A : Type*} (x : ℕ → A) (n i p : ℕ) : Prop :=
  ∀ k : ℕ, k + p < n → x (i + k) = x (i + k + p)

/-- The critical exponent: the supremum of `n / p` over windows of length `n` with a positive
    period `p ≤ n`, valued in `[0, ∞]`. -/
noncomputable def criticalExponent {A : Type*} (x : ℕ → A) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (i : ℕ) (p : ℕ) (_ : 0 < p ∧ p ≤ n ∧ HasPeriod x n i p), (n : ℝ≥0∞) / p

/-- The remaining case of the conjecture: for every odd `d ≥ 13` some balanced sequence using all
    `d` letters has critical exponent `(d − 1)/(d − 2)`. -/
def claim : Prop :=
  ∀ d : ℕ, 13 ≤ d → Odd d → ∃ x : ℕ → Fin d, Function.Surjective x ∧ Balanced x ∧
    criticalExponent x = ((d - 1 : ℕ) : ℝ≥0∞) / ((d - 2 : ℕ) : ℝ≥0∞)

end D5.S1.Words.BalancedThreshold.BalancedThresholdDefs

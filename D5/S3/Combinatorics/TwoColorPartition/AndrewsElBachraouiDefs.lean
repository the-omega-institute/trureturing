/- GID: D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiDefs
   mirror-E: none(waiver:two-color-partition-positivity-statement-definition)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Andrews and El Bachraoui's two-color partition series C' and D' and their sign conjectures. -/

import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs

open PowerSeries

/-! Fixed public statements: Andrews and El Bachraoui, *Certain positive q-series and
    inequalities for two-color partitions*, arXiv:2507.09276v1, equations (1.2) and (1.3),
    §2 Conjecture 2 and §3 Conjectures 3 and 4.  The series are
    `∑ₙ C'(k,m,n) qⁿ = ∑_{j ≥ 0} q^{m(2j+1)} (q^{2j+2}, q^{2j+2k}; q²)_∞ / (q^{2j+1}; q²)_∞²` and
    `∑ₙ D'(k,m,n) qⁿ = ∑_{j ≥ 0} q^{m(2j+2)} (q^{2j+4}, q^{2j+2+2k}; q²)_∞ / (q^{2j+3}; q²)_∞²`.
    Conjecture 2: `C'(2,4,n) ≥ 0` for every `n`.  Conjecture 3: `D'(2,2,n) ≥ 0` for every `n`.
    Conjecture 4: `D'(2,3,n) < 0` exactly for `n = 10` and `n = 22`.

    The coefficient of `qⁿ` is read off a finite truncation.  For `m ≥ 1`, every summand with
    `j > n` starts above degree `n`, and every product factor with `i > n` has the form
    `1 - q^e` or `1 / (1 - q^e)` with `e > n`, which agrees with `1` through degree `n`.  Hence the
    coefficient of `qⁿ` in the `n`-truncation below equals that of the infinite series. -/

/-- The power series `1 / (1 - q^d)`, written as its coefficient sequence. -/
noncomputable def geom (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun t => if d ∣ t then 1 else 0

/-- The `N`-truncation of `∑ⱼ q^{m(2j+1)} (q^{2j+2}, q^{2j+2k}; q²)_∞ / (q^{2j+1}; q²)_∞²`. -/
noncomputable def cTrunc (k m N : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (N + 1), X ^ (m * (2 * j + 1)) *
    ∏ i ∈ Finset.range (N + 1),
      ((1 - X ^ (2 * j + 2 + 2 * i)) * (1 - X ^ (2 * j + 2 * k + 2 * i)) *
        geom (2 * j + 1 + 2 * i) ^ 2)

/-- The `N`-truncation of `∑ⱼ q^{m(2j+2)} (q^{2j+4}, q^{2j+2+2k}; q²)_∞ / (q^{2j+3}; q²)_∞²`. -/
noncomputable def dTrunc (k m N : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (N + 1), X ^ (m * (2 * j + 2)) *
    ∏ i ∈ Finset.range (N + 1),
      ((1 - X ^ (2 * j + 4 + 2 * i)) * (1 - X ^ (2 * j + 2 + 2 * k + 2 * i)) *
        geom (2 * j + 3 + 2 * i) ^ 2)

/-- `C'(k,m,n)`, the coefficient of `qⁿ` in equation (1.2). -/
noncomputable def cCoeff (k m n : ℕ) : ℤ := PowerSeries.coeff n (cTrunc k m n)

/-- `D'(k,m,n)`, the coefficient of `qⁿ` in equation (1.3). -/
noncomputable def dCoeff (k m n : ℕ) : ℤ := PowerSeries.coeff n (dTrunc k m n)

/-- Conjecture 2: the series `∑ₙ C'(2,4,n) qⁿ` is positive. -/
def conjectureTwo : Prop := ∀ n : ℕ, 0 ≤ cCoeff 2 4 n

/-- Conjecture 3: the series `∑ₙ D'(2,2,n) qⁿ` is positive. -/
def conjectureThree : Prop := ∀ n : ℕ, 0 ≤ dCoeff 2 2 n

/-- Conjecture 4: the only negative coefficients of `∑ₙ D'(2,3,n) qⁿ` are at `n = 10, 22`. -/
def conjectureFour : Prop := ∀ n : ℕ, dCoeff 2 3 n < 0 ↔ n = 10 ∨ n = 22

end D5.S3.Combinatorics.TwoColorPartition.AndrewsElBachraouiDefs

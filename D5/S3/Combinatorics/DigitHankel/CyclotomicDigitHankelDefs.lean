/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelDefs
   mirror-E: none(waiver:cyclotomic-digit-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots, mathlib/module/Mathlib.Data.Complex.Basic]
   utility: none
   digest: Sobolewski and Ulas's conjectured zero set of binary digit Hankel determinants at twice a root of unity. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDefs

/-! Fixed public statement: Sobolewski and Ulas, *Hankel determinants of weighted binary sums of
    digits*, arXiv:2607.09376v1, §5.1, Theorem 5.4 and Conjecture 5.7.  For `u = ∑ⱼ eⱼ 2ʲ` put
    `S(u,t) = ∑ⱼ eⱼ tʲ` and `H(n,t) = det (S(i+j,t))_{0 ≤ i,j < n}`.  For `d ≥ 2` and `ℓ ≥ d + 1`
    write `ℓ = q d + r` with `q ≥ 1` and `1 ≤ r ≤ d`, and put
    `z_{d,ℓ} = 2^r (2^{qd} - 1) / (2^d - 1) - 2` if `r < d`, and `- 1` instead of `- 2` if `r = d`.
    `A_d` is the set of positive integers in `⋃_{ℓ ≥ d+1} ⋃_{s odd} (2^ℓ s - z_{d,ℓ} - 1,
    2^ℓ s + z_{d,ℓ} + 1]`.  Conjecture 5.7: for every primitive `d`-th root of unity `ζ` and every
    `n ≥ 2`, `H(n, 2ζ) = 0` if and only if `n ∈ A_d`.  The variable `t` ranges over `ℂ` here,
    since `2ζ` is not an integer; the determinants of `BinaryDigitHankelDefs` take integer `t`. -/

/-- `S(u,t)`: the binary digits of `u`, least significant first, weighted by powers of `t`. -/
def digitSum (u : ℕ) (t : ℂ) : ℂ :=
  ((Nat.digits 2 u).mapIdx fun j e => (e : ℂ) * t ^ j).sum

/-- `H(n,t) = det (S(i+j,t))_{0 ≤ i,j < n}`. -/
noncomputable def hankel (n : ℕ) (t : ℂ) : ℂ :=
  (Matrix.of fun i j : Fin n => digitSum (i + j) t).det

/-- `z_{d,ℓ}` of Theorem 5.4, with `ℓ = q d + r`, `1 ≤ r ≤ d`. -/
def zBound (d l : ℕ) : ℤ :=
  let r := (l - 1) % d + 1
  let q := (l - r) / d
  (2 : ℤ) ^ r * (2 ^ (q * d) - 1) / (2 ^ d - 1) - if r < d then 2 else 1

/-- Membership of the positive integer `n` in the set `A_d`. -/
def InZeroSet (d n : ℕ) : Prop :=
  0 < n ∧ ∃ l s : ℕ, d + 1 ≤ l ∧ Odd s ∧
    (2 : ℤ) ^ l * s - zBound d l - 1 < n ∧ (n : ℤ) ≤ 2 ^ l * s + zBound d l + 1

/-- Conjecture 5.7 for every order `d ≥ 2`. -/
def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ζ : ℂ, IsPrimitiveRoot ζ d → ∀ n : ℕ, 2 ≤ n →
    (hankel n (2 * ζ) = 0 ↔ InZeroSet d n)

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelDefs

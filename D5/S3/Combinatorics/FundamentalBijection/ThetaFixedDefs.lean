/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs
   mirror-E: none(waiver:fixed-fundamental-bijection-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Pattern-avoiding permutations fixed by an iterate of the fundamental bijection. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs

open PowerSeries D5.S3.Combinatorics

/-! Fixed public statements: Archer–Laudone, arXiv:2407.06338v1, §5, Conjecture 5.6: for
    `σ ∈ {231, 312}` the generating functions `F_σ^k(x)` of the `σ`-avoiders fixed by `θ^k` are
    `1/(1 - x - x² - 2x³)` for `k = 3`, `1/(1 - x - x² - 2x⁴ - x⁵ - x⁶)` for `k = 4` and
    `1/(1 - x - x²)` for `k = 5`. Permutations of `[n]` are lists in one-line notation. -/

/-- The cycle of `m`, read from `m`: `m, p(m), p²(m), …` up to the return to `m`. -/
def cycleFrom (p : List ℕ) (m : ℕ) : List ℕ :=
  m :: ((List.range p.length).map fun i => (ArcherCyclicDefs.image p)^[i + 1] m).takeWhile (· ≠ m)

/-- `m` is the largest element of its cycle, so the standard cycle form writes that cycle from `m`. -/
def IsLeader (p : List ℕ) (m : ℕ) : Prop := ∀ y ∈ cycleFrom p m, y ≤ m

instance (p : List ℕ) (m : ℕ) : Decidable (IsLeader p m) := by
  unfold IsLeader; infer_instance

/-- The fundamental bijection `θ`: write the cycles with their largest element first, in increasing
    order of that element, and erase the parentheses. -/
def theta (p : List ℕ) : List ℕ :=
  ((List.range' 1 p.length).filter fun m => decide (IsLeader p m)).flatMap (cycleFrom p)

/-- `𝓕_n^k(σ)`: permutations of `[n]` avoiding `σ` and fixed by `θ^k`. -/
def fixedAvoiders (n k : ℕ) (σ : List ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧ ¬ ArrowWilfDefs.Contains σ [] σ.length p ∧ theta^[k] p = p}

/-- `F_σ^k(x) = ∑ f_n^k(σ) xⁿ` with `f_n^k(σ) = |𝓕_n^k(σ)|`. -/
noncomputable def gf (k : ℕ) (σ : List ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => ((fixedAvoiders n k σ).ncard : ℤ)

/-- Conjecture 5.6, `k = 3`: `F_σ³(x) = 1/(1 - x - x² - 2x³)` for `σ ∈ {231, 312}`. -/
def cubeClaim : Prop :=
  ∀ σ ∈ ({[2, 3, 1], [3, 1, 2]} : Set (List ℕ)), gf 3 σ * (1 - X - X ^ 2 - 2 * X ^ 3) = 1

/-- Conjecture 5.6, `k = 4`: `F_σ⁴(x) = 1/(1 - x - x² - 2x⁴ - x⁵ - x⁶)` for `σ ∈ {231, 312}`. -/
def fourthClaim : Prop :=
  ∀ σ ∈ ({[2, 3, 1], [3, 1, 2]} : Set (List ℕ)),
    gf 4 σ * (1 - X - X ^ 2 - 2 * X ^ 4 - X ^ 5 - X ^ 6) = 1

/-- Conjecture 5.6, `k = 5`: `F_σ⁵(x) = 1/(1 - x - x²)` for `σ ∈ {231, 312}`. -/
def fifthClaim : Prop :=
  ∀ σ ∈ ({[2, 3, 1], [3, 1, 2]} : Set (List ℕ)), gf 5 σ * (1 - X - X ^ 2) = 1

end D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs

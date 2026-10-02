/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateDefs
   mirror-E: none(waiver:fixed-iterate-avoidance-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Permutations whose first iterates under the fundamental bijection all avoid a pattern. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDefs

open D5.S3.Combinatorics D5.S3.Combinatorics.FundamentalBijection

/-! Fixed public statement: Archer–Laudone, arXiv:2407.06338v1, §4, Conjecture 4.5, on
    `𝒯_n^k(132)`, the permutations `π` of `[n]` such that `π, θ(π), …, θ^k(π)` all avoid `132`. -/

/-- `𝒯_n^k(σ)`: permutations `π` of `[n]` with `π, θ(π), …, θ^k(π)` all avoiding `σ`. -/
def iterateAvoiders (n k : ℕ) (σ : List ℕ) : Set (List ℕ) :=
  {p | p.Perm (List.range' 1 n) ∧
    ∀ i ≤ k, ¬ ArrowWilfDefs.Contains σ [] σ.length (ThetaFixedDefs.theta^[i] p)}

/-- The conjectured value of `t_n^2(132)`, with `m = ⌊n/3⌋`. -/
def quadCount (n : ℕ) : ℕ :=
  if n % 3 = 0 then (n / 3) ^ 3 + 3 * (n / 3) ^ 2 + 2 * (n / 3) - 1
  else if n % 3 = 1 then (n / 3) ^ 3 + 4 * (n / 3) ^ 2 + 4 * (n / 3)
  else (n / 3) ^ 3 + 5 * (n / 3) ^ 2 + 7 * (n / 3) + 2

/-- Conjecture 4.5: `t_n^2(132)` is the cubic quasipolynomial for `n ≥ 2`, and for `n ≥ 3`,
    `t_n^3(132) = 3n - 4`, `t_n^4(132) = 2n - 1`, `t_n^5(132) = n + 2`,
    and `t_n^k(132) = 5` for `k ≥ 6`. -/
def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → (iterateAvoiders n 2 [1, 3, 2]).ncard = quadCount n) ∧
  ∀ n : ℕ, 3 ≤ n →
    (iterateAvoiders n 3 [1, 3, 2]).ncard = 3 * n - 4 ∧
    (iterateAvoiders n 4 [1, 3, 2]).ncard = 2 * n - 1 ∧
    (iterateAvoiders n 5 [1, 3, 2]).ncard = n + 2 ∧
    ∀ k : ℕ, 6 ≤ k → (iterateAvoiders n k [1, 3, 2]).ncard = 5

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateDefs

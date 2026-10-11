/- GID: D5/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PackingDomatic/PackingDomaticPathDefs
   mirror-E: none(waiver:bresar-ferme-hu-problem-two-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Fin.Basic, mathlib/module/Mathlib.Data.Nat.Dist]
   utility: none
   digest: Brešar, Ferme and Hu's Problem 2 on packing k-domatic colourings of paths. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathDefs

/-! Fixed public statement: B. Brešar, J. Ferme and W. Hu, *Partitioning an S-packing coloring into
    broadcast dominating sets*, arXiv:2610.03477v1.  A packing `k`-domatic colouring of a graph `G`
    with colours in `[t]` is a map `f : V(G) → [t]` such that two distinct vertices of colour `j`
    are at distance greater than `j`, together with a partition `V(G) = A_1 ⊔ ⋯ ⊔ A_k` such that
    for every vertex `x` and every class `A_i` some `a ∈ A_i` satisfies `d(x, a) ≤ f(a)`; the
    partition classes are arbitrary sets.  `χ_{ρ,k}(G)` is the least such `t`, so
    `χ_{ρ,k}(G) ≤ t` exactly when a packing `k`-domatic colouring with colours in `[t]` exists.
    Section 5 asks: "Problem 2. Is it true that χ_{ρ,k}(P_n) ≤ k + 1 for any k ≥ 3 and any
    n ≥ 2k?"  The path `P_n` has vertices `Fin n` with distance `|i − j|`. -/

/-- A packing `k`-domatic colouring of the path `P_n` with colours in `{1, …, t}`; the partition
    is given by the class map `A`. -/
def IsPackingDomatic (n k t : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ v, 1 ≤ f v ∧ f v ≤ t) ∧
    (∀ u v : Fin n, u ≠ v → f u = f v → f u < Nat.dist u v) ∧
    ∃ A : Fin n → Fin k, ∀ (i : Fin k) (x : Fin n), ∃ a, A a = i ∧ Nat.dist x a ≤ f a

/-- Problem 2, as asked: `χ_{ρ,k}(P_n) ≤ k + 1` for every `k ≥ 3` and `n ≥ 2k`. -/
def claim : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 2 * k ≤ n → ∃ f : Fin n → ℕ, IsPackingDomatic n k (k + 1) f

end D5.S3.Combinatorics.PackingDomatic.PackingDomaticPathDefs

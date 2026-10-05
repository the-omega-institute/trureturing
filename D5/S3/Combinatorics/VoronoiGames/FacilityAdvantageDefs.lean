/- GID: D5/S3/Combinatorics/VoronoiGames/FacilityAdvantageDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/VoronoiGames/FacilityAdvantageDefs
   mirror-E: none(waiver:maharaj-conjecture-one-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Real.Basic, mathlib/module/Mathlib.Order.Lattice.Nat]
   utility: none
   digest: Maharaj's Conjecture 1 on the facility advantage in the one-round discrete Voronoi game. -/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageDefs

/-! Fixed public statement: T. Maharaj, *The Facility Advantage in the One-Round Discrete Voronoi
    Game on a Line*, arXiv:2609.24936v1, Section 4.3: "Conjecture 1. k*(ℓ) = ℓ + 1 for every
    ℓ ≥ 2." Section 1: a finite multiset V of voters on the real line is given; player P selects
    a set P of k points, then player Q selects a set Q of ℓ points; P wins a voter v if
    dist(v, P) ≤ dist(v, Q) (ties favour P); Γ_{k,ℓ}(V) = max_P min_Q |V[P ≻ Q]|, and P wins iff
    Γ_{k,ℓ}(V) ≥ n/2 with n the number of voters. Definition 1: k*(ℓ) = min{k : Γ_{k,ℓ}(V) ≥ n/2
    for every finite multiset V ⊂ ℝ}, with k ≥ 1. For nonempty P and Q, dist(v, P) ≤ dist(v, Q)
    holds exactly when every point of Q is at least as far from v as some point of P. -/

/-- The voters of `V` won by `P` against `Q`: those at least as close to `P` as to `Q`. -/
noncomputable def won (V : Multiset ℝ) (P Q : Finset ℝ) : ℕ :=
  Multiset.card (V.filter fun v => ∀ q ∈ Q, ∃ p ∈ P, |v - p| ≤ |v - q|)

/-- `Γ_{k,ℓ}(V)`: the number of voters `P` guarantees with `k` facilities against `ℓ`. -/
noncomputable def gameValue (k ℓ : ℕ) (V : Multiset ℝ) : ℕ :=
  sSup {x | ∃ P : Finset ℝ, P.card = k ∧
    x = sInf {y | ∃ Q : Finset ℝ, Q.card = ℓ ∧ y = won V P Q}}

/-- `k*(ℓ)`: the least `k ≥ 1` with which `P` wins every instance against `ℓ` facilities. -/
noncomputable def kStar (ℓ : ℕ) : ℕ :=
  sInf {k | 1 ≤ k ∧ ∀ V : Multiset ℝ, Multiset.card V ≤ 2 * gameValue k ℓ V}

/-- Conjecture 1. -/
def claim : Prop := ∀ ℓ : ℕ, 2 ≤ ℓ → kStar ℓ = ℓ + 1

end D5.S3.Combinatorics.VoronoiGames.FacilityAdvantageDefs

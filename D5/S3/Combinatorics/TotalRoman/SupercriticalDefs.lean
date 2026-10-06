/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalDefs
   mirror-E: none(waiver:mynhardt-ogden-total-roman-supercritical-conjectures-statement)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Operations, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum, mathlib/module/Mathlib.Order.Lattice.Nat]
   utility: none
   digest: Mynhardt and Ogden's Conjectures 1 and 2 on total Roman domination edge-supercritical graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalDefs

/-! Fixed public statements: C. M. Mynhardt and S. E. A. Ogden, *Total Roman Domination
    Edge-Supercritical and Edge-Removal-Supercritical Graphs*, Australas. J. Combin. 78(3) (2020),
    arXiv:2002.01347v1, Section 10: "Conjecture 1. If G is a γ_tR-edge-supercritical graph and
    v ∈ V(G), then there exists a γ_tR(G)-function f such that v ∈ V_f^+." "Conjecture 2. If G is a
    k-γ_tR-edge-supercritical graph, then G ∪ K_n is (k + 3)-γ_tR-edge-critical, for n ≥ 3."
    Section 1: a TRD-function on a graph without isolated vertices is f : V → {0, 1, 2} such that
    every vertex with f(v) = 0 has a neighbour u with f(u) = 2 and every vertex with f(v) > 0 has a
    neighbour u with f(u) > 0; γ_tR is the minimum weight and a γ_tR(G)-function attains it. A graph
    without isolated vertices whose complement has an edge is γ_tR-edge-critical if
    γ_tR(G + e) < γ_tR(G) for every edge e of the complement, k-γ_tR-edge-critical if moreover
    γ_tR(G) = k, and γ_tR-edge-supercritical if γ_tR(G + e) ≤ γ_tR(G) − 2 for every such e. -/

variable {V : Type*}

/-- `f` is a total Roman dominating function of `G`. -/
def IsTRDF (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 2) ∧ (∀ v, f v = 0 → ∃ u, G.Adj v u ∧ f u = 2) ∧
    ∀ v, 0 < f v → ∃ u, G.Adj v u ∧ 0 < f u

/-- The total Roman domination number `γ_tR(G)`. -/
noncomputable def gammaTR [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ f : V → ℕ, IsTRDF G f ∧ w = ∑ v, f v}

/-- `G` has no isolated vertices and its complement has an edge. -/
def Admissible (G : SimpleGraph V) : Prop :=
  (∀ v, ∃ u, G.Adj v u) ∧ ∃ u v, u ≠ v ∧ ¬ G.Adj u v

/-- `G` is `γ_tR`-edge-supercritical. -/
def Supercritical [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  Admissible G ∧ ∀ u v, u ≠ v → ¬ G.Adj u v → gammaTR (G ⊔ SimpleGraph.edge u v) + 2 ≤ gammaTR G

/-- `G` is `k`-`γ_tR`-edge-critical. -/
def EdgeCritical [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  Admissible G ∧ gammaTR G = k ∧
    ∀ u v, u ≠ v → ¬ G.Adj u v → gammaTR (G ⊔ SimpleGraph.edge u v) < gammaTR G

/-- Conjecture 1. -/
def claimSupport : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), Supercritical G →
    ∀ v, ∃ f : V → ℕ, IsTRDF G f ∧ ∑ x, f x = gammaTR G ∧ 0 < f v

/-- Conjecture 2. -/
def claimCliqueUnion : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k n : ℕ), Supercritical G →
    gammaTR G = k → 3 ≤ n → EdgeCritical (G ⊕g (⊤ : SimpleGraph (Fin n))) (k + 3)

end D5.S3.Combinatorics.TotalRoman.SupercriticalDefs

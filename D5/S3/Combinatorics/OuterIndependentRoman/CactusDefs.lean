/- GID: D5/S3/Combinatorics/OuterIndependentRoman/CactusDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OuterIndependentRoman/CactusDefs
   mirror-E: none(waiver:nazari-moghaddam-chellali-sheikholeslami-cactus-conjecture-statement)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths, mathlib/module/Mathlib.Data.Set.Card, mathlib/module/Mathlib.Order.Lattice.Nat]
   utility: none
   digest: Conjecture 3.3 of Nazari-Moghaddam, Chellali and Sheikholeslami on outer independent double Roman domination of connected cacti. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Set.Card
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OuterIndependentRoman.CactusDefs

/-! Fixed public statement: S. Nazari-Moghaddam, M. Chellali and S. M. Sheikholeslami, *Outer
    independent double Roman domination in unicyclic and bicyclic graphs*, Ars Combin. 162 (2025)
    51–70: "Conjecture 3.3. If G is a connected cactus graph of order n and having k cycles, then
    γ_oidR(G) ≤ (5n+2k)/4." Section 1: an OIDRDF is f : V → {0, 1, 2, 3} such that every vertex
    with f(v) = 0 is adjacent to a vertex assigned 3 or to at least two vertices assigned 2, every
    vertex with f(v) = 1 has a neighbour assigned 2 or 3, and no two vertices assigned 0 are
    adjacent; γ_oidR is the minimum weight. A cactus is a graph in which each edge belongs to at
    most one cycle. Cycles are counted as edge sets. The paper's base case (its Theorem 1.1) is
    stated for trees of order n ≥ 3, and every graph with a cycle has n ≥ 3; the statement below
    keeps n ≥ 3, since K_1 and K_2 have γ_oidR = 2 and 3. -/

variable {V : Type*}

/-- `f` is an outer independent double Roman dominating function of `G`. -/
def IsOIDRDF (G : SimpleGraph V) (f : V → ℕ) : Prop :=
  (∀ v, f v ≤ 3) ∧
    (∀ v, f v = 0 → (∃ u, G.Adj v u ∧ f u = 3) ∨
      ∃ u w, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ f u = 2 ∧ f w = 2) ∧
    (∀ v, f v = 1 → ∃ u, G.Adj v u ∧ 2 ≤ f u) ∧
    ∀ u v, G.Adj u v → f u = 0 → f v ≠ 0

/-- The outer independent double Roman domination number `γ_oidR(G)`. -/
noncomputable def gammaOIDR [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ f : V → ℕ, IsOIDRDF G f ∧ w = ∑ v, f v}

/-- The cycles of `G`, recorded by their edge sets. -/
def cycleEdgeSets [DecidableEq V] (G : SimpleGraph V) : Set (Finset (Sym2 V)) :=
  {s | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ s = c.edges.toFinset}

/-- `G` is a cactus: every edge lies on at most one cycle. -/
def IsCactus [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ e : Sym2 V, Set.Subsingleton {s | s ∈ cycleEdgeSets G ∧ e ∈ s}

/-- Conjecture 3.3. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), G.Connected → IsCactus G →
    3 ≤ Fintype.card V →
      4 * gammaOIDR G ≤ 5 * Fintype.card V + 2 * (cycleEdgeSets G).ncard

end D5.S3.Combinatorics.OuterIndependentRoman.CactusDefs

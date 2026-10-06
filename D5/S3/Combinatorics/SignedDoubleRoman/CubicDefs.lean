/- GID: D5/S3/Combinatorics/SignedDoubleRoman/CubicDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/CubicDefs
   mirror-E: none(waiver:amjadi-et-al-cubic-signed-double-roman-problem-statement)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite, mathlib/module/Mathlib.Data.Int.ConditionallyCompleteOrder]
   utility: none
   digest: Problem 3.1 of Amjadi, Yang, Nazari-Moghaddam, Sheikholeslami and Shao on signed double Roman 2-domination of cubic graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.ConditionallyCompleteOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.CubicDefs

/-! Fixed public statement: J. Amjadi, H. Yang, S. Nazari-Moghaddam, S. M. Sheikholeslami and
    Z. Shao, *Signed double Roman k-domination in graphs*, Australas. J. Combin. 72(1) (2018), as
    restated in Varieties of Roman domination IV (AKCE Int. J. Graphs Comb., 2025), Section 2.5.2:
    "Problem 1. Is it true that if G is a cubic graph of order n, then γ²_sdR(G) ≤ n?" Section 2.5:
    a signed double Roman k-dominating function is f : V → {−1, 1, 2, 3} such that f(N[v]) ≥ k for
    every vertex v, every vertex with f(v) = −1 is adjacent to at least two vertices assigned 2 or
    to at least one vertex assigned 3, and every vertex with f(v) = 1 is adjacent to at least one
    vertex w with f(w) ≥ 2; γ^k_sdR is the minimum weight. The affirmative answer is `claim`. -/

variable {V : Type*} [Fintype V]

/-- `f` is a signed double Roman `k`-dominating function of `G`. -/
def IsSDRkDF (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℤ) (f : V → ℤ) : Prop :=
  (∀ v, f v = -1 ∨ f v = 1 ∨ f v = 2 ∨ f v = 3) ∧
    (∀ v, k ≤ f v + ∑ u ∈ G.neighborFinset v, f u) ∧
    (∀ v, f v = -1 → (∃ u, G.Adj v u ∧ f u = 3) ∨
      ∃ u w, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ f u = 2 ∧ f w = 2) ∧
    ∀ v, f v = 1 → ∃ u, G.Adj v u ∧ 2 ≤ f u

/-- The signed double Roman `k`-domination number `γ^k_sdR(G)`. -/
noncomputable def gammaSDR (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℤ) : ℤ :=
  sInf {w | ∃ f : V → ℤ, IsSDRkDF G k f ∧ w = ∑ v, f v}

/-- Problem 3.1, affirmative answer: `γ²_sdR(G) ≤ n` for every cubic graph of order `n`. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v, (G.neighborFinset v).card = 3) → gammaSDR G 2 ≤ Fintype.card V

end D5.S3.Combinatorics.SignedDoubleRoman.CubicDefs

/- GID: D5/S3/Combinatorics/SignedRoman/WeakSignedRomanDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedRoman/WeakSignedRomanDefs
   mirror-E: none(waiver:volkmann-weak-signed-roman-three-domination-tree-conjecture-statement)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite, mathlib/module/Mathlib.Data.Int.ConditionallyCompleteOrder]
   utility: none
   digest: Volkmann's conjecture that every tree of order n ≥ 2 has weak signed Roman 3-domination number at least (4n + 7)/5. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.ConditionallyCompleteOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.SignedRoman.WeakSignedRomanDefs

/-! Fixed public statement: L. Volkmann, *Weak signed Roman k-domination in graphs*, Commun.
    Comb. Optim. 6(1) (2021), as restated in M. Chellali, N. Jafari Rad, S. M. Sheikholeslami and
    L. Volkmann, *Varieties of Roman domination IV*, AKCE Int. J. Graphs Comb. (2025), Section
    2.2.3: "In [11], the author conjectured that the better bound γ³_wsR(T) ≥ (4n+7)/5 is valid for
    each tree T of order n ≥ 2." Section 2.2: a weak signed Roman k-dominating function of G is a
    function f : V(G) → {−1, 1, 2} with f(N[v]) ≥ k for every vertex v, where N[v] is the closed
    neighbourhood; its weight is the sum of its values, and γ^k_wsR(G) is the minimum weight. -/

variable {V : Type*} [Fintype V]

/-- `f` is a weak signed Roman `k`-dominating function of `G`. -/
def IsWeakSignedRoman (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℤ) (f : V → ℤ) : Prop :=
  (∀ v, f v = -1 ∨ f v = 1 ∨ f v = 2) ∧
    ∀ v, k ≤ f v + ∑ u ∈ G.neighborFinset v, f u

/-- The weak signed Roman `k`-domination number `γ^k_wsR(G)`. -/
noncomputable def weakSignedRomanNumber (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℤ) : ℤ :=
  sInf {w | ∃ f : V → ℤ, IsWeakSignedRoman G k f ∧ w = ∑ v, f v}

/-- Volkmann's conjecture: `γ³_wsR(T) ≥ (4n + 7)/5` for every tree of order `n ≥ 2`. -/
def claim : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) [DecidableRel T.Adj], 2 ≤ n → T.IsTree →
    4 * (n : ℤ) + 7 ≤ 5 * weakSignedRomanNumber T 3

end D5.S3.Combinatorics.SignedRoman.WeakSignedRomanDefs

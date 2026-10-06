/- GID: D5/S3/Combinatorics/OddIndependence/OddGridDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddIndependence/OddGridDefs
   mirror-E: none(waiver:caro-petrusevski-skrekovski-tuza-problem-twenty-nine-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Hasse, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Prod, mathlib/module/Mathlib.Topology.Instances.Real.Lemmas]
   utility: none
   digest: Problem 29 of Caro, Petruševski, Škrekovski and Tuza on dense independent sets of the square grid. -/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddIndependence.OddGridDefs

open Filter

/-! Fixed public statement: Y. Caro, M. Petruševski, R. Škrekovski and Zs. Tuza, *The odd
    independence number of graphs, II: Finite and infinite grids and chessboard graphs*,
    arXiv:2510.01897v1, Section 6.1: "Problem 29. Does there exist a sequence ϵ_n with
    lim_{n→∞} ϵ_n = 0, such that any (3/8 + ϵ_n) n² independent vertices of P_n □ P_n contain all
    the four neighbors of some vertex?" P_n is the path on n vertices and □ the Cartesian product.
    The affirmative answer is recorded as `claim`: a set of at least (3/8 + ϵ_n) n² vertices that
    is independent contains the whole neighbourhood of some vertex with four neighbours. -/

/-- The square grid `P_n □ P_n`. -/
def grid (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.pathGraph n □ SimpleGraph.pathGraph n

/-- Problem 29, affirmative answer. -/
def claim : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
    ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), (grid n).IsIndepSet (S : Set (Fin n × Fin n)) →
      ((3 / 8 : ℝ) + ε n) * (n : ℝ) ^ 2 ≤ (S.card : ℝ) →
        ∃ v : Fin n × Fin n, 4 ≤ ((grid n).neighborSet v).ncard ∧
          ∀ w, (grid n).Adj v w → w ∈ S

end D5.S3.Combinatorics.OddIndependence.OddGridDefs

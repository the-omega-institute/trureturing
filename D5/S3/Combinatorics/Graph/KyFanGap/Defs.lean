/- GID: D5/S3/Combinatorics/Graph/KyFanGap/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/KyFanGap/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.AdjMatrix]
   utility: none
   digest: Ky Fan singular-value sums, graph maxima, and the asymptotic gap predicate. -/

import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! Definitions for the Ky Fan graph gap problem. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.KyFanGap

open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

/- The sum is indexed by `Fin k`; singular values outside the finite rank are zero. -/
def kyFan (k : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  kyFanSum k (Matrix.toEuclideanLin M)

/- The finite maximum is written as a supremum over the nonempty finite graph type. -/
def xi (k n : ℕ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty)
    (fun G : SimpleGraph (Fin n) =>
      letI : DecidableRel G.Adj := Classical.decRel _
      kyFan k (G.adjMatrix ℝ))

def conjecture : Prop :=
  Set.Infinite
    {k : ℕ |
      ∃ L : ℝ,
        Filter.Tendsto (fun n : ℕ => xi k n / n) Filter.atTop (nhds L) ∧
          L < (1 + Real.sqrt k) / 2}

end D5.S3.Combinatorics.Graph.KyFanGap

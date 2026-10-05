/- GID: D5/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PhylogeneticRank/PhylogeneticRankDefs
   mirror-E: none(waiver:ashworth-et-al-conjecture-seven-one-statement-definition)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Topology.Instances.Real.Lemmas]
   utility: none
   digest: Conjecture 7.1 of Ashworth et al. on the maximal phylogenetic density of n-vertex graphs. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankDefs

/-! Fixed public statement: F. Ashworth, O. Clarke, J. Giansiracusa, J. Jones,
    J. Quijas-Aceves and Y. Ren, *The phylogenetic rank of a graph*, arXiv:2609.19372v1,
    Section 7: "Conjecture 7.1 We have lim_{n→∞} max_{|V(G)|=n} ρ(G) = 1", where
    `ρ(G) = r(G)/|V(G)|` and the phylogenetic rank `r(G)` is the least `k` such that the
    graph metric of `G` (Convention 2.1: finite, simple, connected, unit edge lengths) embeds
    isometrically into a product of `k` metric trees with the supremum metric (Definition 2.2).
    Metric trees have arbitrary positive edge lengths and points may lie inside edges;
    subdividing the edges at the finitely many image points makes every image a vertex, so a
    metric tree is recorded here as a finite tree with positive edge lengths and its weighted
    path metric, and vertices of `G` map to vertices of the tree. -/

open SimpleGraph

/-- A finite metric tree: a tree on `Fin m` with positive symmetric edge lengths. -/
structure MetricTree where
  m : ℕ
  graph : SimpleGraph (Fin m)
  isTree : graph.IsTree
  len : Fin m → Fin m → ℝ
  len_symm : ∀ u v, len u v = len v u
  len_pos : ∀ u v, graph.Adj u v → 0 < len u v

namespace MetricTree

/-- The total edge length of a walk. -/
def walkLength (T : MetricTree) : ∀ {u v : Fin T.m}, T.graph.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := v) _ p => T.len u v + walkLength T p

/-- The path metric of a metric tree: the least total length of a walk. -/
noncomputable def dist (T : MetricTree) (u v : Fin T.m) : ℝ :=
  sInf (Set.range fun p : T.graph.Walk u v => T.walkLength p)

end MetricTree

/-- `G` embeds isometrically into a product of `k` metric trees with the supremum metric. -/
def HasTreeEmbedding {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ T : Fin k → MetricTree, ∃ f : ∀ i, Fin n → Fin (T i).m,
    ∀ a b, (G.dist a b : ℝ) = ⨆ i, (T i).dist (f i a) (f i b)

/-- The phylogenetic rank: the least number of metric-tree factors of a tree embedding. -/
noncomputable def phyloRank {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | HasTreeEmbedding G k}

/-- The maximal phylogenetic density `r(G)/n` over connected graphs on `n` vertices. -/
noncomputable def maxDensity (n : ℕ) : ℝ :=
  sSup {x | ∃ G : SimpleGraph (Fin n), G.Connected ∧ x = (phyloRank G : ℝ) / n}

/-- Conjecture 7.1. -/
def claim : Prop := Filter.Tendsto maxDensity Filter.atTop (nhds 1)

end D5.S3.Combinatorics.PhylogeneticRank.PhylogeneticRankDefs

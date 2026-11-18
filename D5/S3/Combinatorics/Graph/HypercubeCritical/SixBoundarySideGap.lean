/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: An actual six-boundary bipartite side of Q9 has two, four, or at least twenty-eight vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCubical

/-! The six-boundary side gap follows from actual short paths, the seven-vertex
partner obstruction, and the cubical obstruction to the eight-vertex core. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open SimpleGraph
open scoped Classical
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q)
open private small_side_cases from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCounting
open private eleven_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideLabeling
open private twelve_impossible from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCubical

/-- A finite induced subgraph of Q9 with a cubic left side, right degrees at most
three, girth at least eight and two more right vertices has order two, four, or
at least twenty-eight. No balance or connectivity hypothesis is required. -/
theorem six_boundary_side_gap (C : Finset (Q 9))
    (L R : Finset (C : Set (Q 9)))
    (hb : ((hypercube 9).induce (C : Set (Q 9))).IsBipartiteWith (L : Set _) (R : Set _))
    (hcover : L ∪ R = Finset.univ)
    (hd : ∀ x ∈ L, ((hypercube 9).induce (C : Set (Q 9))).degree x = 3)
    (hr : ∀ y ∈ R, ((hypercube 9).induce (C : Set (Q 9))).degree y ≤ 3)
    (hg : (8 : ℕ∞) ≤ ((hypercube 9).induce (C : Set (Q 9))).egirth)
    (hcard : R.card = L.card + 2) : C.card = 2 ∨ C.card = 4 ∨ 28 ≤ C.card := by
  classical
  have hdis : Disjoint L R := by simpa only [Finset.disjoint_coe] using hb.disjoint
  have hsize : L.card + R.card = C.card := by
    rw [← Finset.card_union_of_disjoint hdis, hcover, Finset.card_univ]
    simp
  rcases small_side_cases hb hd hr hg hcard with h | h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact (eleven_impossible hb hd hr hg h (by omega)).elim
  · exact (twelve_impossible hb hd hr hg h (by omega)).elim
  · exact Or.inr (Or.inr (by omega))

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

/- GID: D5/S3/Combinatorics/Graph/RegularCHS/Result
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RegularCHS/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: The cycle and complete graph attain the regular connected CHS norm extrema. -/

import D5.S3.Combinatorics.Graph.RegularCHS.Newton
import D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
import D5.S3.Combinatorics.Graph.RegularCHS.Cubic
import D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
import Mathlib.Combinatorics.SimpleGraph.Acyclic

noncomputable section
open Classical
open scoped BigOperators
open D5.S3.Combinatorics.Graph.RegularCHS.Defs
open D5.S3.Combinatorics.Graph.RegularCHS.Interface
open D5.S3.Combinatorics.Graph.RegularCHS.Newton
open D5.S3.Combinatorics.Graph.RegularCHS.CycleBound
open D5.S3.Combinatorics.Graph.RegularCHS.Cubic
open D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular

namespace D5.S3.Combinatorics.Graph.RegularCHS.Result

private theorem two_le_regular {n r : ℕ} (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hconn : G.Connected) (hreg : G.IsRegularOfDegree r) : 2 ≤ r := by
  have hedge : n ≤ G.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin, G.card_edgeSet] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hdegree : ∀ v, G.degree v = r := fun v => by
    simpa only [← SimpleGraph.ncard_neighborSet] using hreg v
  have hsum : n * r = 2 * G.edgeFinset.card := by
    simpa only [hdegree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] using G.sum_degrees_eq_twice_card_edges
  by_contra hr
  have hr' : r ≤ 1 := by omega
  have hnr : n * r ≤ n := by simpa using Nat.mul_le_mul_left n hr'
  omega

end D5.S3.Combinatorics.Graph.RegularCHS.Result

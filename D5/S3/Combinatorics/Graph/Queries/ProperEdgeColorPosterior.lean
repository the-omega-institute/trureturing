/- GID: D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDetermineColorLikelihood; result=D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDoNotDetermineColorLikelihood; claim=D5/S3/Combinatorics/Graph/Queries/ProperEdgeColorPosterior.erasedRepliesDetermineColorLikelihood
   digest: Proper edge colors distinguish a path and a cycle with identical middle replies. -/

module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-! Uniform proper edge colors can carry information beyond the uncolored neighbor replies. -/

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior

private instance (G : SimpleGraph (Fin 4)) : DecidableRel G.lineGraph.Adj :=
  fun e f => decidable_of_iff (e ≠ f ∧ ∃ v : Fin 4, v ∈ (e : Sym2 (Fin 4)) ∧
    v ∈ (f : Sym2 (Fin 4))) G.lineGraph_adj_iff_exists.symm

/-- Proper edge assignments are proper vertex assignments on the line graph. -/
def properColors (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    Finset (G.edgeSet → Fin 3) :=
  Finset.univ.filter fun colors =>
    ∀ e f, G.lineGraph.Adj e f → colors e ≠ colors f

/-- Read the color of an adjacent vertex, using none for nonadjacent vertices. -/
def coloredReply (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (colors : G.edgeSet → Fin 3) (q v : Fin 4) : Option (Fin 3) :=
  if h : G.Adj q v then
    if q ≤ v then
      some (colors ⟨s(q, v), (SimpleGraph.mem_edgeSet (G := G)).mpr h⟩)
    else
      some (colors ⟨s(v, q), (SimpleGraph.mem_edgeSet (G := G)).mpr h.symm⟩)
  else none

/-- Proper assignments compatible with the two recorded complete replies. -/
def matchingColors (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] :
    Finset (G.edgeSet → Fin 3) :=
  (properColors G).filter fun colors =>
    (∀ v, coloredReply G colors 1 v =
      if v = 0 then some 0 else if v = 2 then some 1 else none) ∧
    (∀ v, coloredReply G colors 2 v =
      if v = 1 then some 1 else if v = 3 then some 0 else none)

/-- Count all proper assignments on the path or on the cycle. -/
def properColorCount (cycle : Bool) : ℕ :=
  if cycle then (properColors (SimpleGraph.cycleGraph 4)).card
  else (properColors (SimpleGraph.pathGraph 4)).card

/-- Count the proper assignments that produce the recorded pair of colored replies. -/
def matchingColorCount (cycle : Bool) : ℕ :=
  if cycle then (matchingColors (SimpleGraph.cycleGraph 4)).card
  else (matchingColors (SimpleGraph.pathGraph 4)).card

/-- The likelihood of this complete pair of replies under a uniform proper colouring. -/
def replyLikelihood (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : ℚ :=
  (matchingColors G).card / (properColors G).card

/-- Equal erased replies are conjectured to give equal likelihood for the recorded colours. -/
def erasedRepliesDetermineColorLikelihood : Prop :=
  ∀ (G H : SimpleGraph (Fin 4)) [DecidableRel G.Adj] [DecidableRel H.Adj],
    (properColors G).Nonempty → (properColors H).Nonempty →
    G.neighborFinset 1 = H.neighborFinset 1 →
    G.neighborFinset 2 = H.neighborFinset 2 →
    replyLikelihood G = replyLikelihood H

/-- The conditional probability of the cycle after the colored replies, given equal priors. -/
def cyclePosterior : ℚ :=
  let pathMass := replyLikelihood (SimpleGraph.pathGraph 4)
  let cycleMass := replyLikelihood (SimpleGraph.cycleGraph 4)
  cycleMass / (pathMass + cycleMass)

/-- The two uncolored queries agree in both graphs, while the colored record favors the cycle. -/
theorem proper_edge_colors_change_posterior :
    (∀ cycle : Bool, matchingColorCount cycle = (if cycle then 2 else 1) ∧
      properColorCount cycle = (if cycle then 18 else 12)) ∧
    (SimpleGraph.pathGraph 4).neighborFinset 1 = (SimpleGraph.cycleGraph 4).neighborFinset 1 ∧
    (SimpleGraph.pathGraph 4).neighborFinset 2 = (SimpleGraph.cycleGraph 4).neighborFinset 2 ∧
    cyclePosterior = 4 / 7 := by
  decide +kernel

/-- The path and cycle have matching uncolored replies and different colored likelihoods. -/
theorem erasedRepliesDoNotDetermineColorLikelihood : ¬ erasedRepliesDetermineColorLikelihood := by
  intro h
  obtain ⟨counts, firstReply, secondReply, _⟩ := proper_edge_colors_change_posterior
  have pathColors : (properColors (SimpleGraph.pathGraph 4)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < properColorCount false
    rw [(counts false).2]
    decide
  have cycleColors : (properColors (SimpleGraph.cycleGraph 4)).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < properColorCount true
    rw [(counts true).2]
    decide
  have equal := h (SimpleGraph.pathGraph 4) (SimpleGraph.cycleGraph 4)
    pathColors cycleColors firstReply secondReply
  change ((matchingColorCount false : ℚ) / properColorCount false) =
    ((matchingColorCount true : ℚ) / properColorCount true) at equal
  rw [(counts false).1, (counts false).2, (counts true).1, (counts true).2] at equal
  norm_num at equal

end D5.S3.Combinatorics.Graph.Queries.ProperEdgeColorPosterior

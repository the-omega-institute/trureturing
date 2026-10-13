/- GID: D5/S3/Combinatorics/Graph/Walks/PathRingSplicing
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/PathRingSplicing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicing]
   utility: none
   digest: Actual connections splice spanning graph pieces into a Hamilton cycle
     with exact support and edge lists. -/
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

open SimpleGraph
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Every consecutive pair is joined by a real edge of the ambient graph. -/
def Linked : Piece G → List (Piece G) → Prop
  | _, [] => True
  | p, q :: qs => G.Adj p.finish q.start ∧ Linked q qs

/-- The final endpoint follows the actual final piece. -/
def finish : Piece G → List (Piece G) → V
  | p, [] => p.finish
  | _, q :: qs => finish q qs

/-- Preserve all piece edges and insert just the prescribed real connections. -/
def chainEdges : Piece G → List (Piece G) → List (Sym2 V)
  | p, [] => p.walk.edges
  | p, q :: qs => p.walk.edges ++ s(p.finish, q.start) :: chainEdges q qs

private def join (p : Piece G) : (ps : List (Piece G)) →
    Linked p ps → G.Walk p.start (finish p ps)
  | [], _ => p.walk
  | q :: qs, h => p.walk.append ((join q qs h.2).cons h.1)

private theorem join_support (p : Piece G) (ps : List (Piece G)) (h : Linked p ps) :
    (join p ps h).support = (p :: ps).flatMap (fun z => z.walk.support) := by
  induction ps generalizing p with
  | nil => simp only [join, finish, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | cons q qs ih =>
    change (p.walk.append ((join q qs h.2).cons h.1)).support = _
    rw [Walk.support_append, Walk.support_cons, List.tail_cons]
    rw [ih]
    rfl

private theorem join_edges (p : Piece G) (ps : List (Piece G)) (h : Linked p ps) :
    (join p ps h).edges = chainEdges p ps := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih =>
    change (p.walk.append ((join q qs h.2).cons h.1)).edges = _
    rw [Walk.edges_append, Walk.edges_cons]
    rw [ih]
    rfl

variable [DecidableEq V]

/-- A list of genuine graph pieces whose supports independently partition the
whole vertex type becomes one actual Hamilton cycle. The final return is a
supplied graph edge; the support and edge inventories are literal lists. -/
theorem exists_spliced_hamiltonian_cycle (p : Piece G) (ps : List (Piece G))
    (h : Linked p ps) (hclose : G.Adj (finish p ps) p.start)
    (hfull : ∀ v : V, ((p :: ps).flatMap (fun z => z.walk.support)).count v = 1)
    (hsize : 3 ≤ ((p :: ps).flatMap (fun z => z.walk.support)).length) :
    ∃ c : G.Walk p.start p.start,
      c.IsHamiltonianCycle ∧
      c.support.tail = ((p :: ps).flatMap (fun z => z.walk.support)).reverse ∧
      c.edges = s(p.start, finish p ps) :: (chainEdges p ps).reverse := by
  let q := join p ps h
  have hq : q.IsHamiltonian := by
    intro v
    rw [show q.support = _ from join_support p ps h]
    exact hfull v
  have hqr : q.reverse.IsHamiltonian := by
    intro v
    simpa only [Walk.support_reverse, List.count_reverse] using hq v
  have hlen : 2 ≤ q.length := by
    rw [← join_support p ps h, Walk.length_support] at hsize
    change 2 ≤ (join p ps h).length
    omega
  have hmissing : s(p.start, finish p ps) ∉ q.reverse.edges := by
    intro he
    have he' : s(finish p ps, p.start) ∈ q.reverse.edges := by
      simpa only [Sym2.eq_swap] using he
    have heq := hqr.isPath.length_eq_one_of_mem_edges he'
    simp only [Walk.length_reverse] at heq
    omega
  refine ⟨q.reverse.cons hclose.symm, ?_, ?_, ?_⟩
  · apply Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mpr
    refine ⟨(Walk.cons_isCycle_iff q.reverse hclose.symm).mpr
      ⟨hqr.isPath, hmissing⟩, ?_⟩
    intro v
    simpa only [Walk.support_cons, List.tail_cons] using hqr v
  · simp only [Walk.support_cons, List.tail_cons, Walk.support_reverse]
    exact congrArg List.reverse (join_support p ps h)
  · simp only [Walk.edges_cons, Walk.edges_reverse]
    exact congrArg (s(p.start, finish p ps) :: ·) (congrArg List.reverse (join_edges p ps h))

#print axioms exists_spliced_hamiltonian_cycle

end D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

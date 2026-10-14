/- GID: D5/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualOuterChainExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extract the literal intermediate route and its inventories from a supplied closed parent. -/
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualOuterChainExtraction

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} {G : SimpleGraph V}

private def outsideChain (p q : Piece G) :
    (ps : List (Piece G)) → Linked p (ps ++ [q]) → G.Walk p.finish q.start
  | [], h => SimpleGraph.Walk.nil.cons h.1
  | r :: rs, h => (r.walk.append (outsideChain r q rs h.2)).cons h.1

private theorem outsideChain_support (p q : Piece G)
    (ps : List (Piece G)) (h : Linked p (ps ++ [q])) :
    (outsideChain p q ps h).support =
      p.finish :: ((ps.flatMap fun z => z.walk.support) ++ [q.start]) := by
  induction ps generalizing p with
  | nil => rfl
  | cons r rs ih =>
    simp only [outsideChain, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_append, ih, List.tail_cons,
      List.flatMap_cons, List.append_assoc]

private theorem outsideChain_edges (p q : Piece G)
    (ps : List (Piece G)) (h : Linked p (ps ++ [q])) :
    chainEdges p (ps ++ [q]) =
      p.walk.edges ++ (outsideChain p q ps h).edges ++ q.walk.edges := by
  induction ps generalizing p with
  | nil =>
    simp only [List.nil_append, chainEdges, outsideChain,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.cons_append, List.nil_append, List.append_assoc]
  | cons r rs ih =>
    change p.walk.edges ++ s(p.finish, r.start) :: chainEdges r (rs ++ [q]) = _
    rw [ih r h.2]
    simp only [outsideChain, SimpleGraph.Walk.edges_cons,
      SimpleGraph.Walk.edges_append, List.cons_append, List.append_assoc]

private theorem finish_append_last (p q : Piece G) (ps : List (Piece G)) :
    finish p (ps ++ [q]) = q.finish := by
  induction ps generalizing p with
  | nil => rfl
  | cons r rs ih => exact ih r

variable [DecidableEq V]

/-- The actual outside chain covers every remaining full child exactly
as supplied. Reversing the closed-route construction changes only list
order; the resulting support and edge inventories still refer to that
same actual parent cycle. -/
theorem actual_closed_route_outer_chain
    (p q : Piece G) (ps : List (Piece G)) (h : Linked p (ps ++ [q]))
    {base : V} (c : G.Walk base base) (hbase : base = p.start)
    (hcs : c.support.tail =
      ((p :: (ps ++ [q])).flatMap fun z => z.walk.support).reverse)
    (hce : c.edges = s(base, finish p (ps ++ [q])) ::
      (chainEdges p (ps ++ [q])).reverse) :
    ∃ chain : G.Walk p.finish q.start,
      ¬ chain.Nil ∧
      chain.support.tail.dropLast = (ps.flatMap fun z => z.walk.support) ∧
      c.support.tail.Perm
        (p.walk.support ++ q.walk.support ++ chain.support.tail.dropLast) ∧
      c.edges.Perm
        (p.walk.edges ++ q.walk.edges ++ chain.edges ++ [s(q.finish, p.start)]) := by
  let chain := outsideChain p q ps h
  have hsupport : chain.support =
      p.finish :: ((ps.flatMap fun z => z.walk.support) ++ [q.start]) :=
    outsideChain_support p q ps h
  have hn : ¬ chain.Nil := by
    intro hn
    have hz : chain.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hn
    have hslen := congrArg List.length hsupport
    simp only [SimpleGraph.Walk.length_support, List.length_cons,
      List.length_append, List.length_singleton, hz] at hslen
    omega
  have hinterior : chain.support.tail.dropLast =
      (ps.flatMap fun z => z.walk.support) := by
    simp only [hsupport, List.tail_cons, List.dropLast_concat]
  have hsperm : c.support.tail.Perm
      (p.walk.support ++ q.walk.support ++ chain.support.tail.dropLast) := by
    rw [hcs, hinterior]
    have h₀ := List.reverse_perm
      ((p :: (ps ++ [q])).flatMap fun z => z.walk.support)
    have h₁ := (show ((ps.flatMap fun z => z.walk.support) ++ q.walk.support).Perm
      (q.walk.support ++ (ps.flatMap fun z => z.walk.support)) from
      List.perm_append_comm).append_left p.walk.support
    apply h₀.trans
    simpa only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
      List.append_nil, List.append_assoc] using h₁
  have heperm : c.edges.Perm
      (p.walk.edges ++ q.walk.edges ++ chain.edges ++ [s(q.finish, p.start)]) := by
    classical
    apply List.perm_iff_count.mpr
    intro e
    have hechain : chainEdges p (ps ++ [q]) =
        p.walk.edges ++ chain.edges ++ q.walk.edges :=
      outsideChain_edges p q ps h
    rw [hce, finish_append_last, hechain, hbase]
    have hswap : s(p.start, q.finish) = s(q.finish, p.start) := Sym2.eq_swap
    rw [hswap]
    simp only [List.count_cons, List.count_reverse, List.count_append,
      List.count_nil]
    omega
  exact ⟨chain, hn, hinterior, hsperm, heperm⟩

#print axioms actual_closed_route_outer_chain

end D5.S3.Combinatorics.Graph.Walks.ActualOuterChainExtraction

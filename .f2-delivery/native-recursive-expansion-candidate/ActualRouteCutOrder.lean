/- UNCOMPILED actual-route helper for the J-state update.
   Ordered cut positions are a conclusion of the literal support of an
   actual joined route. Inputs identify the two real route pieces and their
   real oriented cuts; no final i<j certificate or next pairing is an input. -/
import D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
import D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.Infix

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder

open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.OrderedTwoCutSlicing
open private join join_support from
  D5.S3.Combinatorics.Graph.Walks.PathRingSplicing

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

private theorem route_piece_support_position (ps : List (Piece G))
    (r : ℕ) (hr : r < ps.length) (i : ℕ)
    (hi : i < (ps[r]'hr).walk.support.length) :
    (ps.flatMap (fun z => z.walk.support))
      [((ps.take r).flatMap (fun z => z.walk.support)).length + i]'(by
        have hsplit := List.take_append_drop r ps
        have hdrop := List.drop_eq_getElem_cons hr
        rw [← hsplit, List.flatMap_append, hdrop, List.flatMap_cons,
          List.length_append, List.length_append]
        omega) = (ps[r]'hr).walk.support[i]'hi := by
  have hsplit := List.take_append_drop r ps
  have hdrop := List.drop_eq_getElem_cons hr
  conv_lhs => arg 1; rw [← hsplit, List.flatMap_append, hdrop, List.flatMap_cons]
  rw [List.getElem_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem_append_left hi]

private theorem route_offsets_strict (ps : List (Piece G))
    {r s i j : ℕ} (hrs : r < s) (hs : s < ps.length)
    (hi : i < (ps[r]'(lt_trans hrs hs)).walk.length) :
    ((ps.take r).flatMap fun z => z.walk.support).length + i <
      ((ps.take s).flatMap fun z => z.walk.support).length + j := by
  have hhead :
      ((ps.take r).flatMap fun z => z.walk.support).length +
          (ps[r]'(lt_trans hrs hs)).walk.support.length ≤
        ((ps.take s).flatMap fun z => z.walk.support).length := by
    have hprefix : ps.take (r + 1) <+: ps.take s :=
      List.take_prefix_take_left (by omega)
    have hsub : (ps.take (r + 1)).flatMap (fun z => z.walk.support) <+:
        (ps.take s).flatMap (fun z => z.walk.support) :=
      hprefix.flatMap (fun z => z.walk.support)
    have hle := hsub.length_le
    rw [List.take_succ_eq_append_getElem (lt_trans hrs hs), List.flatMap_append,
      List.flatMap_singleton, List.length_append] at hle
    exact hle
  rw [SimpleGraph.Walk.length_support] at hhead
  omega

/-- Oriented cuts in two different actual route pieces occur in that
same order on the actual joined path. The route's literal full support
locates each cut, so the strict order is earned from the piece order. -/
theorem actual_joined_route_cut_order
    (p : Piece G) (ps : List (Piece G)) (hlink : Linked p ps)
    {r s i j : ℕ} (hrs : r < s) (hs : s < (p :: ps).length)
    (hi : i < ((p :: ps)[r]'(lt_trans hrs hs)).walk.length)
    (hj : j < ((p :: ps)[s]'hs).walk.length)
    {ℓ₀ r₀ ℓ₁ r₁ : V}
    (hℓ₀ : ((p :: ps)[r]'(lt_trans hrs hs)).walk.getVert i = ℓ₀)
    (hr₀ : ((p :: ps)[r]'(lt_trans hrs hs)).walk.getVert (i + 1) = r₀)
    (hℓ₁ : ((p :: ps)[s]'hs).walk.getVert j = ℓ₁)
    (hr₁ : ((p :: ps)[s]'hs).walk.getVert (j + 1) = r₁) :
    ∃ i' j' : ℕ, i' < j' ∧ j' < (join p ps hlink).length ∧
      (join p ps hlink).getVert i' = ℓ₀ ∧
      (join p ps hlink).getVert (i' + 1) = r₀ ∧
      (join p ps hlink).getVert j' = ℓ₁ ∧
      (join p ps hlink).getVert (j' + 1) = r₁ := by
  let pieces := p :: ps
  let q := join p ps hlink
  let offset (t : ℕ) := ((pieces.take t).flatMap fun z => z.walk.support).length
  have hsupport : q.support = pieces.flatMap (fun z => z.walk.support) :=
    join_support p ps hlink
  have hposition (t : ℕ) (ht : t < pieces.length) (n : ℕ)
      (hn : n ≤ (pieces[t]'ht).walk.length) :
      q.getVert (offset t + n) = (pieces[t]'ht).walk.getVert n := by
    have hlen : offset t + n < q.support.length := by
      rw [hsupport]
      have hsplit := List.take_append_drop t pieces
      have hdrop := List.drop_eq_getElem_cons ht
      rw [← hsplit, List.flatMap_append, hdrop, List.flatMap_cons,
        List.length_append, List.length_append, SimpleGraph.Walk.length_support]
      dsimp only [offset]
      omega
    rw [q.getVert_eq_support_getElem (by
      rw [SimpleGraph.Walk.length_support] at hlen; omega), hsupport]
    rw [route_piece_support_position pieces t ht n (by
        rw [SimpleGraph.Walk.length_support]; omega)]
    exact ((pieces[t]'ht).walk.getVert_eq_support_getElem hn).symm
  have hjlen : offset s + j + 1 < q.support.length := by
    rw [hsupport]
    have hsplit := List.take_append_drop s pieces
    have hdrop := List.drop_eq_getElem_cons hs
    rw [← hsplit, List.flatMap_append, hdrop, List.flatMap_cons,
      List.length_append, List.length_append, SimpleGraph.Walk.length_support]
    dsimp only [offset]
    omega
  rw [SimpleGraph.Walk.length_support] at hjlen
  refine ⟨offset r + i, offset s + j,
    route_offsets_strict pieces hrs hs hi, by omega, ?_, ?_, ?_, ?_⟩
  · exact (hposition r (lt_trans hrs hs) i (by omega)).trans hℓ₀
  · rw [Nat.add_assoc]
    exact (hposition r (lt_trans hrs hs) (i + 1) (by omega)).trans hr₀
  · exact (hposition s hs j (by omega)).trans hℓ₁
  · rw [Nat.add_assoc]
    exact (hposition s hs (j + 1) (by omega)).trans hr₁

/-- Apply the already available two-cut slicing to the strict order earned
above. These are the three actual Q fragments, retaining full support and
exactly the original route edges other than the two specified cuts. -/
theorem actual_joined_route_two_cut_slicing
    (p : Piece G) (ps : List (Piece G)) (hlink : Linked p ps)
    (hpath : (join p ps hlink).IsPath)
    {r s i j : ℕ} (hrs : r < s) (hs : s < (p :: ps).length)
    (hi : i < ((p :: ps)[r]'(lt_trans hrs hs)).walk.length)
    (hj : j < ((p :: ps)[s]'hs).walk.length)
    {ℓ₀ r₀ ℓ₁ r₁ : V}
    (hℓ₀ : ((p :: ps)[r]'(lt_trans hrs hs)).walk.getVert i = ℓ₀)
    (hr₀ : ((p :: ps)[r]'(lt_trans hrs hs)).walk.getVert (i + 1) = r₀)
    (hℓ₁ : ((p :: ps)[s]'hs).walk.getVert j = ℓ₁)
    (hr₁ : ((p :: ps)[s]'hs).walk.getVert (j + 1) = r₁) :
    ∃ q₀ : G.Walk p.start ℓ₀, ∃ q₁ : G.Walk r₀ ℓ₁,
      ∃ q₂ : G.Walk r₁ (finish p ps),
      q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
      q₀.support ++ q₁.support ++ q₂.support = (join p ps hlink).support ∧
      q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
        (join p ps hlink).edges ∧
      q₀.edges ++ q₁.edges ++ q₂.edges = (join p ps hlink).edges.filter
        (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  obtain ⟨i', j', hij, hj', h₀, h₁, h₂, h₃⟩ :=
    actual_joined_route_cut_order p ps hlink hrs hs hi hj hℓ₀ hr₀ hℓ₁ hr₁
  obtain ⟨q₀, q₁, q₂, hq₀, hq₁, hq₂, hsupp, hedge, hret, _, _, _⟩ :=
    exists_path_slicing_at_two_ordered_edges (join p ps hlink) hpath hij hj' h₀ h₁ h₂ h₃
  exact ⟨q₀, q₁, q₂, hq₀, hq₁, hq₂, hsupp, hedge, hret⟩

#print axioms actual_joined_route_cut_order
#print axioms actual_joined_route_two_cut_slicing

end D5.S3.Combinatorics.Graph.Walks.ActualRouteCutOrder

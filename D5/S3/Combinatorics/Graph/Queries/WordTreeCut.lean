/- GID: D5/S3/Combinatorics/Graph/Queries/WordTreeCut
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Queries/WordTreeCut
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Removing one parent edge of a finite word tree separates its child subtree. -/

import D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SimpleGraph
open D5.S3.Combinatorics.Graph.Queries.BinaryTreeLeafDistance

namespace D5.S3.Combinatorics.Graph.Queries.WordTreeCut

private theorem crossing_extension {r u : List Bool} (b : Bool)
    (hout : ¬ r <+: u) (hin : r <+: u ++ [b]) :
    r = u ++ [b] := by
  have hle := hin.length_le
  have hlarge : u.length < r.length := by
    by_contra! hsmall
    apply hout
    rw [List.prefix_iff_eq_take] at hin ⊢
    exact hin.trans (List.take_append_of_le_length hsmall)
  have hlen : r.length = (u ++ [b]).length := by
    simp at hle ⊢
    omega
  simpa only [hlen, List.take_length] using List.prefix_iff_eq_take.mp hin

private theorem prefix_boundary_edge (p : List Bool) (a : Bool) {u v : List Bool}
    (h : wordTree.Adj u v) (hout : ¬ p ++ [a] <+: u) (hin : p ++ [a] <+: v) :
    s(u, v) = s(p, p ++ [a]) := by
  rw [wordTree, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have he := crossing_extension b hout hin
    have hparent : p = u := by
      simpa only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil]
        using congrArg List.dropLast he
    subst u
    exact congrArg (fun l => s(p, l)) he.symm
  · exact False.elim (hout (hin.trans (List.prefix_append _ _)))

private theorem extension_walk_in_side (p : List Bool) (a : Bool) {u v : List Bool}
    (hPrefix : u <+: v) (hSame : (p ++ [a] <+: u ↔ p ++ [a] <+: v)) :
    ∃ w : (wordTree.deleteEdges {s(p, p ++ [a])}).Walk u v,
      ∀ x ∈ w.support, x.length ≤ v.length := by
  obtain ⟨suffix, rfl⟩ := hPrefix
  induction suffix using List.reverseRecOn with
  | nil =>
    let emptyWalk : (wordTree.deleteEdges {s(p, p ++ [a])}).Walk u u := .nil
    exact ⟨emptyWalk.copy rfl (List.append_nil u).symm, by simp [emptyWalk, Walk.support_copy]⟩
  | append_singleton suffix b ih =>
    rw [← List.append_assoc] at hSame ⊢
    have hPrefix₁ : u <+: u ++ suffix := List.prefix_append _ _
    have hPrefix₂ : u ++ suffix <+: (u ++ suffix) ++ [b] := List.prefix_append _ _
    have hPart : (p ++ [a] <+: u ↔ p ++ [a] <+: u ++ suffix) :=
      ⟨fun h => h.trans hPrefix₁, fun h => hSame.mpr (h.trans hPrefix₂)⟩
    obtain ⟨w, hw⟩ := ih hPart
    have hAdj : (wordTree.deleteEdges {s(p, p ++ [a])}).Adj (u ++ suffix) ((u ++ suffix) ++ [b]) := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨?_, ?_⟩
      · exact child_adj (u ++ suffix) b
      · intro h
        have hSide := hPart.symm.trans hSame
        rcases Sym2.eq_iff.mp (Set.mem_singleton_iff.mp h) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · rw [h₂, h₁] at hSide
          have hImpossible := (hSide.mpr (List.prefix_refl _)).length_le
          simp at hImpossible
        · have hLen := congrArg List.length h₁
          have hLen' := congrArg List.length h₂
          simp at hLen hLen'
          omega
    refine ⟨w.concat hAdj, ?_⟩
    intro x hx
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact (hw x hx).trans (by simp)
    · rfl

private theorem walk_preserves_side (p : List Bool) (a : Bool) {u v : List Bool}
    (walk : (wordTree.deleteEdges {s(p, p ++ [a])}).Walk u v)
    (hInside : p ++ [a] <+: v) : p ++ [a] <+: u := by
  classical
  by_contra hOutside
  let outside : Set (List Bool) := {word | ¬ p ++ [a] <+: word}
  obtain ⟨dart, _, hSource, hTarget⟩ :=
    walk.exists_boundary_dart outside hOutside (not_not_intro hInside)
  have hAdj := SimpleGraph.deleteEdges_adj.mp dart.adj
  exact hAdj.2 (by
    change dart.edge = s(p, p ++ [a])
    exact prefix_boundary_edge p a hAdj.1 hSource (not_not.mp hTarget))

private abbrev CutVertices (k : ℕ) := {w : List Bool // w.length ≤ k}

private theorem bounded_extension_reachable (k : ℕ) (p : List Bool) (a : Bool)
    {u v : CutVertices k} (hPrefix : u.1 <+: v.1)
    (hSame : p ++ [a] <+: u.1 ↔ p ++ [a] <+: v.1) :
    ((wordTree.deleteEdges {s(p, p ++ [a])}).induce {w : List Bool | w.length ≤ k}).Reachable u v := by
  obtain ⟨w, hSupport⟩ := extension_walk_in_side p a hPrefix hSame
  refine ⟨w.induce {x : List Bool | x.length ≤ k} (fun x hx => (hSupport x hx).trans v.2)⟩

private theorem induce_delete_extension (k : ℕ) (p : CutVertices k) (a : Bool)
    (hChild : (p.1 ++ [a]).length ≤ k) :
    (wordTree.deleteEdges {s(p.1, p.1 ++ [a])}).induce {w : List Bool | w.length ≤ k} =
      (boundedWordTree k).deleteEdges {s(p, ⟨p.1 ++ [a], hChild⟩)} := by
  ext u v
  rw [SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj]
  change (wordTree.Adj u.1 v.1 ∧ _) ↔ (wordTree.Adj u.1 v.1 ∧ _)
  simp only [Set.mem_singleton_iff, and_congr_right_iff]
  intro _
  apply not_congr
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h₁, Subtype.ext h₂⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h₁, Subtype.ext h₂⟩)
  · intro h
    exact congrArg (Sym2.map Subtype.val) h

/-- The descendants of the selected child, including the child itself. -/
def belowChild (k : ℕ) (p : CutVertices k) (bit : Bool) (word : CutVertices k) : Prop :=
  p.1 ++ [bit] <+: word.1

/-- Deleting the parent edge of a child separates its descendants from the other vertices. -/
theorem bounded_reachable_after_extension_cut (k : ℕ) (p : CutVertices k) (a : Bool)
    (hChild : (p.1 ++ [a]).length ≤ k) :
    let side := belowChild k p a
    ∀ u v : CutVertices k,
      ((boundedWordTree k).deleteEdges {s(p, ⟨p.1 ++ [a], hChild⟩)}).Reachable u v ↔
        (side u ↔ side v) := by
  intro side u v
  change ((boundedWordTree k).deleteEdges {s(p, ⟨p.1 ++ [a], hChild⟩)}).Reachable u v ↔
    (p.1 ++ [a] <+: u.1 ↔ p.1 ++ [a] <+: v.1)
  rw [← induce_delete_extension k p a hChild]
  constructor
  · rintro ⟨walk⟩
    let projected := walk.map (SimpleGraph.Embedding.induce _).toHom
    exact ⟨walk_preserves_side p.1 a projected.reverse, walk_preserves_side p.1 a projected⟩
  · intro h
    by_cases hu : p.1 ++ [a] <+: u.1
    · have hv := h.mp hu
      exact (bounded_extension_reachable k p.1 a (u := ⟨p.1 ++ [a], hChild⟩)
        hu (iff_of_true (List.prefix_refl _) hu)).symm.trans
        (bounded_extension_reachable k p.1 a (u := ⟨p.1 ++ [a], hChild⟩)
          hv (iff_of_true (List.prefix_refl _) hv))
    · have hv := mt h.mpr hu
      have hNil : ¬ p.1 ++ [a] <+: ([] : List Bool) := by simp
      exact (bounded_extension_reachable k p.1 a (u := ⟨[], by simp⟩)
        List.nil_prefix (iff_of_false hNil hu)).symm.trans
        (bounded_extension_reachable k p.1 a (u := ⟨[], by simp⟩)
          List.nil_prefix (iff_of_false hNil hv))

end D5.S3.Combinatorics.Graph.Queries.WordTreeCut

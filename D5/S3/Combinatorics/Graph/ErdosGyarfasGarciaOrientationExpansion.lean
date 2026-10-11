/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationExpansion
   generality: G
   mirror-B: none(waiver:external-open-problem-resolution)
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Disjoint internal paths with cyclic attachment edges expand to a simple cycle. -/

/-
proof_shape: cycle_of_disjoint_blocks: bind-only
consumers: Garcia orientation result in this delivery.
Direct frozen dependencies: none (pinned Mathlib only).
escape_witness: none; consumed organization of the cycle construction.
admission_basis: open-problem-resolution (#14828; consumed helper).
Utility none: the lemma is universal over a simple graph and path blocks.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationExpansion

open scoped BigOperators

private theorem cycle_of_list {V : Type*} (G : SimpleGraph V) (l : List V)
    (hn : l ≠ []) (hd : l.Nodup) (hc : l.IsChain G.Adj)
    (he : G.Adj (l.getLast hn) (l.head hn)) (hl : 3 ≤ l.length) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = l.length := by
  let p := SimpleGraph.Walk.ofSupport l hn hc
  let q := p.concat he
  have hlen : q.length = l.length := by
    simp only [q, SimpleGraph.Walk.length_concat, p, SimpleGraph.Walk.length_ofSupport]
    have : 0 < l.length := List.length_pos_iff.mpr hn
    omega
  have hdq : q.support.dropLast.Nodup := by
    simpa [q, SimpleGraph.Walk.support_concat, p] using hd
  have htail : q.support.tail.Nodup :=
    q.tail_support_perm_dropLast_support.nodup_iff.mpr hdq
  have hq : ¬q.Nil := by
    intro h
    have : q.length = 0 := by rw [h.eq_nil]; rfl
    omega
  refine ⟨l.head hn, q, ?_, hlen⟩
  apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, by omega⟩
  apply SimpleGraph.Walk.IsPath.mk'
  simpa only [q.support_tail_of_not_nil hq] using htail

/-- Disjoint path blocks linked in cyclic order give a cycle whose length is the
sum of their vertex counts: each internal path contributes its edge count and
each block contributes one attachment edge. -/
theorem cycle_of_disjoint_blocks {V : Type*} (G : SimpleGraph V) {n : ℕ}
    (blocks : Fin (n + 1) → List V)
    (hn : ∀ i, blocks i ≠ [])
    (hd : ∀ i, (blocks i).Nodup)
    (hc : ∀ i, (blocks i).IsChain G.Adj)
    (hj : ∀ i j, i ≠ j → List.Disjoint (blocks i) (blocks j))
    (he : ∀ i, ∀ x ∈ (blocks i).getLast?,
      ∀ y ∈ (blocks (finRotate (n + 1) i)).head?, G.Adj x y)
    (hl : 3 ≤ ∑ i, (blocks i).length) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = ∑ i, (blocks i).length := by
  let bs := List.ofFn blocks
  have hempty : [] ∉ bs := by
    simp only [bs, List.mem_ofFn]
    rintro ⟨i, hi⟩
    exact hn i hi
  have hbn : bs ≠ [] := by simp [bs]
  have hln : bs.flatten ≠ [] :=
    List.flatten_ne_nil_iff.mpr ⟨blocks 0, by simp [bs], hn 0⟩
  have hpair : bs.Pairwise List.Disjoint := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hj i j (ne_of_lt hij)
  have hnodup : bs.flatten.Nodup := List.nodup_flatten.mpr
    ⟨by
      intro b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact hd i, hpair⟩
  have hboundary : bs.IsChain (fun a b => ∀ x ∈ a.getLast?, ∀ y ∈ b.head?, G.Adj x y) := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [bs, List.length_ofFn] at hi
    simp only [bs, List.getElem_ofFn]
    simpa only [finRotate_of_lt (by omega : i < n)] using
      he ⟨i, by omega⟩
  have hchain : bs.flatten.IsChain G.Adj := (List.isChain_flatten hempty).mpr
    ⟨by
      intro b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact hc i, hboundary⟩
  have hlast : bs.flatten.getLast hln = (blocks (Fin.last n)).getLast (hn _) := by
    rw [List.getLast_flatten_eq_getLast_getLast]
    · change ((List.ofFn blocks).getLast _).getLast _ = _
      simp only [List.getLast_ofFn_succ]
    · change (List.ofFn blocks).getLast _ ≠ []
      rw [List.getLast_ofFn_succ]
      exact hn (Fin.last n)
  have hhead : bs.flatten.head hln = (blocks 0).head (hn 0) := by
    rw [List.head_flatten_eq_head_head]
    · simp [bs]
    · simpa [bs] using hn 0
  have hclose : G.Adj (bs.flatten.getLast hln) (bs.flatten.head hln) := by
    rw [hlast, hhead]
    apply he (Fin.last n)
    · simp [List.getLast?_eq_some_getLast (hn _)]
    · simp [List.head?_eq_some_head (hn 0)]
  have hlength : bs.flatten.length = ∑ i, (blocks i).length := by
    simp only [bs, List.length_flatten, List.map_ofFn, List.sum_ofFn]
    rfl
  obtain ⟨v, p, hp, hplen⟩ := cycle_of_list G bs.flatten hln hnodup hchain hclose
    (hlength.symm ▸ hl)
  exact ⟨v, p, hp, hplen.trans hlength⟩

end D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationExpansion

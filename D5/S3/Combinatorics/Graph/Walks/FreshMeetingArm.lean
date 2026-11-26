/- GID: D5/S3/Combinatorics/Graph/Walks/FreshMeetingArm
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/FreshMeetingArm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Paths]
   utility: none
   digest: Traversing two simple arms in order records each edge of the second arm afresh. -/

import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- After revealing the first arm and a strict prefix of the second, the next
edge of the second arm has not been revealed by either path. -/
theorem fresh_edge_after_first_arm {a b c : V} (p : G.Walk a b) (q : G.Walk a c)
    (hp : p.IsPath) (hq : q.IsPath)
    (hFirst : ¬ p.Nil → p.snd ≠ q.snd)
    (hInterior : ∀ i, 0 < i → i < q.length → q.getVert i ∉ p.support)
    (j : ℕ) (hj : j < q.length) :
    let seenEdges := p.edges ++ (q.take j).edges
    s(q.getVert j, q.getVert (j + 1)) ∉ seenEdges := by
  dsimp only
  rw [List.mem_append]
  intro he
  rcases he with he | he
  · have hx : q.getVert j ∈ p.support :=
      p.mem_support_of_mem_edges he (Sym2.mem_mk_left _ _)
    have hj0 : j = 0 := by
      by_contra h
      exact hInterior j (Nat.pos_of_ne_zero h) hj hx
    subst j
    simp only [Walk.getVert_zero, Nat.zero_add] at he
    obtain ⟨heq, hNotNil⟩ := hp.mk_start_mem_edges_iff.mp he
    exact hFirst hNotNil heq.symm
  · rw [Walk.edges_take] at he
    obtain ⟨i, hi, hiEdge⟩ := List.mem_iff_getElem.mp he
    have hiLt : i < j := lt_of_lt_of_le hi (by
      rw [List.length_take]
      exact min_le_left _ _)
    have hiLen : i < q.edges.length := by
      rw [Walk.length_edges]
      omega
    have hjLen : j < q.edges.length := by simpa using hj
    have hEq : q.edges[i]'hiLen = q.edges[j]'hjLen := by
      rw [← List.getElem_take (h := hi), hiEdge, q.getElem_edges]
    have hij := hq.isTrail.edges_nodup.getElem_inj_iff.mp hEq
    omega

end D5.S3.Combinatorics.Graph.Walks.FreshMeetingArm

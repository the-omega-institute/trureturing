/- GID: D5/S3/Combinatorics/Graph/Chordal/Characterization
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Characterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite chordality is equivalent to an injective perfect elimination order. -/

import D5.S3.Combinatorics.Graph.Chordal.EliminationForest
import D5.S3.Combinatorics.Graph.CliquePolynomial.FaalNonStable

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/

/-!
Adapted from LeanPool/lean-pool at edbe5bd56f476cc2965564676b66199f281ab714.
Source paths and the original proof attributions are specified in
Library/GraphInvariants/traversogianini2026brooks.md.
The complete Apache-2.0 LICENSE and upstream NOTICE are retained in
docs/reports/brooks-suppliers/lean-pool-LICENSE.txt and lean-pool-NOTICE.txt.
Modifications: repository imports and ordinary Lean sections replace the donor
module interface; only the dependencies of the finite PEO characterization are
retained, with pinned Mathlib walk suppliers used directly.
Retirement requires an equivalent complete characterization in the host's
pinned Mathlib, correspondence to the native predicate, and migrated consumers.
-/

/-! # The finite chordal graph characterization

The converse chooses a deepest top bag on the same cycle.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {ι : Type*} {T : CliqueTree G ι}

namespace CliqueTree

/-- The top nodes of two vertices sharing a bag are comparable. -/
theorem top_comparable_of_mem_bag {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k) :
    T.IsAncestor (T.top u) (T.top v) ∨ T.IsAncestor (T.top v) (T.top u) :=
  (isAncestor_top_of_mem_bag hu).comparable (isAncestor_top_of_mem_bag hv)

/-- If `u` and `v` share a bag and the top node of `v` has the smaller rank, then the top node of
`v` is an ancestor of the top node of `u`. -/
theorem isAncestor_top_of_rank_le {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k)
    (hrank : T.rank (T.top v) ≤ T.rank (T.top u)) : T.IsAncestor (T.top u) (T.top v) := by
  rcases top_comparable_of_mem_bag hu hv with h | h
  · exact h
  · exact (T.rank_injective (le_antisymm hrank h.rank_le)) ▸ isAncestor_refl _

/-- If `u` and `v` share a bag and the top node of `v` has the smaller rank, then `v` already lies
in the top bag of `u`. -/
theorem mem_bag_top_of_rank_le {k : ι} {u v : V} (hu : u ∈ T.bag k) (hv : v ∈ T.bag k)
    (hrank : T.rank (T.top v) ≤ T.rank (T.top u)) : v ∈ T.bag (T.top u) :=
  mem_bag_of_isAncestor hv (isAncestor_top_of_mem_bag hu)
    (isAncestor_top_of_rank_le hu hv hrank)

end CliqueTree
end SimpleGraph

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
/-- In a cycle of length at least `4`, the pair formed by the two neighbours of the base point is
not an edge of the cycle. -/
private theorem chord_notMem_edges {z : V} {c : G.Walk z z} (hc : c.IsCycle) (hn : 4 ≤ c.length) :
    s(c.getVert 1, c.getVert (c.length - 1)) ∉ c.edges := by
  intro hmem
  obtain ⟨i, hi, hei'⟩ := (Walk.mk_mem_edges_iff_exists c).mp hmem
  have hei := hei'.symm
  have hinj := hc.getVert_injOn
  have hzn : c.getVert c.length = z := c.getVert_length
  have hz0 : c.getVert 0 = z := c.getVert_zero
  rcases Sym2.eq_iff.1 hei with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hipos
    · have : (1 : ℕ) = c.length :=
        hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (by rw [h₁, hz0, hzn])
      omega
    · have e₁ : (1 : ℕ) = i :=
        hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show i ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₁
      have e₂ : c.length - 1 = i + 1 :=
        hinj (show c.length - 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
          (show i + 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₂
      omega
  · have e₁ : (1 : ℕ) = i + 1 :=
      hinj (show (1 : ℕ) ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (show i + 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩) h₁
    have hi0 : i = 0 := by omega
    subst hi0
    have : c.length - 1 = c.length :=
      hinj (show c.length - 1 ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (show c.length ∈ {i | 1 ≤ i ∧ i ≤ c.length} from ⟨by omega, by omega⟩)
        (by rw [h₂, hz0, hzn])
    omega

/-- **A graph carrying a clique tree is chordal.** -/
theorem IsChordal.of_nonempty_cliqueTree {ι : Type*} (T : CliqueTree G ι) : G.IsChordal := by
  classical
  intro v c hc hlen
  obtain ⟨z, hz, hzmax⟩ :=
    Finset.exists_max_image c.support.toFinset (fun u => T.rank (T.top u)) ⟨v, by simp⟩
  have hzs : z ∈ c.support := by simpa using hz
  have hcycle := hc.rotate hzs
  have hrot : (c.rotate z hzs).edges ~r c.edges := c.rotate_edges z hzs
  set c' := c.rotate z hzs with hc'def
  have hlen' : c'.length = c.length := by
    have h := hrot.perm.length_eq
    rwa [Walk.length_edges, Walk.length_edges] at h
  have hn : 4 ≤ c'.length := by omega
  -- the two neighbours of `z` along the cycle
  have hadjzx : G.Adj z (c'.getVert 1) := by
    have := c'.adj_getVert_succ (i := 0) (by omega)
    rwa [Walk.getVert_zero] at this
  have hadjyz : G.Adj (c'.getVert (c'.length - 1)) z := by
    have := c'.adj_getVert_succ (i := c'.length - 1) (by omega)
    rwa [show c'.length - 1 + 1 = c'.length by omega, Walk.getVert_length] at this
  have hsupp : ∀ w ∈ c'.support, w ∈ c.support := by
    intro w hw
    rw [← Walk.cons_tail_support] at hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hzs
    · exact List.mem_of_mem_tail ((c.support_rotate z hzs).mem_iff.1 hw)
  have hxs : c'.getVert 1 ∈ c.support := hsupp _ (c'.getVert_mem_support 1)
  have hys : c'.getVert (c'.length - 1) ∈ c.support :=
    hsupp _ (c'.getVert_mem_support (c'.length - 1))
  -- the chord
  obtain ⟨k, hzk, hxk⟩ := T.exists_bag_of_adj hadjzx
  have hxbag : c'.getVert 1 ∈ T.bag (T.top z) :=
    CliqueTree.mem_bag_top_of_rank_le hzk hxk (hzmax _ (by simpa using hxs))
  obtain ⟨k₂, hyk, hzk₂⟩ := T.exists_bag_of_adj hadjyz
  have hybag : c'.getVert (c'.length - 1) ∈ T.bag (T.top z) :=
    CliqueTree.mem_bag_top_of_rank_le hzk₂ hyk (hzmax _ (by simpa using hys))
  refine ⟨c'.getVert 1, c'.getVert (c'.length - 1), hxs, hys,
    T.bag_isClique (T.top z) (by simpa using hxbag) (by simpa using hybag)
      hcycle.snd_ne_penultimate, fun hmemE => chord_notMem_edges hcycle hn (hrot.mem_iff.2 hmemE)⟩
/-- **A graph carrying a perfect elimination order is chordal.** -/
theorem IsPEO.isChordal [Finite V] {ord : V → ℕ} (h : G.IsPEO ord) :
    G.IsChordal := by
  classical
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DecidableRel G.Adj := Classical.decRel _
  exact IsChordal.of_nonempty_cliqueTree h.cliqueTree

/-- **Chordality is exactly the existence of a perfect elimination order.** -/
theorem isChordal_iff_exists_isPEO [Finite V] :
    G.IsChordal ↔ ∃ ord : V → ℕ, G.IsPEO ord :=
  ⟨fun hG => hG.exists_isPEO, fun ⟨_, h⟩ => h.isChordal⟩

end SimpleGraph

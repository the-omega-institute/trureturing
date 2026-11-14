/- GID: D5/S3/Combinatorics/Graph/StarForming/FiberConnectivity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/FiberConnectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected]
   utility: none
   digest: Connected fibers and actual inter-fiber edges lift connectivity. -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The elementary block-connectivity argument used in the received cyclic
and reciprocal constructions. The inter-fiber premise asks for actual edges,
not just an abstract adjacency assigned to a quotient. -/
namespace D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity

/-- Connected fibers over a preconnected base give a preconnected graph.
Empty fibers may occur only where the explicit inter-fiber hypotheses allow. -/
theorem preconnected_of_fibers {V I : Type*} (G : SimpleGraph V)
    (Q : SimpleGraph I) (f : V → I) (hQ : Q.Preconnected)
    (hf : ∀ a b, f a = f b → G.Reachable a b)
    (he : ∀ i j, Q.Adj i j → ∃ a b, f a = i ∧ f b = j ∧ G.Adj a b) :
    G.Preconnected := by
  have hr (i j : I) (h : Q.Reachable i j) :
      ∀ a b, f a = i → f b = j → G.Reachable a b := by
    obtain ⟨w⟩ := h
    induction w with
    | nil =>
      intro a b ha hb
      exact hf a b (ha.trans hb.symm)
    | @cons i k j hik w ih =>
      obtain ⟨x,y,hx,hy,hxy⟩ := he i k hik
      intro a b ha hb
      exact (hf a x (ha.trans hx.symm)).trans (hxy.reachable.trans (ih y b hy hb))
  intro a b
  exact hr (f a) (f b) (hQ _ _) a b rfl rfl

/-- Two disjoint endpoint pairs cannot both be destroyed by one deletion. -/
theorem surviving_pair {V : Type*} (a b c d z : V)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (a ≠ z ∧ b ≠ z) ∨ (c ≠ z ∧ d ≠ z) := by
  by_cases ha : a = z
  · right
    constructor <;> intro h
    · exact hac (ha.trans h.symm)
    · exact had (ha.trans h.symm)
  · by_cases hb : b = z
    · right
      constructor <;> intro h
      · exact hbc (hb.trans h.symm)
      · exact hbd (hb.trans h.symm)
    · exact Or.inl ⟨ha,hb⟩

/-- A parent of smaller natural rank gives actual paths to the root. -/
theorem preconnected_of_rank {V : Type*} (G : SimpleGraph V) (root : V)
    (parent : V → V) (rank : V → ℕ)
    (hstep : ∀ v, v ≠ root → G.Adj v (parent v) ∧ rank (parent v) < rank v) :
    G.Preconnected := by
  have hr : ∀ n : ℕ, ∀ v, rank v = n → G.Reachable v root := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases he : v = root
      · subst v; exact SimpleGraph.Reachable.refl _
      · obtain ⟨ha,hl⟩ := hstep v he
        exact ha.reachable.trans (ih (rank (parent v)) (hv ▸ hl) (parent v) rfl)
  intro a b
  exact (hr _ a rfl).trans (hr _ b rfl).symm

end D5.S3.Combinatorics.Graph.StarForming.FiberConnectivity

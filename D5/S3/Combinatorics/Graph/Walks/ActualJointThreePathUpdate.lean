/- GID: D5/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/ActualJointThreePathUpdate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal P and Q fragments and the real connector assemble three simple joint paths with exact support and edge permutations. -/
import D5.S3.Combinatorics.Graph.Walks.ActualJointRouteSlicing
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.ActualJointThreePathUpdate

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Actual path pieces produce precisely the three new pairs of (58.20).
The source support includes the old distinguished P path, all of Q, and
the interiors of the remaining full-child chain. All other P paths can
therefore be retained unchanged in the full partition. -/
theorem actual_joint_three_path_update
    {ℓ s t z a ℓ₀ r₀ ℓ₁ r₁ b : V}
    (d : G.Walk ℓ z) (tail : G.Walk t z)
    (hₐ : G.Adj ℓ s) (h_b : G.Adj s t)
    (hd : d = (tail.cons h_b).cons hₐ)
    (Λ : G.Walk a b)
    (q₀ : G.Walk a ℓ₀) (q₁ : G.Walk r₀ ℓ₁) (q₂ : G.Walk r₁ b)
    (hQ : q₀.support ++ q₁.support ++ q₂.support = Λ.support)
    (chain : G.Walk b s) (hchain : ¬ chain.Nil) (hc : G.Adj t a)
    (hn : (d.support ++ Λ.support ++ chain.support.tail.dropLast).Nodup) :
    ∃ new₀ : G.Walk z ℓ₀, ∃ new₁ : G.Walk r₀ ℓ₁, ∃ new₂ : G.Walk r₁ ℓ,
      new₀.IsPath ∧ new₁.IsPath ∧ new₂.IsPath ∧
      (new₀.support ++ new₁.support ++ new₂.support).Nodup ∧
      (new₀.support ++ new₁.support ++ new₂.support).Perm
        (d.support ++ Λ.support ++ chain.support.tail.dropLast) ∧
      (new₀.edges ++ new₁.edges ++ new₂.edges).Perm
        (tail.edges ++ q₀.edges ++ q₁.edges ++ q₂.edges ++ chain.edges ++
          [s(ℓ, s), s(t, a)]) ∧
      new₀ = tail.reverse.append (q₀.cons hc) ∧
      new₁ = q₁ ∧ new₂ = (q₂.append chain).concat hₐ.symm := by
  let new₀ : G.Walk z ℓ₀ := tail.reverse.append (q₀.cons hc)
  let new₂ : G.Walk r₁ ℓ := (q₂.append chain).concat hₐ.symm
  have hctail : chain.support.tail ≠ [] := by
    intro h
    have hz := congrArg List.length h
    simp only [List.length_tail, SimpleGraph.Walk.length_support, List.length_nil] at hz
    exact hchain (SimpleGraph.Walk.length_eq_zero_iff.mp (by omega))
  have hcs : chain.support.tail.dropLast ++ [s] = chain.support.tail := by
    have h := List.dropLast_append_getLast hctail
    rw [List.getLast_tail, SimpleGraph.Walk.getLast_support] at h
    exact h
  have hs₀ : new₀.support = tail.support.reverse ++ q₀.support := by
    simp only [new₀, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse,
      SimpleGraph.Walk.support_cons, List.tail_cons]
  have hs₂ : new₂.support = q₂.support ++ chain.support.tail.dropLast ++ [s, ℓ] := by
    have h := congrArg (fun xs : List V => q₂.support ++ xs ++ [ℓ]) hcs
    simpa only [new₂, SimpleGraph.Walk.support_concat,
      SimpleGraph.Walk.support_append, List.append_assoc, List.singleton_append] using h.symm
  have hsperm : (new₀.support ++ q₁.support ++ new₂.support).Perm
      (d.support ++ Λ.support ++ chain.support.tail.dropLast) := by
    apply List.perm_iff_count.mpr
    intro v
    rw [hs₀, hs₂, hd, ← hQ]
    simp only [SimpleGraph.Walk.support_cons, List.count_append, List.count_cons,
      List.count_reverse, List.count_nil]
    omega
  have hnew : (new₀.support ++ q₁.support ++ new₂.support).Nodup :=
    hsperm.nodup_iff.mpr hn
  have he₀ : new₀.edges = tail.edges.reverse ++ s(t, a) :: q₀.edges := by
    simp only [new₀, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
      SimpleGraph.Walk.edges_cons]
  have he₂ : new₂.edges = q₂.edges ++ chain.edges ++ [s(s, ℓ)] := by
    simp only [new₂, SimpleGraph.Walk.edges_concat, SimpleGraph.Walk.edges_append,
      List.concat_eq_append]
  have he_a : s(s, ℓ) = s(ℓ, s) := Sym2.eq_swap
  have heperm : (new₀.edges ++ q₁.edges ++ new₂.edges).Perm
      (tail.edges ++ q₀.edges ++ q₁.edges ++ q₂.edges ++ chain.edges ++
        [s(ℓ, s), s(t, a)]) := by
    classical
    apply List.perm_iff_count.mpr
    intro e
    rw [he₀, he₂, he_a]
    simp only [List.count_append, List.count_reverse, List.count_cons, List.count_nil]
    omega
  have hnew' : ((new₀.support ++ q₁.support) ++ new₂.support).Nodup := by
    simpa only [List.append_assoc] using hnew
  have hn' := List.nodup_append'.mp hnew'
  have hnleft := List.nodup_append'.mp hn'.1
  exact ⟨new₀, q₁, new₂, SimpleGraph.Walk.IsPath.mk' hnleft.1,
    SimpleGraph.Walk.IsPath.mk' hnleft.2.1, SimpleGraph.Walk.IsPath.mk' hn'.2.1,
    hnew, hsperm, heperm, rfl, rfl, rfl⟩

#print axioms actual_joint_three_path_update

end D5.S3.Combinatorics.Graph.Walks.ActualJointThreePathUpdate

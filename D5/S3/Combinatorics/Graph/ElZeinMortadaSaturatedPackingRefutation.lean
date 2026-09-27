/- GID: D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric, mathlib/module/Mathlib.Tactic.FinCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.claim; result=D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.result; claim=D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.claim
   digest: Conjecture 3 is refuted by the seven-vertex graph FhcYG. -/

/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #8799)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.Graph.ElZeinMortadaSaturatedPackingRefutation

/-- Subcubic: `∆(G) ≤ 3`. -/
def Subcubic {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v ≤ 3

/-- `k`-saturated: every vertex of degree 3 is adjacent to at most `k` vertices of degree 3. -/
def Saturated {V : Type} [Fintype V] [DecidableEq V]
    (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ v, G.degree v = 3 →
    ((G.neighborFinset v).filter (fun u => G.degree u = 3)).card ≤ k

/-- An `S`-packing coloring for `S = (1, 1, 2)`: a partition of `V` into `V1`, `V2`, `V3`
(a coloring `c : V → Fin 3`; classes may be empty) with `dist > 1, > 1, > 2` inside the
classes. Distance is `SimpleGraph.edist` (`⊤` for unreachable pairs), the faithful reading of
`dist_G` on a possibly disconnected graph. -/
def IsPacking112 {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ c : V → Fin 3, ∀ u v, u ≠ v → c u = c v →
    if c u = 2 then (2 : ℕ∞) < G.edist u v else (1 : ℕ∞) < G.edist u v

/-- Conjecture 3 of arXiv:2603.25113v1 as printed (no local-girth hypothesis). -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
    Subcubic G → Saturated 2 G → IsPacking112 G

/-- The connected seven-vertex graph with graph6 encoding `FhcYG`. -/
private def counterexample : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 4) ∨
    (u = 1 ∧ v = 2) ∨ (u = 1 ∧ v = 6) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨
    (u = 3 ∧ v = 5) ∨ (u = 4 ∧ v = 5) ∨
    (u = 5 ∧ v = 6)

private instance counterexampleDecidableAdj : DecidableRel counterexample.Adj := by
  unfold counterexample
  infer_instance

/-- The graph `counterexample` refutes the printed Conjecture 3. -/
theorem result : ¬claim := by
  intro conjecture
  have subcubic : Subcubic counterexample := by
    unfold Subcubic
    simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
    decide +kernel
  have saturated : Saturated 2 counterexample := by
    unfold Saturated
    simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter]
    decide +kernel
  have counterexample_not_packing112 : ¬IsPacking112 counterexample := by
    let TriangleVertex : Fin 7 → Prop := fun v => v = 3 ∨ v = 4 ∨ v = 5
    let WithinTwo : Fin 7 → Fin 7 → Prop := fun u v =>
      counterexample.Adj u v ∨ ∃ w, counterexample.Adj u w ∧ counterexample.Adj w v
    have triangle_vertex_reaches_all_within_two :
        ∀ v, TriangleVertex v → ∀ u, u ≠ v → WithinTwo v u := by
      intro vertex triangleVertex u distinct
      fin_cases vertex <;> fin_cases u <;>
        simp_all [TriangleVertex, WithinTwo, counterexample] <;> decide
    have odd_five_colors (a b d e f : Fin 3)
        (ha : a ≠ 2) (hb : b ≠ 2) (hd : d ≠ 2) (he : e ≠ 2) (hf : f ≠ 2)
        (hab : a ≠ b) (hbd : b ≠ d) (hde : d ≠ e) (hef : e ≠ f) (hfa : f ≠ a) :
        False := by
      fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
        simp_all
    rintro ⟨c, packing⟩
    have independent : ∀ u v, u ≠ v → c u = c v → c u ≠ 2 →
        ¬counterexample.Adj u v := by
      intro u v distinct same notTwo adjacent
      have separated := packing u v distinct same
      rw [if_neg notTwo, SimpleGraph.edist_eq_one_iff_adj.mpr adjacent] at separated
      norm_num at separated
    have triangle_requires_color_two : ∃ v, TriangleVertex v ∧ c v = 2 := by
      by_contra h
      have h3 : c 3 ≠ 2 := by
        intro h3
        exact h ⟨3, Or.inl rfl, h3⟩
      have h4 : c 4 ≠ 2 := by
        intro h4
        exact h ⟨4, Or.inr (Or.inl rfl), h4⟩
      have h5 : c 5 ≠ 2 := by
        intro h5
        exact h ⟨5, Or.inr (Or.inr rfl), h5⟩
      have h34 : c 3 ≠ c 4 := by
        intro same
        exact independent 3 4 (by decide) same h3 (by decide)
      have h45 : c 4 ≠ c 5 := by
        intro same
        exact independent 4 5 (by decide) same h4 (by decide)
      have h35 : c 3 ≠ c 5 := by
        intro same
        exact independent 3 5 (by decide) same h3 (by decide)
      generalize hx : c 3 = x at *
      generalize hy : c 4 = y at *
      generalize hz : c 5 = z at *
      clear triangle_vertex_reaches_all_within_two odd_five_colors
      fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all
    obtain ⟨v, triangle, colorTwo⟩ := triangle_requires_color_two
    have edist_le_two_of_withinTwo :
        ∀ {u v : Fin 7}, WithinTwo u v → counterexample.edist u v ≤ 2 := by
      intro u w h
      rcases h with adjacent | ⟨middle, first, second⟩
      · rw [SimpleGraph.edist_eq_one_iff_adj.mpr adjacent]
        norm_num
      · let walk : counterexample.Walk u w := .cons first (.cons second .nil)
        have bound := walk.edist_le
        simpa [walk] using bound
    have uniqueTwo : ∀ u, u ≠ v → c u ≠ 2 := by
      intro u distinct otherTwo
      have separated := packing v u distinct.symm (colorTwo.trans otherTwo.symm)
      rw [if_pos colorTwo] at separated
      have close := edist_le_two_of_withinTwo
        (triangle_vertex_reaches_all_within_two v triangle u distinct)
      exact (not_lt_of_ge close) separated
    have noOddCycle (a b d e f : Fin 7)
        (ha : a ≠ v) (hb : b ≠ v) (hd : d ≠ v) (he : e ≠ v) (hf : f ≠ v)
        (hab : counterexample.Adj a b) (hbd : counterexample.Adj b d)
        (hde : counterexample.Adj d e) (hef : counterexample.Adj e f)
        (hfa : counterexample.Adj f a) : False := by
      have different (x y : Fin 7) (hx : x ≠ v)
          (edge : counterexample.Adj x y) : c x ≠ c y := by
        intro same
        exact independent x y edge.ne same (uniqueTwo x hx) edge
      exact odd_five_colors (c a) (c b) (c d) (c e) (c f)
        (uniqueTwo a ha) (uniqueTwo b hb) (uniqueTwo d hd)
        (uniqueTwo e he) (uniqueTwo f hf)
        (different a b ha hab) (different b d hb hbd) (different d e hd hde)
        (different e f he hef) (different f a hf hfa)
    rcases triangle with rfl | rfl | rfl
    · exact noOddCycle 0 1 6 5 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact noOddCycle 1 2 3 5 6 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact noOddCycle 0 1 2 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact counterexample_not_packing112
    (conjecture (Fin 7) counterexample subcubic saturated)

example : counterexample.degree 1 = 3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example : counterexample.degree 0 = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example :
    ((counterexample.neighborFinset 1).filter (fun u => counterexample.degree u = 3)).card = 0 := by
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example :
    ((counterexample.neighborFinset 3).filter (fun u => counterexample.degree u = 3)).card = 2 := by
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example :
    ((counterexample.neighborFinset 4).filter (fun u => counterexample.degree u = 3)).card = 2 := by
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example :
    ((counterexample.neighborFinset 5).filter (fun u => counterexample.degree u = 3)).card = 2 := by
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example : Subcubic counterexample := by
  unfold Subcubic
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example : Saturated 2 counterexample := by
  unfold Saturated
  simp_rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]
  decide +kernel

example : counterexample.Connected := by
  have reachable_from_zero (v : Fin 7) : counterexample.Reachable 0 v := by
    fin_cases v
    · exact SimpleGraph.Reachable.refl _
    · exact (show counterexample.Adj 0 1 from by decide).reachable
    · exact (show counterexample.Adj 0 1 from by decide).reachable.trans
        (show counterexample.Adj 1 2 from by decide).reachable
    · exact (show counterexample.Adj 0 4 from by decide).reachable.trans
        (show counterexample.Adj 4 3 from by decide).reachable
    · exact (show counterexample.Adj 0 4 from by decide).reachable
    · exact (show counterexample.Adj 0 4 from by decide).reachable.trans
        (show counterexample.Adj 4 5 from by decide).reachable
    · exact (show counterexample.Adj 0 1 from by decide).reachable.trans
        (show counterexample.Adj 1 6 from by decide).reachable
  exact ⟨fun u v => (reachable_from_zero u).symm.trans (reachable_from_zero v)⟩

example : counterexample.edist 0 5 = 2 := by
  let walk : counterexample.Walk 0 5 :=
    .cons (show counterexample.Adj 0 4 from by decide)
      (.cons (show counterexample.Adj 4 5 from by decide) .nil)
  have reachable : counterexample.Reachable 0 5 := walk.reachable
  rw [← reachable.coe_dist_eq_edist]
  have upper : counterexample.dist 0 5 ≤ 2 := by
    simpa [walk] using SimpleGraph.dist_le walk
  have positive : 0 < counterexample.dist 0 5 :=
    walk.reachable.pos_dist_of_ne (by decide)
  have notOne : counterexample.dist 0 5 ≠ 1 := by
    intro h
    have adjacent := SimpleGraph.dist_eq_one_iff_adj.mp h
    exact (by decide : ¬counterexample.Adj 0 5) adjacent
  have hdist : counterexample.dist 0 5 = 2 := by omega
  exact_mod_cast hdist

#print axioms result

end D5.S3.Combinatorics.Graph.ElZeinMortadaSaturatedPackingRefutation

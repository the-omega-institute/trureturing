/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCycle
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full independent bond law of any marked simple cycle reduces to three independent arcs. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalProduct

/-! Actual undirected cycle-edge sources retain their complete finite product law. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle

open SimpleGraph ThreeTerminalBond ThreeTerminalTree ThreeTerminalCycleArcs
open ThreeTerminalTriangleArms
open scoped BigOperators
set_option backward.isDefEq.respectTransparency.types false

private theorem ordered_cycle_law {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] {a : V} (p : G.Walk a a) (hp : p.IsCycle)
    {n : ℕ} (hlen : p.length = n + 3) (hedges : G.edgeSet = p.edgeSet)
    (i j : Fin (n + 3)) (hi : 0 < i.val) (hij : i.val < j.val)
    (θ : G.edgeSet → ℝ) :
    bondLaw G a (p.getVert i.val) (p.getVert j.val) θ =
      law (cycleEnds n) 0 i j (fun e => θ (cycleEdgeEquiv p hp hlen hedges e)) := by
  classical
  let e := cycleEdgeEquiv p hp hlen hedges
  let cfg : (G.edgeSet → Bool) ≃ (Fin (n + 3) → Bool) :=
    Equiv.arrowCongr e.symm (Equiv.refl Bool)
  have hcfg (ω : G.edgeSet → Bool) (k : Fin (n + 3)) : cfg ω k = ω (e k) := rfl
  have hweight (ω : G.edgeSet → Bool) :
      weight θ ω = weight (fun k => θ (e k)) (cfg ω) := by
    unfold weight
    simpa only [hcfg] using
      (e.prod_comp (fun k => if ω k then θ k else 1 - θ k)).symm
  have hpart (ω : G.edgeSet → Bool) :
      graphMode (bondGraph G ω) a (p.getVert i.val) (p.getVert j.val) =
        partition (cycleEnds n) 0 i j (cfg ω) := by
    rw [ThreeTerminalProduct.partition_graphMode,cycle_partition _ i j hi hij]
    exact bond_cycle_partition p hp hlen hedges ω i j hi hij
  funext s
  unfold bondLaw law
  simp_rw [hpart,hweight]
  exact cfg.sum_comp (fun ξ =>
    if partition (cycleEnds n) 0 i j ξ = s then weight (fun k => θ (e k)) ξ else 0)

/-- Any three distinct vertices of an actual simple cycle have exactly the law
of a triangle with three independent arc rates. The strengthened determinant
bound is stable under subsequent independent one-vertex network attachments.
All edge rates in the closed unit interval, including deterministic edges,
are retained on the original undirected graph-edge configuration cube. -/
theorem cycle_law_and_invariant {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hedges : G.edgeSet = p.edgeSet) (a b c : V)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hc : c ∈ p.support)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    ∃ u v r : ℝ, u ∈ Set.Icc 0 1 ∧ v ∈ Set.Icc 0 1 ∧ r ∈ Set.Icc 0 1 ∧
      bondLaw G a b c θ = law triangleArmsEnds 0 1 2 ![u,v,r,1,1,1] ∧
      0 ≤ delta (bondLaw G a b c θ) ∧
      delta (bondLaw G a b c θ) + bondLaw G a b c θ .all * bondLaw G a b c θ .ac ≤
        2 * bondLaw G a b c θ .ac := by
  classical
  obtain ⟨q,hq,n,hlen,hqedges,i,j,hi,hij,hbq,hcq⟩ :=
    cycle_ordered_coordinates p hp a b c ha hb hc hab hac hbc
  have hedgeq : G.edgeSet = q.edgeSet := hedges.trans hqedges.symm
  have hlaw := ordered_cycle_law q hq hlen hedgeq i j hi hij θ
  rw [hbq,hcq] at hlaw
  rw [hlaw]
  exact ThreeTerminalProduct.cycle_law_and_invariant i j hi hij
    (fun e => θ (cycleEdgeEquiv q hq hlen hedgeq e)) (fun e => hθ _)

private theorem impossible_mode_mass {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] (a b c : V) (θ : G.edgeSet → ℝ) (s : Mode)
    (h : ∀ ω, graphMode (bondGraph G ω) a b c ≠ s) :
    bondLaw G a b c θ s = 0 := by
  classical
  unfold bondLaw
  exact Finset.sum_eq_zero (fun ω _ => if_neg (h ω))

/-- If any two labelled terminals coincide, the determinant vanishes. Every
constant at least one bounds the stronger expression including the product
of the all-connected and exceptional masses. The assertion holds on any
finite-edge simple graph, without a cycle or connectivity assumption. -/
theorem coincident_terminal_invariant {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] (a b c : V) (heq : a = b ∨ a = c ∨ b = c)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1)
    (C : ℝ) (hC : 1 ≤ C) :
    0 ≤ delta (bondLaw G a b c θ) ∧
      delta (bondLaw G a b c θ) + bondLaw G a b c θ .all * bondLaw G a b c θ .ac ≤
        C * bondLaw G a b c θ .ac := by
  classical
  have hnonneg (s : Mode) : 0 ≤ bondLaw G a b c θ s := by
    unfold bondLaw
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · apply Finset.prod_nonneg
      intro e _
      split_ifs
      · exact (hθ e).1
      · exact sub_nonneg.mpr (hθ e).2
    · exact le_rfl
  have hdelta : delta (bondLaw G a b c θ) = 0 := by
    rcases heq with h | h | h
    · subst b
      have hs := impossible_mode_mass G a a c θ .separate (by
        intro ω
        by_cases hh : (bondGraph G ω).Reachable a c <;> simp [graphMode,hh])
      have hbc := impossible_mode_mass G a a c θ .bc (by
        intro ω
        by_cases hh : (bondGraph G ω).Reachable a c <;> simp [graphMode,hh])
      simp [delta,hs,hbc]
    · subst c
      have hm (ω : G.edgeSet → Bool) :
          graphMode (bondGraph G ω) a b a =
            if (bondGraph G ω).Reachable a b then Mode.all else Mode.ac := by
        by_cases hh : (bondGraph G ω).Reachable a b
        · have hh' := hh.symm
          simp [graphMode,hh,hh']
        · have hh' : ¬ (bondGraph G ω).Reachable b a := fun h => hh h.symm
          simp [graphMode,hh,hh']
      have hs := impossible_mode_mass G a b a θ .separate (by
        intro ω
        rw [hm]
        split_ifs <;> decide)
      have hab := impossible_mode_mass G a b a θ .ab (by
        intro ω
        rw [hm]
        split_ifs <;> decide)
      simp [delta,hs,hab]
    · subst c
      have hs := impossible_mode_mass G a b b θ .separate (by
        intro ω
        by_cases hh : (bondGraph G ω).Reachable a b <;> simp [graphMode,hh])
      have hab := impossible_mode_mass G a b b θ .ab (by
        intro ω
        by_cases hh : (bondGraph G ω).Reachable a b <;> simp [graphMode,hh])
      simp [delta,hs,hab]
  have hall : bondLaw G a b c θ .all ≤ 1 := by
    calc bondLaw G a b c θ .all ≤ ∑ s, bondLaw G a b c θ s :=
          Finset.single_le_sum (fun s _ => hnonneg s) (Finset.mem_univ _)
         _ = 1 := bondLaw_sum a b c θ
  rw [hdelta]
  constructor
  · exact le_rfl
  · simpa only [zero_add] using
      mul_le_mul_of_nonneg_right (hall.trans hC) (hnonneg .ac)

/-- The strengthened constant-two invariant holds for every triple of marked
vertices on an actual simple cycle, including coincident marked vertices. -/
theorem cycle_invariant {V : Type*} {G : SimpleGraph V}
    [Fintype G.edgeSet] {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    (hedges : G.edgeSet = p.edgeSet) (a b c : V)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hc : c ∈ p.support)
    (θ : G.edgeSet → ℝ) (hθ : ∀ e, θ e ∈ Set.Icc 0 1) :
    0 ≤ delta (bondLaw G a b c θ) ∧
      delta (bondLaw G a b c θ) + bondLaw G a b c θ .all * bondLaw G a b c θ .ac ≤
        2 * bondLaw G a b c θ .ac := by
  classical
  by_cases hab : a = b
  · exact coincident_terminal_invariant G a b c (Or.inl hab) θ hθ 2 (by norm_num)
  by_cases hac : a = c
  · exact coincident_terminal_invariant G a b c (Or.inr (Or.inl hac)) θ hθ 2 (by norm_num)
  by_cases hbc : b = c
  · exact coincident_terminal_invariant G a b c (Or.inr (Or.inr hbc)) θ hθ 2 (by norm_num)
  obtain ⟨u,v,r,hu,hv,hr,heq,hlo,hup⟩ :=
    cycle_law_and_invariant p hp hedges a b c ha hb hc hab hac hbc θ hθ
  exact ⟨hlo,hup⟩

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.cycle_law_and_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_law_and_invariant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.coincident_terminal_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coincident_terminal_invariant

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle.cycle_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_invariant

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCycle

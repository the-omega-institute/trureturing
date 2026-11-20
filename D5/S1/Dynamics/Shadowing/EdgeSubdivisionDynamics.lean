/- GID: D5/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/EdgeSubdivisionDynamics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Contracting inverse charts yield exactness and finite compact cells yield expansivity. -/

import D5.S1.Dynamics.Shadowing.ExactPendantObstruction
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz

open Set Function
open scoped NNReal

namespace D5.S1.Dynamics.Shadowing.EdgeSubdivisionDynamics

variable {X : Type*} [MetricSpace X] {f : X → X}

local notation "I" => Icc (0 : ℝ) 1

/-- At every depth, a contracting chart through the chosen point maps onto a whole edge. -/
theorem exists_iterate_chart {E : Type*} (chart : E → I → X)
    (hcover : ∀ x, ∃ e, x ∈ range (chart e))
    (hchart : ∀ e, LipschitzWith 1 (chart e))
    (hbranch : ∀ e (t : I), ∃ (e' : E) (h : I → I),
      t ∈ range h ∧ LipschitzWith (1 / 2) h ∧ f ∘ chart e ∘ h = chart e')
    (x : X) (n : ℕ) :
    ∃ (e : E) (g : I → X), x ∈ range g ∧
      LipschitzWith ((1 / 2) ^ n) g ∧ f^[n] ∘ g = chart e := by
  induction n with
  | zero =>
    obtain ⟨e, he⟩ := hcover x
    exact ⟨e, chart e, he, by simpa only [pow_zero] using hchart e, by simp⟩
  | succ n ih =>
    obtain ⟨e, g, ⟨t, ht⟩, hg, hiterate⟩ := ih
    obtain ⟨e', h, ⟨s, hs⟩, hh, he'⟩ := hbranch e t
    refine ⟨e', g ∘ h, ⟨s, (congrArg g hs).trans ht⟩, ?_, ?_⟩
    · simpa only [pow_succ] using hg.comp hh
    · funext u
      change f^[n.succ] (g (h u)) = chart e' u
      rw [iterate_succ_apply']
      exact (congrArg f (congrFun hiterate (h u))).trans (congrFun he' u)

/-- If every full edge covers the space in one step, shrinking branches give exactness. -/
theorem topologicallyExact_of_inverse_charts {E : Type*} (chart : E → I → X)
    (hcover : ∀ x, ∃ e, x ∈ range (chart e))
    (hchart : ∀ e, LipschitzWith 1 (chart e))
    (hbranch : ∀ e (t : I), ∃ (e' : E) (h : I → I),
      t ∈ range h ∧ LipschitzWith (1 / 2) h ∧ f ∘ chart e ∘ h = chart e')
    (honto : ∀ e, f '' range (chart e) = univ) :
    ExactPendantObstruction.TopologicallyExact f := by
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨e, g, ⟨t, ht⟩, hg, hiterate⟩ :=
    exists_iterate_chart (f := f) chart hcover hchart hbranch x n
  have hsmall : range g ⊆ U := by
    rintro _ ⟨s, rfl⟩
    apply hball
    rw [Metric.mem_ball, ← ht]
    have hst : dist s t ≤ 1 := by
      change dist (s : ℝ) (t : ℝ) ≤ 1
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]
    calc
      dist (g s) (g t) ≤ (↑((1 / 2 : ℝ≥0) ^ n) : ℝ) * 1 := hg.dist_le_mul_of_le hst
      _ = (1 / 2 : ℝ) ^ n := by
        rw [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two, mul_one]
      _ < r := hn
  refine ⟨n + 1, Nat.succ_pos n, Subset.antisymm (subset_univ _) ?_⟩
  rw [← honto e, iterate_succ', Set.image_comp]
  apply Set.image_mono
  rw [← hiterate, Set.range_comp]
  exact Set.image_mono hsmall

/-- Expansion on every intersecting pair of compact cells, including equal cells, gives a
singleton forward Bowen set at a common positive radius. -/
theorem forwardBowenBound_one_of_compact_cells {ι : Type*} [Finite ι]
    (cell : ι → Set X) (hcompact : ∀ i, IsCompact (cell i))
    (hcover : ∀ x, ∃ i, x ∈ cell i) {c : ℝ} (hc : 1 < c)
    (hexpand : ∀ i j, (cell i ∩ cell j).Nonempty →
      ∀ x ∈ cell i, ∀ y ∈ cell j, c * dist x y ≤ dist (f x) (f y)) :
    ∃ ε > 0, ForwardBowenBound f univ ε 1 := by
  classical
  letI := Fintype.ofFinite ι
  have hseparate (pairs : Finset (ι × ι)) : ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ p ∈ pairs, Disjoint (cell p.1) (cell p.2) →
        ∀ x ∈ cell p.1, ∀ y ∈ cell p.2, ε ≤ nndist x y := by
    induction pairs using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | insert p pairs _ ih =>
      obtain ⟨δ, hδ, hprev⟩ := ih
      have hpair : ∃ r : ℝ≥0, 0 < r ∧ (Disjoint (cell p.1) (cell p.2) →
          ∀ x ∈ cell p.1, ∀ y ∈ cell p.2, r ≤ nndist x y) := by
        by_cases hd : Disjoint (cell p.1) (cell p.2)
        · obtain ⟨r, hr, hgap⟩ := Metric.exists_pos_forall_lt_edist
            (hcompact p.1) (hcompact p.2).isClosed hd
          refine ⟨r, hr, fun _ x hx y hy => ?_⟩
          have hxy := hgap x hx y hy
          rw [edist_nndist, ENNReal.coe_lt_coe] at hxy
          exact hxy.le
        · exact ⟨1, zero_lt_one, fun h => (hd h).elim⟩
      obtain ⟨r, hr, hgap⟩ := hpair
      refine ⟨min r δ, lt_min hr hδ, ?_⟩
      intro q hq hd x hx y hy
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (min_le_left _ _).trans (hgap hd x hx y hy)
      · exact (min_le_right _ _).trans (hprev q hq hd x hx y hy)
  obtain ⟨ε, hε, hsep⟩ := hseparate Finset.univ
  have hnear (x y : X) (hxy : dist x y < (ε : ℝ)) : c * dist x y ≤ dist (f x) (f y) := by
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨j, hj⟩ := hcover y
    have hmeet : (cell i ∩ cell j).Nonempty := by
      apply Set.not_disjoint_iff_nonempty_inter.mp
      intro hd
      exact (not_lt_of_ge (hsep (i, j) (Finset.mem_univ _) hd x hi y hj)) (dist_lt_coe.mp hxy)
    exact hexpand i j hmeet x hi y hj
  refine ⟨(ε : ℝ), NNReal.coe_pos.mpr hε, fun x _ => ?_⟩
  change (univ ∩ ForwardBowen f (ε : ℝ) x).encard ≤ 1
  rw [← Set.encard_singleton x]
  apply Set.encard_mono
  intro y hy
  apply Set.mem_singleton_iff.mpr
  have hgrowth (n : ℕ) : c ^ n * dist x y ≤ dist (f^[n] x) (f^[n] y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, iterate_succ_apply', iterate_succ_apply']
      exact (mul_le_mul_of_nonneg_left ih (zero_lt_one.trans hc).le).trans
        (hnear _ _ (hy.2 n))
  by_contra hne
  have hd : 0 < dist x y := dist_pos.mpr (Ne.symm hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((ε : ℝ) / dist x y) hc
  exact (not_lt_of_ge (hgrowth n)) ((hy.2 n).trans ((div_lt_iff₀ hd).mp hn))

end D5.S1.Dynamics.Shadowing.EdgeSubdivisionDynamics

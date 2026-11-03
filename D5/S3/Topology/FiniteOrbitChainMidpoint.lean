/- GID: D5/S3/Topology/FiniteOrbitChainMidpoint
   generality: G
   mirror-B: D5/B/S3/Topology/FiniteOrbitChainMidpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Topology.Order.Compact, mathlib/module/Mathlib.Topology.Instances.ENNReal.Lemmas]
   utility: none
   digest: Original finite-cost chains admit prescribed-cost cuts and compact chain quotients admit exact midpoints. -/

import D5.S3.Topology.FiniteOrbitChainMetric
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

open Set
open D5.S3.Topology.FiniteOrbitChainMetric.Datum
open scoped NNReal ENNReal Topology

namespace D5.S3.Topology.FiniteOrbitChainMidpoint

universe u v w z

variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)] (G : FiniteOrbitChainMetric.Datum I J X)
variable {Y : Type z} [EMetricSpace Y] (q : Sigma X → Y)

/-- Every finite-cost original chain can be cut at any prescribed paid cost.
The two resulting distance bounds use the original target distance. -/
theorem original_chain_cut
    (hq : ∀ a b, edist (q a) (q b) = G.distance a b)
    (hseg : ∀ (i : I) (x y : X i) (s : ℝ≥0∞),
      edist x y < ⊤ → s ≤ edist x y →
      ∃ z : X i, edist x z ≤ s ∧ edist z y ≤ edist x y - s)
    {a b : Sigma X} {c : ℝ≥0∞} (h : G.Chain a b c)
    (hc : c < ⊤) (s : ℝ≥0∞) (hs : s ≤ c) :
    ∃ z : Y, edist (q a) z ≤ s ∧ edist z (q b) ≤ c - s := by
  have bound {a b : Sigma X} {c : ℝ≥0∞} (h : G.Chain a b c) :
      edist (q a) (q b) ≤ c := by
    rw [hq]
    exact iInf₂_le c h
  have piece_bound (i : I) (x y : X i) :
      edist (q ⟨i, x⟩) (q ⟨i, y⟩) ≤ edist x y := by
    apply bound
    simpa only [zero_add] using Chain.move x y (Chain.nil (G := G))
  induction h generalizing s with
  | nil =>
      have hs0 : s = 0 := le_antisymm hs bot_le
      subst s
      exact ⟨q a, by simp, by simp⟩
  | @move i x y c h ih =>
      have hc' : c < ⊤ := le_self_add.trans_lt hc
      have hxy : edist x y < ⊤ := le_add_self.trans_lt hc
      by_cases hsc : s ≤ c
      · obtain ⟨z, haz, hzx⟩ := ih hc' s hsc
        refine ⟨z, haz, ?_⟩
        calc
          edist z (q ⟨i, y⟩) ≤
              edist z (q ⟨i, x⟩) + edist (q ⟨i, x⟩) (q ⟨i, y⟩) :=
            edist_triangle _ _ _
          _ ≤ (c - s) + edist x y := add_le_add hzx (piece_bound i x y)
          _ = (c + edist x y) - s :=
            ENNReal.sub_add_eq_add_sub hsc (hs.trans_lt hc).ne
      · have hcs : c ≤ s := (lt_of_not_ge hsc).le
        have hcut : s - c ≤ edist x y := tsub_le_iff_left.mpr hs
        obtain ⟨z, hxz, hzy⟩ := hseg i x y (s - c) hxy hcut
        have hsum : c + (s - c) = s := add_tsub_cancel_of_le hcs
        have hrem : edist x y - (s - c) = (c + edist x y) - s := by
          conv_rhs => rw [← hsum]
          exact (ENNReal.add_sub_add_eq_sub_left hc'.ne).symm
        refine ⟨q ⟨i, z⟩, ?_, ?_⟩
        · calc
            edist (q a) (q ⟨i, z⟩) ≤
                edist (q a) (q ⟨i, x⟩) + edist (q ⟨i, x⟩) (q ⟨i, z⟩) :=
              edist_triangle _ _ _
            _ ≤ c + (s - c) := add_le_add (bound h) ((piece_bound i x z).trans hxz)
            _ = s := hsum
        · exact ((piece_bound i z y).trans hzy).trans_eq hrem
  | @forward j x c h ih =>
      have heq : q ⟨G.src j, x.val⟩ = q ⟨G.dst j, (G.iso j x).val⟩ := by
        apply edist_eq_zero.mp
        exact le_antisymm (bound (Chain.forward j x (Chain.nil (G := G)))) bot_le
      simpa only [← heq] using ih hc s hs
  | @backward j x c h ih =>
      have heq : q ⟨G.dst j, x.val⟩ = q ⟨G.src j, ((G.iso j).symm x).val⟩ := by
        apply edist_eq_zero.mp
        exact le_antisymm (bound (Chain.backward j x (Chain.nil (G := G)))) bot_le
      simpa only [← heq] using ih hc s hs

/-- The infimum over original chains supplies approximate midpoints without
requiring a minimizing chain or a bound on the number of seam crossings. -/
private theorem original_chain_approximate_midpoint
    (hq : ∀ a b, edist (q a) (q b) = G.distance a b)
    (hseg : ∀ (i : I) (x y : X i) (s : ℝ≥0∞),
      edist x y < ⊤ → s ≤ edist x y →
      ∃ z : X i, edist x z ≤ s ∧ edist z y ≤ edist x y - s)
    (a b : Sigma X) (hfinite : G.distance a b < ⊤)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ z : Y, edist (q a) z ≤ G.distance a b / 2 + ε ∧
      edist z (q b) ≤ G.distance a b / 2 + ε := by
  have hlt : (⨅ (c : ℝ≥0∞) (_ : G.Chain a b c), c) < G.distance a b + ε :=
    ENNReal.lt_add_right hfinite.ne (ENNReal.coe_pos.mpr hε).ne'
  simp only [iInf_lt_iff, exists_prop] at hlt
  obtain ⟨c, hc, hcost⟩ := hlt
  have hctop : c < ⊤ := hcost.trans (ENNReal.add_lt_top.mpr ⟨hfinite, ENNReal.coe_lt_top⟩)
  obtain ⟨z, haz, hzb⟩ :=
    original_chain_cut G q hq hseg hc hctop (c / 2) ENNReal.half_le_self
  have hhalf : c / 2 ≤ G.distance a b / 2 + ε := by
    calc
      c / 2 ≤ (G.distance a b + ε) / 2 := ENNReal.div_le_div_right hcost.le 2
      _ = G.distance a b / 2 + (ε : ℝ≥0∞) / 2 := ENNReal.add_div
      _ ≤ G.distance a b / 2 + ε := add_le_add le_rfl ENNReal.half_le_self
  exact ⟨z, haz.trans hhalf, (hzb.trans_eq (ENNReal.sub_half hctop.ne)).trans hhalf⟩

end D5.S3.Topology.FiniteOrbitChainMidpoint

namespace D5.S3.Topology.FiniteOrbitChainMidpoint

universe u

variable {Y : Type u} [EMetricSpace Y] [CompactSpace Y]

/-- Compactness attains the limiting midpoint error while allowing infinite
distances to points outside the finite-distance component. -/
private theorem exists_midpoint_of_approximate (a b : Y)
    (happrox : ∀ ε : ℝ≥0, 0 < ε →
      ∃ z : Y, edist a z ≤ edist a b / 2 + ε ∧
        edist z b ≤ edist a b / 2 + ε) :
    ∃ m : Y, edist a m ≤ edist a b / 2 ∧ edist m b ≤ edist a b / 2 := by
  let f : Y → ℝ≥0∞ := fun z => max (edist a z) (edist z b)
  have hf : Continuous f := by
    exact (continuous_const.edist continuous_id).max (continuous_id.edist continuous_const)
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_isMinOn ⟨a, mem_univ a⟩ hf.continuousOn
  have hmin : f m ≤ edist a b / 2 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨z, haz, hzb⟩ := happrox ε hε
    exact (hm (mem_univ z)).trans (max_le haz hzb)
  exact ⟨m, (le_max_left _ _).trans hmin, (le_max_right _ _).trans hmin⟩

end D5.S3.Topology.FiniteOrbitChainMidpoint

namespace D5.S3.Topology.FiniteOrbitChainMidpoint

universe u v w z

variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)] (G : FiniteOrbitChainMetric.Datum I J X)
variable {Y : Type z} [EMetricSpace Y] [CompactSpace Y] (q : Sigma X → Y)

/-- A compact target carrying exactly the original chain distance has exact
midpoints between images at finite distance. -/
private theorem original_chain_midpoint
    (hq : ∀ a b, edist (q a) (q b) = G.distance a b)
    (hseg : ∀ (i : I) (x y : X i) (s : ℝ≥0∞),
      edist x y < ⊤ → s ≤ edist x y →
      ∃ z : X i, edist x z ≤ s ∧ edist z y ≤ edist x y - s)
    (a b : Sigma X) (hfinite : G.distance a b < ⊤) :
    ∃ m : Y, edist (q a) m ≤ G.distance a b / 2 ∧
      edist m (q b) ≤ G.distance a b / 2 := by
  have happ := original_chain_approximate_midpoint G q hq hseg a b hfinite
  have hm := exists_midpoint_of_approximate (q a) (q b) (by
    simpa only [hq] using happ)
  simpa only [hq] using hm

end D5.S3.Topology.FiniteOrbitChainMidpoint

namespace D5.S3.Topology.FiniteOrbitChainMidpoint

universe u v w
variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)]

/-- Compact pieces with finite actual gluing orbits give exact finite-distance
midpoints in the literal original quotient, with its original chain distance. -/
theorem compact_original_quotient_midpoints
    [Fintype I] [Fintype J] [∀ i, CompactSpace (X i)]
    (G : FiniteOrbitChainMetric.Datum I J X)
    (hf : ∀ a : Sigma X, Set.Finite {b : Sigma X | G.Rel a b})
    (hseg : ∀ (i : I) (x y : X i) (s : ℝ≥0∞),
      edist x y < ⊤ → s ≤ edist x y →
      ∃ z : X i, edist x z ≤ s ∧ edist z y ≤ edist x y - s) :
    let S := Relation.EqvGen.setoid G.Step
    let Q := Quotient S
    let τ : TopologicalSpace Q := inferInstance
    ∃ m : EMetricSpace Q,
      m.toUniformSpace.toTopologicalSpace = τ ∧
      (∀ a b : Sigma X,
        @edist Q m.toEDist (Quotient.mk S a) (Quotient.mk S b) = G.distance a b) ∧
      (letI : EMetricSpace Q := m
       ∀ a b : Q, edist a b < ⊤ →
         ∃ z : Q, edist a z = edist a b / 2 ∧ edist z b = edist a b / 2) := by
  let S := Relation.EqvGen.setoid G.Step
  let Q := Quotient S
  obtain ⟨m, htop, hdist, _, _, _⟩ := G.chain_metric_on_original_quotient hf
  refine ⟨m, htop, hdist, ?_⟩
  have hc : @CompactSpace Q m.toUniformSpace.toTopologicalSpace := by
    rw [htop]
    infer_instance
  letI : TopologicalSpace Q := m.toUniformSpace.toTopologicalSpace
  letI : EMetricSpace Q := m
  letI : CompactSpace Q := hc
  let q : Sigma X → Q := Quotient.mk S
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  have hfin : G.distance a b < ⊤ := by
    simpa only [hdist a b] using hab
  obtain ⟨z, haz, hzb⟩ := original_chain_midpoint G q hdist hseg a b hfin
  rw [← hdist a b] at haz hzb
  refine ⟨z, le_antisymm haz ?_, le_antisymm hzb ?_⟩
  · have hlow : edist (q a) (q b) - edist (q a) (q b) / 2 ≤ edist (q a) z :=
      tsub_le_iff_right.mpr ((edist_triangle (q a) z (q b)).trans
        (add_le_add le_rfl hzb))
    rwa [ENNReal.sub_half hab.ne] at hlow
  · have hlow : edist (q a) (q b) - edist (q a) (q b) / 2 ≤ edist z (q b) :=
      tsub_le_iff_left.mpr ((edist_triangle (q a) z (q b)).trans
        (add_le_add haz le_rfl))
    rwa [ENNReal.sub_half hab.ne] at hlow

end D5.S3.Topology.FiniteOrbitChainMidpoint

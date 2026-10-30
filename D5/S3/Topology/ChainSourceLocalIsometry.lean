/- GID: D5/S3/Topology/ChainSourceLocalIsometry
   generality: G
   mirror-B: D5/B/S3/Topology/ChainSourceLocalIsometry
   mirror-E: none(waiver:arbitrary-original-chain-locality)
   anchors: [mathlib/module/Mathlib.Topology.MetricSpace.Isometry]
   utility: none
   digest: A generator-free open source region contains a ball that is isometric in the original chain quotient. -/

import D5.S3.Topology.FiniteOrbitChainMetric
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Small source balls disjoint from the gluing faces preserve all pairwise distances. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal NNReal Topology

namespace D5.S3.Topology.ChainSourceLocalIsometry

universe u v w z
variable {I : Type u} {J : Type v} {X : I → Type w}
variable [∀ i, EMetricSpace (X i)]
variable (G : FiniteOrbitChainMetric.Datum I J X)

private theorem chain_confined {i : I} (a x : X i) (r : ℝ≥0∞)
    (U : Set (Sigma X))
    (hball : Metric.eball a (r + r + r) ⊆ Sigma.mk i ⁻¹' U)
    (hsource : ∀ j (y : G.dom j), (⟨G.src j, y.val⟩ : Sigma X) ∉ U)
    (htarget : ∀ j (y : G.ran j), (⟨G.dst j, y.val⟩ : Sigma X) ∉ U)
    (hx : edist a x < r) {b : Sigma X} {c : ℝ≥0∞}
    (h : G.Chain ⟨i,x⟩ b c) (hc : c < r + r) :
    ∃ y : X i, b = ⟨i,y⟩ ∧ edist x y ≤ c := by
  induction h with
  | nil => exact ⟨x, rfl, by simp⟩
  | @move k y z c h ih =>
      have hc' : c < r + r := le_self_add.trans_lt hc
      obtain ⟨y', heq, hxy⟩ := ih hc'
      have hki : k = i := congrArg Sigma.fst heq
      subst k
      have hyy : y = y' := sigma_mk_injective heq
      subst y'
      exact ⟨z, rfl, (edist_triangle x y z).trans (add_le_add hxy le_rfl)⟩
  | @forward j y c h ih =>
      obtain ⟨y', heq, hxy⟩ := ih hc
      have hnear : edist a y' < r + r + r := by
        apply (edist_triangle a x y').trans_lt
        apply (add_le_add le_rfl hxy).trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx hc
      have hyU : (⟨G.src j, y.val⟩ : Sigma X) ∈ U := by
        rw [heq]
        exact hball (by simpa only [Metric.mem_eball, edist_comm] using hnear)
      exact False.elim (hsource j y hyU)
  | @backward j y c h ih =>
      obtain ⟨y', heq, hxy⟩ := ih hc
      have hnear : edist a y' < r + r + r := by
        apply (edist_triangle a x y').trans_lt
        apply (add_le_add le_rfl hxy).trans_lt
        simpa only [add_assoc] using ENNReal.add_lt_add hx hc
      have hyU : (⟨G.dst j, y.val⟩ : Sigma X) ∈ U := by
        rw [heq]
        exact hball (by simpa only [Metric.mem_eball, edist_comm] using hnear)
      exact False.elim (htarget j y hyU)

/-- The original chain metric preserves all pairwise distances on a small
source ball in an open region disjoint from every gluing source and target. -/
theorem original_chain_local_source_isometry
    {Y : Type z} [EMetricSpace Y] (q : Sigma X → Y)
    (hq : ∀ a b, edist (q a) (q b) = G.distance a b)
    (U : Set (Sigma X)) (hU : IsOpen U)
    (hsource : ∀ j (y : G.dom j), (⟨G.src j, y.val⟩ : Sigma X) ∉ U)
    (htarget : ∀ j (y : G.ran j), (⟨G.dst j, y.val⟩ : Sigma X) ∉ U)
    (a : Sigma X) (ha : a ∈ U) :
    ∃ r : ℝ≥0, 0 < r ∧
      Isometry (fun x : Metric.eball a.2 (r : ℝ≥0∞) => q ⟨a.1,x.val⟩) := by
  obtain ⟨ε, hε, hεU⟩ :=
    EMetric.isOpen_iff.mp (isOpen_sigma_iff.mp hU a.1) a.2 ha
  obtain ⟨R, hR, hRε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hRpos : 0 < R := by exact_mod_cast hR
  let r : ℝ≥0 := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h3r : r + r + r < R := by
    have hp : (0 : ℝ) < R := by exact_mod_cast hRpos
    have hs : (R : ℝ) / 4 + R / 4 + R / 4 < R := by linarith
    exact_mod_cast hs
  have hsmall : (r : ℝ≥0∞) + r + r < ε := by
    simpa only [ENNReal.coe_add] using (ENNReal.coe_lt_coe.mpr h3r).trans hRε
  have hball : Metric.eball a.2 ((r : ℝ≥0∞) + r + r) ⊆
      Sigma.mk a.1 ⁻¹' U := by
    intro x hx
    exact hεU (hx.trans hsmall)
  refine ⟨r, hr, ?_⟩
  intro x y
  change edist (q ⟨a.1,x.val⟩) (q ⟨a.1,y.val⟩) = edist x.val y.val
  rw [hq]
  have hx : edist a.2 x.val < (r : ℝ≥0∞) := by
    simpa only [Metric.mem_eball, edist_comm] using x.property
  have hy : edist a.2 y.val < (r : ℝ≥0∞) := by
    simpa only [Metric.mem_eball, edist_comm] using y.property
  have hxy : edist x.val y.val < (r : ℝ≥0∞) + r := by
    apply (edist_triangle x.val a.2 y.val).trans_lt
    simpa only [edist_comm] using ENNReal.add_lt_add hx hy
  apply le_antisymm
  · have one : G.Chain ⟨a.1,x.val⟩ ⟨a.1,y.val⟩ (edist x.val y.val) := by
      simpa only [zero_add] using
        (FiniteOrbitChainMetric.Datum.Chain.move x.val y.val
          (FiniteOrbitChainMetric.Datum.Chain.nil (G := G)))
    exact iInf₂_le _ one
  · apply le_iInf₂
    intro c hc
    by_contra hnot
    have hshort : c < edist x.val y.val := lt_of_not_ge hnot
    obtain ⟨y', heq, hbound⟩ := chain_confined G a.2 x.val r U hball
      hsource htarget hx hc (hshort.trans hxy)
    have hy' : y.val = y' := sigma_mk_injective heq
    subst y'
    exact (not_lt_of_ge hbound) hshort

#print axioms original_chain_local_source_isometry

end D5.S3.Topology.ChainSourceLocalIsometry

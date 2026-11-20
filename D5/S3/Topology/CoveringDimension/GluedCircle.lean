/- GID: D5/S3/Topology/CoveringDimension/GluedCircle
   generality: I
   mirror-B: D5/B/S3/Topology/CoveringDimension/GluedCircle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite graph sheets over a circle have covering dimension at most one. -/

import D5.S1.Dynamics.Shadowing.CantorCircleExpansivity
import D5.S3.Topology.CoveringDimension.FiniteFrontier
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Covering dimension of glued circle sheets

Projection to the unit additive circle bounds the dimension of finite graph
sheets. Connectedness and nontriviality give equality for the Cantor gluing.
-/

open Set
open D5.S1.Dynamics.Shadowing.InvarianceGluedSheets

namespace D5.S3.Topology.CoveringDimension

private theorem finite_circle_sphere (x : UnitAddCircle) (r : ℝ) :
    (Metric.sphere x r).Finite := by
  apply (Finite.insert (x + (r : UnitAddCircle))
    (finite_singleton (x + ((-r : ℝ) : UnitAddCircle)))).subset
  intro y hy
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (y - x)
  change (t : UnitAddCircle) = y - x at ht
  have hr := Metric.mem_sphere.mp hy
  rw [dist_eq_norm, ← ht, UnitAddCircle.norm_eq] at hr
  have hz : (((round t : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round t, by simp [zsmul_eq_mul]⟩
  have hcenter : ((t - (round t : ℝ) : ℝ) : UnitAddCircle) = y - x := by
    rw [AddCircle.coe_sub, hz, sub_zero, ht]
  by_cases hpos : 0 ≤ t - (round t : ℝ)
  · rw [abs_of_nonneg hpos] at hr
    rw [hr] at hcenter
    apply mem_insert_iff.mpr
    exact Or.inl (by rw [hcenter]; abel)
  · rw [abs_of_neg (lt_of_not_ge hpos)] at hr
    have hn : t - (round t : ℝ) = -r := by linarith
    rw [hn] at hcenter
    exact mem_insert_of_mem _ (mem_singleton_iff.mpr (by rw [hcenter]; abel))

/-- Every metric ball in the unit additive circle has a frontier of at most
two points, giving finite open refinements of multiplicity at most two. -/
theorem atMost_one_unitAddCircle : AtMost UnitAddCircle 1 := by
  apply atMost_one_of_finiteFrontier
  intro x u hu hx
  obtain ⟨r, hr, hSub⟩ := Metric.isOpen_iff.mp hu x hx
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hSub,
    (finite_circle_sphere x r).subset Metric.frontier_ball_subset_sphere⟩

/-- Every finite union of continuous graph sheets over the circle admits a
finite open refinement of multiplicity at most two. -/
theorem atMost_one_gluedCircle {N : ℕ} {ρ : UnitAddCircle → ℝ}
    (hρ : Continuous ρ) : AtMost (Space N ρ) 1 := by
  let _ : CompactSpace (Space N ρ) := compactSpace_space hρ
  let f : Space N ρ → UnitAddCircle := fun p => p.val.1
  have hf : Continuous f := continuous_fst.comp continuous_subtype_val
  apply atMost_of_closedMap_finiteFibers hf hf.isClosedMap _ atMost_one_unitAddCircle
  intro y
  apply (finite_range (fun i : Fin N => lift ρ i y)).subset
  intro p hp
  have hp₁ : p.val.1 = y := mem_singleton_iff.mp hp
  obtain ⟨i, hi⟩ := p.property
  refine ⟨i, Subtype.ext (Prod.ext hp₁.symm ?_)⟩
  change (i.val : ℝ) * ρ y = p.val.2
  rw [← hp₁]
  exact hi.symm

open D5.S1.Dynamics.Shadowing in
/-- Gluing circles along the image of the ternary Cantor set gives a compact,
connected space of covering dimension exactly one and a continuous surjection
whose least finite positive expansivity order is the number of sheets. -/
theorem cantorCircle_exactOrder_oneDimensional {N : ℕ} (hN : 2 ≤ N) :
    CompactSpace (CantorCircleExpansivity.Space N) ∧
      ConnectedSpace (CantorCircleExpansivity.Space N) ∧
      AtMost (CantorCircleExpansivity.Space N) 1 ∧
      ¬ AtMost (CantorCircleExpansivity.Space N) 0 ∧
      Continuous (CantorCircleExpansivity.sheetMap N) ∧
      Function.Surjective (CantorCircleExpansivity.sheetMap N) ∧
      (∃ ε > 0, ForwardBowenBound (CantorCircleExpansivity.sheetMap N) univ ε N) ∧
      (∀ ε > 0, ¬ ForwardBowenBound (CantorCircleExpansivity.sheetMap N) univ ε (N - 1)) := by
  obtain ⟨hCompact, hConnected, hContinuous, hOnto, hUpper, hLower⟩ :=
    CantorCircleExpansivity.exact_order hN
  let _ : ConnectedSpace (CantorCircleExpansivity.Space N) := hConnected
  let i : Fin N := ⟨0, by omega⟩
  let ρ (y : UnitAddCircle) := Metric.infDist y CantorCircleExpansivity.cantorCircle
  have hDistinct : (0 : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    intro hz
    have hnorm := AddCircle.norm_half_period_eq (1 : ℝ)
    rw [← hz, norm_zero] at hnorm
    norm_num at hnorm
  let _ : Nontrivial (CantorCircleExpansivity.Space N) :=
    ⟨⟨lift ρ i 0, lift ρ i ((1 / 2 : ℝ) : UnitAddCircle),
      fun he => hDistinct (congrArg (fun p : CantorCircleExpansivity.Space N => p.val.1) he)⟩⟩
  exact ⟨hCompact, hConnected, atMost_one_gluedCircle (Metric.continuous_infDist_pt _),
    not_atMost_zero, hContinuous, hOnto, hUpper, hLower⟩

end D5.S3.Topology.CoveringDimension

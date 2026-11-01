/- GID: D5/S3/Topology/BorsukUlam/PlanarOddMapZero
   generality: G
   mirror-B: D5/B/S3/Topology/BorsukUlam/PlanarOddMapZero
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every continuous odd map from the two-sphere to the plane has a zero. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-! The planar Borsuk--Ulam route used by the chiral-event settlement. -/

set_option autoImplicit false

open scoped EuclideanSpace

noncomputable section

namespace D5.S3.Topology.BorsukUlam.PlanarOddMapZero

private def hemisphere (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z.re, z.im, Real.sqrt (1 - ‖z‖ ^ 2)]

private theorem hemisphere_continuous : Continuous hemisphere := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

private theorem hemisphere_mem (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    hemisphere z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hzle : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hs : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hnorm := EuclideanSpace.real_norm_sq_eq (hemisphere z)
  have hzsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  rw [Fin.sum_univ_three] at hnorm
  change ‖hemisphere z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 +
    (Real.sqrt (1 - ‖z‖ ^ 2)) ^ 2 at hnorm
  rw [Real.sq_sqrt hs, hzsq] at hnorm
  apply mem_sphere_zero_iff_norm.mpr
  nlinarith [norm_nonneg (hemisphere z)]

private def diskBoundary (z : Circle) : Metric.closedBall (0 : ℂ) 1 :=
  ⟨z, mem_closedBall_zero_iff.mpr (le_of_eq (Circle.norm_coe z))⟩

private theorem diskBoundary_continuous : Continuous diskBoundary :=
  continuous_subtype_val.subtype_mk _

private theorem hemisphere_boundary_neg (z : Circle) :
    hemisphere (diskBoundary (-z)) = -hemisphere (diskBoundary z) := by
  ext i
  fin_cases i <;> simp [hemisphere, diskBoundary, Circle.norm_coe]

/-- The planar Borsuk--Ulam theorem in the form used by the chiral-event argument. -/
theorem planar_odd_map_zero (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ContinuousOn f (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (hodd : ∀ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f (-v) = -f v) :
    ∃ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f v = 0 := by
  by_contra hn
  have hne : ∀ v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, f v ≠ 0 := by
    simpa only [not_exists, not_and] using hn
  let D := Metric.closedBall (0 : ℂ) 1
  have hconv : Convex ℝ D := convex_closedBall 0 1
  let : ContractibleSpace D := hconv.contractibleSpace ⟨0, by simp [D]⟩
  let : LocallyPathConnectedSpace D := hconv.locallyPathConnectedSpace
  let q : D → ℂ := fun z => f (hemisphere z)
  have hq : Continuous q := hf.comp_continuous
    (hemisphere_continuous.comp continuous_subtype_val) (fun z => hemisphere_mem z z.property)
  have hqne : ∀ z : D, q z ≠ 0 := fun z => hne _ (hemisphere_mem z z.property)
  let g : C(D, Circle) :=
    ⟨fun z => ⟨q z / (‖q z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr (hqne z))])⟩,
      (hq.div (Complex.continuous_ofReal.comp hq.norm)
        (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hqne z)))).subtype_mk _⟩
  let d₀ : D := ⟨0, by simp [D]⟩
  obtain ⟨r₀, hr₀⟩ := Circle.exp_surjective (g d₀)
  obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g d₀ r₀ hr₀
  let l : Circle → ℝ := fun z => F (diskBoundary z)
  have hl : Continuous l := F.continuous.comp diskBoundary_continuous
  have hlift (z : Circle) : Circle.exp (l z) = g (diskBoundary z) :=
    congrFun hF.2 (diskBoundary z)
  have hgodd (z : Circle) : g (diskBoundary (-z)) = -g (diskBoundary z) := by
    apply Circle.ext
    change q (diskBoundary (-z)) / (‖q (diskBoundary (-z))‖ : ℂ) =
      -(q (diskBoundary z) / (‖q (diskBoundary z)‖ : ℂ))
    have hqodd : q (diskBoundary (-z)) = -q (diskBoundary z) := by
      exact (congrArg f (hemisphere_boundary_neg z)).trans
        (hodd _ (hemisphere_mem _ (diskBoundary z).property))
    rw [hqodd, norm_neg, neg_div]
  let delta : Circle → ℝ := fun z => l (-z) - l z
  have hdelta : Continuous delta := (hl.comp continuous_neg).sub hl
  have hexp (z : Circle) : Circle.exp (delta z) = -1 := by
    change Circle.exp (l (-z) - l z) = -1
    rw [Circle.exp_sub, hlift, hlift, hgodd, neg_div, div_self']
  have hc : delta (-1) = delta 1 := Circle.isCoveringMap_exp.const_of_comp hdelta
    (fun z w => (hexp z).trans (hexp w).symm) (-1) 1
  have hz : delta 1 = 0 := by
    dsimp [delta] at hc ⊢
    simp only [neg_neg] at hc
    linarith
  have hh := hexp 1
  rw [hz, Circle.exp_zero] at hh
  have : (1 : ℂ) = -1 := congrArg (fun z : Circle => (z : ℂ)) hh
  norm_num at this

end D5.S3.Topology.BorsukUlam.PlanarOddMapZero

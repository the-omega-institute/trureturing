/- GID: D5/S3/Weil/ZetaLinear/FiniteIndexHorizonExclusion
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/FiniteIndexHorizonExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A uniform finite inclusion-index bound excludes noncritical zeta zeros. -/

import D5.S3.Weil.Pick.HorizonEffectiveIndex
import D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening
import D5.S3.Weil.ZetaSeam.ZetaReflect
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Searches of D5 for finite-index horizon exclusion, uniform horizon-index
     bounds, and critical-line zero conclusions found no equivalent theorem.
     `Pick.HorizonEffectiveIndex.singularFactor_tendsto_atTop` supplies the
     boundary divergence, while `ZetaSeam.ZetaReflect.zeta_reflect_zero`
     supplies reflection of nontrivial zeros. Neither combines the public
     inclusion-index hypotheses into the exclusion conclusion.
   * Pinned Mathlib searches found no exact exclusion theorem. The proof uses
     `Tendsto.eventually_gt_atTop`, `Eventually.exists`, and elementary real
     inequalities from the pinned library.
   * Searches of the installed non-Mathlib Lean packages for horizon index,
     inclusion-index bounds, and zeta-zero exclusion returned no hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix

namespace D5.S3.Weil.ZetaLinear.FiniteIndexHorizonExclusion

open Filter Set Topology
open D5.S3.Weil.Convention
open D5.S3.Weil.Pick.HorizonEffectiveIndex
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/-- If every positive observation depth below the critical abscissa has a
uniformly bounded inclusion index, and that index controls the canonical
rank-one horizon index produced by every right-side nontrivial zero, then all
nontrivial zeros lie on the critical line. Reflection excludes the left side
after the horizon divergence excludes the right side. -/
theorem finite_index_horizon_exclusion
    (inclusionIndex : ℝ → ℝ) (bound : ℝ)
    (inclusionIndexBound :
      ∀ omega : ℝ, 0 < omega → omega < criticalAbscissa →
        inclusionIndex omega ≤ bound)
    (horizonIndexControlled :
      ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
        criticalAbscissa < rho.re →
        ∀ omega : ℝ, 0 < omega → omega < criticalDisplacement rho →
          horizonEffectiveIndex
              (!![omega / criticalDisplacement rho] : Matrix (Fin 1) (Fin 1) ℝ) ≤
            inclusionIndex omega) :
    ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
      rho.re = criticalAbscissa := by
  have excludeRight :
      ∀ rho : ℂ, Zeta23.IsNontrivialZero rho →
        criticalAbscissa < rho.re → False := by
    intro rho hrho hright
    have hdeltaPos : 0 < criticalDisplacement rho := by
      simpa only [criticalDisplacement] using sub_pos.mpr hright
    have hdeltaLt : criticalDisplacement rho < criticalAbscissa := by
      rcases hrho with ⟨_, _, hrhoReLt⟩
      simp only [criticalDisplacement]
      norm_num [criticalAbscissa] at hright hrhoReLt ⊢
      linarith
    have hlarge :
        ∀ᶠ sigma : ℝ in nhdsWithin 1 (Iio 1),
          bound < (1 - sigma ^ 2)⁻¹ :=
      singularFactor_tendsto_atTop.eventually_gt_atTop bound
    have hinterior :
        ∀ᶠ sigma : ℝ in nhdsWithin 1 (Iio 1), sigma ∈ Ioo 0 1 :=
      Ioo_mem_nhdsLT (by norm_num)
    rcases (hlarge.and hinterior).exists with ⟨sigma, hsigmaLarge, hsigma⟩
    let omega := sigma * criticalDisplacement rho
    have homegaPos : 0 < omega := by
      dsimp only [omega]
      exact mul_pos hsigma.1 hdeltaPos
    have homegaLtDelta : omega < criticalDisplacement rho := by
      dsimp only [omega]
      exact (mul_lt_iff_lt_one_left hdeltaPos).mpr hsigma.2
    have homegaLtCritical : omega < criticalAbscissa :=
      homegaLtDelta.trans hdeltaLt
    have hsigmaEq : omega / criticalDisplacement rho = sigma := by
      dsimp only [omega]
      field_simp
    have hcontrolled := horizonIndexControlled rho hrho hright omega
      homegaPos homegaLtDelta
    have hbounded := inclusionIndexBound omega homegaPos homegaLtCritical
    rw [hsigmaEq] at hcontrolled
    have hindexFormula :
        horizonEffectiveIndex
            (!![sigma] : Matrix (Fin 1) (Fin 1) ℝ) =
          (1 - sigma ^ 2)⁻¹ := by
      simp [horizonEffectiveIndex, horizonDefect, Matrix.mul_apply]
      ring
    rw [hindexFormula] at hcontrolled
    linarith
  intro rho hrho
  by_contra hoffLine
  have hside : rho.re < criticalAbscissa ∨ criticalAbscissa < rho.re :=
    lt_or_gt_of_ne hoffLine
  rcases hside with hleft | hright
  · have hreflected := Zeta23.zeta_reflect_zero rho hrho
    have hreflectedRight : criticalAbscissa < (Zeta23.reflect rho).re := by
      simp only [Zeta23.reflect]
      norm_num [criticalAbscissa] at hleft ⊢
      linarith
    exact excludeRight (Zeta23.reflect rho) hreflected hreflectedRight
  · exact excludeRight rho hrho hright

#print axioms finite_index_horizon_exclusion

end D5.S3.Weil.ZetaLinear.FiniteIndexHorizonExclusion

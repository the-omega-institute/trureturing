/- GID: D5/S3/Zeros/Symmetry/CriticalDampingFlatness
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/CriticalDampingFlatness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Vanishing finite damping defect characterizes critical rates at every nonzero scale. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace D5.S3.Zeros.Symmetry.CriticalDampingFlatness

/-- The nonnegative finite defect obtained by centering each damping rate at one half. -/
noncomputable def criticalDampingDefect {Zero : Type*} [Fintype Zero]
    (realPart : Zero → ℝ) (tau : ℝ) : ℝ :=
  ∑ rho, (Real.cosh (tau * (realPart rho - 1 / 2)) - 1)

/-- At every nonzero scale, the finite damping defect vanishes exactly when every rate is
critical. Multiplicity is represented by the finite index type. -/
theorem critical_damping_flatness_criterion {Zero : Type*} [Fintype Zero]
    (realPart : Zero → ℝ) (tau : ℝ) (htau : tau ≠ 0) :
    (∀ rho, realPart rho = 1 / 2) ↔ criticalDampingDefect realPart tau = 0 := by
  constructor
  · intro hcritical
    simp [criticalDampingDefect, hcritical]
  · intro hdefect rho
    have hterms :
        ∀ index : Zero, Real.cosh (tau * (realPart index - 1 / 2)) - 1 = 0 := by
      rw [criticalDampingDefect, Fintype.sum_eq_zero_iff_of_nonneg] at hdefect
      · exact fun index => congrFun hdefect index
      · intro index
        exact sub_nonneg.mpr (Real.one_le_cosh _)
    have hproduct : tau * (realPart rho - 1 / 2) = 0 := by
      by_contra hne
      have hstrict := Real.one_lt_cosh.mpr hne
      linarith [hterms rho]
    rcases mul_eq_zero.mp hproduct with htauZero | hcentered
    · exact (htau htauZero).elim
    · exact sub_eq_zero.mp hcentered

/-- The finite source carrier is inhabited. -/
example : Type := Fin 1

/-- The nonzero-scale hypothesis is satisfiable. -/
example : (1 : ℝ) ≠ 0 := one_ne_zero

/-- A one-point critical family witnesses the theorem's hypotheses and conclusion. -/
example :
    (∀ rho : Fin 1, (fun _ : Fin 1 => (1 / 2 : ℝ)) rho = 1 / 2) ↔
      criticalDampingDefect (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 = 0 :=
  critical_damping_flatness_criterion (fun _ : Fin 1 => (1 / 2 : ℝ)) 1 one_ne_zero

#print axioms critical_damping_flatness_criterion

end D5.S3.Zeros.Symmetry.CriticalDampingFlatness

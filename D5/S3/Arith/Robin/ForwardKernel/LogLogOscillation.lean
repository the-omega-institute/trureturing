/- GID: D5/S3/Arith/Robin/ForwardKernel/LogLogOscillation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/LogLogOscillation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The forward response has two-sided logarithmic logarithmic excursions under the paired xi expansion. -/

import D5.S3.Arith.Robin.ForwardKernel.PairedLaplace

namespace D5.S3.Arith.Robin.ForwardKernel

open Set MeasureTheory Filter
open scoped Topology BigOperators
open D5.S3.Analytic.Oscillation.FejerDirichletTransfer
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Weil.ZeroData.PairedXiExpansion (PairedXiExpansion)
open D5.S3.Arith.Robin.ForwardKernel.MellinPolynomialGrowth (VonKochBound)
open ForwardKernel.Transport (forwardResponse)

noncomputable section
set_option autoImplicit false

theorem forward_kernel_omega_pm_loglog (hRH : RiemannHypothesis) (hVK : VonKochBound)
    (hH : PairedXiExpansion hRH) :
    ∃ c : ℝ, 0 < c ∧
      (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ Real.exp 1 < x ∧ forwardResponse x ≤ -c * Real.log (Real.log x)) ∧
      (∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ Real.exp 1 < x ∧ c * Real.log (Real.log x) ≤ forwardResponse x) := by
  let D := forwardPairedLaplaceData hRH hVK hH (x0 := 3) (by norm_num)
  obtain ⟨c, hc, hneg, hpos⟩ :=
    quantitative_fejer_dirichlet_transfer (zetaSpectrum hRH)
      (D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum.zetaSpectrum_countAsymptotic hRH) D
  refine ⟨c, hc, ?_, ?_⟩
  · intro X
    obtain ⟨y, hyY, hy1, hyf⟩ := hneg (max (Real.log 3) (max (Real.log X) 2))
    let x : ℝ := Real.exp y
    have hy2 : 2 ≤ y :=
      (le_max_right (Real.log X) 2).trans
        ((le_max_right (Real.log 3) (max (Real.log X) 2)).trans hyY)
    have hlog3 : Real.log 3 < 2 := by
      convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≠ 1) using 1 <;> norm_num
    have hcut : Real.log 3 < y := hlog3.trans_le hy2
    have hX : X ≤ x := by
      by_cases hX0 : X ≤ 0
      · exact hX0.trans (le_of_lt (Real.exp_pos y))
      · have hXp : 0 < X := lt_of_not_ge hX0
        have hlogX : Real.log X ≤ y :=
          (le_max_left (Real.log X) 2).trans (le_max_right (Real.log 3) (max (Real.log X) 2) |>.trans hyY)
        have he := Real.exp_le_exp.mpr hlogX
        simpa [x, Real.exp_log hXp] using he
    have hxe : Real.exp 1 < x := by
      dsimp [x]
      exact Real.exp_lt_exp.mpr hy1
    have hforward : forwardLog 3 y = forwardResponse x := by
      rw [forwardLog, if_pos hcut]
    refine ⟨x, hX, hxe, ?_⟩
    calc
      forwardResponse x = forwardLog 3 y := hforward.symm
      _ ≤ -c * Real.log y := hyf
      _ = -c * Real.log (Real.log x) := by simp [x]
  · intro X
    obtain ⟨y, hyY, hy1, hyf⟩ := hpos (max (Real.log 3) (max (Real.log X) 2))
    let x : ℝ := Real.exp y
    have hy2 : 2 ≤ y :=
      (le_max_right (Real.log X) 2).trans
        ((le_max_right (Real.log 3) (max (Real.log X) 2)).trans hyY)
    have hlog3 : Real.log 3 < 2 := by
      convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) ≠ 1) using 1 <;> norm_num
    have hcut : Real.log 3 < y := hlog3.trans_le hy2
    have hX : X ≤ x := by
      by_cases hX0 : X ≤ 0
      · exact hX0.trans (le_of_lt (Real.exp_pos y))
      · have hXp : 0 < X := lt_of_not_ge hX0
        have hlogX : Real.log X ≤ y :=
          (le_max_left (Real.log X) 2).trans (le_max_right (Real.log 3) (max (Real.log X) 2) |>.trans hyY)
        have he := Real.exp_le_exp.mpr hlogX
        simpa [x, Real.exp_log hXp] using he
    have hxe : Real.exp 1 < x := by
      dsimp [x]
      exact Real.exp_lt_exp.mpr hy1
    have hforward : forwardLog 3 y = forwardResponse x := by
      rw [forwardLog, if_pos hcut]
    refine ⟨x, hX, hxe, ?_⟩
    calc
      c * Real.log (Real.log x) = c * Real.log y := by simp [x]
      _ ≤ forwardLog 3 y := hyf
      _ = forwardResponse x := hforward

end
end D5.S3.Arith.Robin.ForwardKernel

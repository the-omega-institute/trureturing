/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized zero-free collar for every positive Xu--Zhao composition. -/

import D5.S3.AnalyticClosure.Polylogarithm.CompositionBanks
import D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFree
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Complex Filter Metric Set Topology
open scoped ComplexConjugate

namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar

open CompositionDisk CompositionContinuation

/-- The actual slit continuation after removing its exact source power at the origin. -/
def normalizedContinuation (head : ℕ+) (tail : List ℕ+) (z : ℂ) : ℂ :=
  if z = 0 then CompositionDisk.normalized head tail 0
  else CompositionContinuation.continued (head :: tail) z /
    z ^ CompositionDisk.depth tail

/-- Every positive composition has one radius beyond the unit disk on which its
actual normalized slit continuation is zero-free. -/
theorem result (head : ℕ+) (tail : List ℕ+) :
    (∀ z, ‖z‖ < 1 → normalizedContinuation head tail z =
      CompositionDisk.normalized head tail z) /\
    AnalyticOnNhd ℂ (normalizedContinuation head tail) CompositionContinuation.omega /\
    ∃ R0 : ℝ, 1 < R0 /\ ∀ z ∈ CompositionContinuation.omega,
      ‖z‖ < R0 → normalizedContinuation head tail z ≠ 0 := by
  classical
  obtain ⟨_normSummable, hnormalizedAnalytic, hnormalizedNonzero,
      _hlogAnalytic, hlogPositive⟩ := CompositionZeroFree.result head tail
  obtain ⟨_continuedNil, hcontinued, hsourceData, _leadingDerivative,
      _ordinaryDerivative⟩ := CompositionSlit.result
  have hcontinuedAnalytic := (hcontinued (head :: tail)).1
  have hcontinuedSource := (hcontinued (head :: tail)).2
  have hliSource := (CompositionDisk.source_series head tail).2.2.2.2.1
  have homega : IsOpen CompositionContinuation.omega :=
    Complex.isOpen_slitPlane.preimage (by fun_prop)
  have hballOmega : Metric.ball (0 : ℂ) 1 ⊆ CompositionContinuation.omega := by
    intro z hz
    simpa [CompositionContinuation.omega, sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)
  have hcontinuedLi : ∀ z : ℂ, ‖z‖ < 1 →
      CompositionContinuation.continued (head :: tail) z =
        CompositionDisk.li head tail z := by
    intro z hz
    exact (hcontinuedSource z hz).trans (hliSource z hz).symm
  have hnormalizedAgreement : ∀ z : ℂ, ‖z‖ < 1 →
      normalizedContinuation head tail z = CompositionDisk.normalized head tail z := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [normalizedContinuation, hz0]
    · rw [normalizedContinuation, if_neg hz0, hcontinuedLi z hz]
      simp only [CompositionDisk.li]
      field_simp
  have hnormalizedContinuationAnalytic :
      AnalyticOnNhd ℂ (normalizedContinuation head tail)
        CompositionContinuation.omega := by
    intro z hzomega
    by_cases hz0 : z = 0
    · subst z
      apply (hnormalizedAnalytic 0 (by simp)).congr
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with w hw
      exact (hnormalizedAgreement w (by simpa using hw)).symm
    · have hpow : z ^ CompositionDisk.depth tail ≠ 0 := pow_ne_zero _ hz0
      have hquot := (hcontinuedAnalytic z hzomega).div
        (analyticAt_id.pow (CompositionDisk.depth tail)) hpow
      apply hquot.congr
      filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
      have hw0 : w ≠ 0 := by simpa using hw
      simp [normalizedContinuation, hw0]
  have hunitCircleNonzero : ∀ zeta : ℂ,
      zeta ∈ CompositionContinuation.omega → ‖zeta‖ = 1 →
      CompositionContinuation.continued (head :: tail) zeta ≠ 0 := by
    intro zeta hzetaOmega hzetaNorm
    have hzeta0 : zeta ≠ 0 := by
      intro hzetaZero
      subst zeta
      norm_num at hzetaNorm
    let F : ℝ -> ℂ := fun r =>
      CompositionContinuation.continued (head :: tail) ((r : ℂ) * zeta)
    let H : ℝ -> ℝ := fun r => ‖F r‖ ^ 2
    have hrayOmega : ∀ r : ℝ, r ∈ Set.Icc (1 / 2 : ℝ) 1 →
        (r : ℂ) * zeta ∈ CompositionContinuation.omega := by
      intro r hr
      by_cases hr1 : r = 1
      · simpa [hr1] using hzetaOmega
      · apply hballOmega
        have hrnonneg : 0 ≤ r := le_trans (by norm_num) hr.1
        rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hrnonneg, hzetaNorm, mul_one]
        exact lt_of_le_of_ne hr.2 (by
          intro h
          exact hr1 h)
    have hHContinuous : ContinuousOn H (Set.Icc (1 / 2 : ℝ) 1) := by
      intro r hr
      have hinner : HasDerivAt (fun s : ℝ => (s : ℂ) * zeta) zeta r := by
        simpa using (hasDerivAt_id r).ofReal_comp.mul_const zeta
      have hFContinuous : ContinuousAt F r := by
        simpa [F] using
          (hcontinuedAnalytic _ (hrayOmega r hr)).continuousAt.comp'
            (f := fun s : ℝ => (s : ℂ) * zeta) hinner.continuousAt
      exact (hFContinuous.norm.pow 2).continuousWithinAt
    have hHDerivativePositive : ∀ r : ℝ,
        r ∈ interior (Set.Icc (1 / 2 : ℝ) 1) → 0 < deriv H r := by
      intro r hr
      have hr' : r ∈ Set.Ioo (1 / 2 : ℝ) 1 := by simpa using hr
      have hrpos : 0 < r := lt_trans (by norm_num) hr'.1
      have hr0 : r ≠ 0 := hrpos.ne'
      let z : ℂ := (r : ℂ) * zeta
      have hzNorm : ‖z‖ = r := by
        simp only [z, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hrpos, hzetaNorm, mul_one]
      have hzDisk : ‖z‖ < 1 := by rw [hzNorm]; exact hr'.2
      have hzOmega : z ∈ CompositionContinuation.omega :=
        hballOmega (by simpa using hzDisk)
      have hz0 : z ≠ 0 := by
        dsimp [z]
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0) hzeta0
      have hnormalizedZ : CompositionDisk.normalized head tail z ≠ 0 :=
        hnormalizedNonzero z hzDisk
      have hliZ : CompositionDisk.li head tail z ≠ 0 := by
        rw [CompositionDisk.li]
        exact mul_ne_zero (pow_ne_zero _ hz0) hnormalizedZ
      have hfunctions :
          CompositionContinuation.continued (head :: tail) =ᶠ[nhds z]
            CompositionDisk.li head tail := by
        filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : ℂ) 1 by
          simpa using hzDisk)] with w hw
        exact hcontinuedLi w (by simpa using hw)
      have hderivEq : deriv (CompositionContinuation.continued (head :: tail)) z =
          deriv (CompositionDisk.li head tail) z := hfunctions.deriv_eq
      have hlogIdentity : deriv (CompositionDisk.li head tail) z =
          CompositionDisk.logarithmicDerivative head tail z *
            CompositionDisk.li head tail z / z := by
        have hdef : CompositionDisk.logarithmicDerivative head tail z *
            CompositionDisk.li head tail z =
              z * deriv (CompositionDisk.li head tail) z := by
          rw [CompositionDisk.logarithmicDerivative, if_neg hz0]
          exact (div_mul_cancel₀ _ hliZ)
        apply (eq_div_iff hz0).2
        calc
          deriv (CompositionDisk.li head tail) z * z =
              z * deriv (CompositionDisk.li head tail) z := mul_comm _ _
          _ = CompositionDisk.logarithmicDerivative head tail z *
              CompositionDisk.li head tail z := hdef.symm
      have hinner : HasDerivAt (fun s : ℝ => (s : ℂ) * zeta) zeta r := by
        simpa using (hasDerivAt_id r).ofReal_comp.mul_const zeta
      have hFDeriv : HasDerivAt F
          ((CompositionDisk.logarithmicDerivative head tail z / (r : ℂ)) * F r) r := by
        have hraw := (hcontinuedAnalytic z hzOmega).differentiableAt.hasDerivAt.comp r hinner
        change HasDerivAt F
          (deriv (CompositionContinuation.continued (head :: tail)) z * zeta) r at hraw
        convert hraw using 1
        dsimp [F]
        rw [hcontinuedLi z hzDisk, hderivEq, hlogIdentity]
        dsimp [z]
        field_simp [hr0, hzeta0]
      have hHDeriv := hFDeriv.norm_sq
      have hHFormula : deriv H r =
          2 * ‖F r‖ ^ 2 * (CompositionDisk.logarithmicDerivative head tail z).re / r := by
        rw [hHDeriv.deriv]
        simp only [Complex.inner]
        rw [show ((CompositionDisk.logarithmicDerivative head tail z / (r : ℂ)) * F r) *
            conj (F r) = (CompositionDisk.logarithmicDerivative head tail z / (r : ℂ)) *
              (F r * conj (F r)) by ring,
          Complex.mul_conj]
        simp [Complex.div_re, Complex.normSq_apply]
        field_simp [hr0]
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [hHFormula]
      have hFne : F r ≠ 0 := by
        dsimp [F]
        rw [hcontinuedLi z hzDisk]
        exact hliZ
      have hFnorm : 0 < ‖F r‖ := norm_pos_iff.mpr hFne
      have hlog := hlogPositive z hzDisk
      exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hFnorm)) hlog)
        hrpos
    have hstrict : StrictMonoOn H (Set.Icc (1 / 2 : ℝ) 1) :=
      strictMonoOn_of_deriv_pos (convex_Icc _ _) hHContinuous hHDerivativePositive
    have hhalfMem : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by norm_num
    have honeMem : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by norm_num
    have hhalfDisk : ‖((1 / 2 : ℝ) : ℂ) * zeta‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
        hzetaNorm]
      norm_num
    have hhalfNe : F (1 / 2) ≠ 0 := by
      dsimp [F]
      rw [hcontinuedLi _ hhalfDisk, CompositionDisk.li]
      exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by norm_num) hzeta0))
        (hnormalizedNonzero _ hhalfDisk)
    have hgrowth := hstrict hhalfMem honeMem (by norm_num : (1 / 2 : ℝ) < 1)
    intro honeZero
    have hHzero : H 1 = 0 := by simp [H, F, honeZero]
    have hHhalfPositive : 0 < H (1 / 2) := by
      dsimp [H]
      exact sq_pos_of_pos (norm_pos_iff.mpr hhalfNe)
    rw [hHzero] at hgrowth
    linarith
  obtain ⟨rho, hrho0, hrho1, hbank, _hendpoint, _hbanks⟩ :=
    CompositionBanks.result head tail (1 : ℕ+)
  let V : Set ℂ := {z | z ∈ CompositionContinuation.omega /\
    normalizedContinuation head tail z ≠ 0}
  let U : Set ℂ := V ∪ Metric.ball 1 rho
  have hVOpen : IsOpen V := by
    change IsOpen (CompositionContinuation.omega ∩
      normalizedContinuation head tail ⁻¹' {z : ℂ | z ≠ 0})
    exact hnormalizedContinuationAnalytic.continuousOn.isOpen_inter_preimage
      homega isOpen_ne
  have hUOpen : IsOpen U := hVOpen.union Metric.isOpen_ball
  have hclosedBallSubset : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    change z ∈ V ∪ Metric.ball (1 : ℂ) rho
    have hzNorm : ‖z‖ <= 1 := by simpa using hz
    by_cases hzin : ‖z‖ < 1
    · left
      refine ⟨hballOmega (by simpa using hzin), ?_⟩
      rw [hnormalizedAgreement z hzin]
      exact hnormalizedNonzero z hzin
    · have hzNormEq : ‖z‖ = 1 := le_antisymm hzNorm (not_lt.mp hzin)
      by_cases hzball : z ∈ Metric.ball (1 : ℂ) rho
      · exact Or.inr hzball
      · left
        have hz1 : z ≠ 1 := by
          intro hzOne
          apply hzball
          simp [hzOne, hrho0]
        have hzOmega : z ∈ CompositionContinuation.omega := by
          rw [CompositionContinuation.omega, mem_ofPred_eq, Complex.mem_slitPlane_iff]
          by_cases him : z.im = 0
          · left
            have hsqNorm : Complex.normSq z = 1 := by
              have := congrArg (fun x : ℝ => x ^ 2) hzNormEq
              simpa [Complex.sq_norm] using this
            have hsq : z.re ^ 2 = 1 := by
              rw [Complex.normSq_apply, him] at hsqNorm
              nlinarith
            have hre : z.re ≠ 1 := by
              intro hre
              apply hz1
              apply Complex.ext
              · simp [hre]
              · simp [him]
            have hreNeg : z.re = -1 := (sq_eq_one_iff.mp hsq).resolve_left hre
            simp only [sub_re, one_re]
            rw [hreNeg]
            norm_num
          · right
            simpa using him
        exact ⟨hzOmega, by
          by_cases hz0 : z = 0
          · subst z; norm_num at hzNormEq
          · simp only [normalizedContinuation, if_neg hz0, div_ne_zero_iff]
            exact ⟨hunitCircleNonzero z hzOmega hzNormEq, pow_ne_zero _ hz0⟩⟩
  obtain ⟨delta, hdelta, hthick⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open
      hUOpen hclosedBallSubset
  refine ⟨hnormalizedAgreement, hnormalizedContinuationAnalytic,
    1 + delta, by linarith, ?_⟩
  intro z hzOmega hzRadius
  have hzThick : z ∈ Metric.cthickening delta (Metric.closedBall (0 : ℂ) 1) := by
    rw [cthickening_closedBall hdelta.le (by norm_num) (0 : ℂ)]
    simpa [add_comm] using hzRadius.le
  have hzU : z ∈ U := hthick hzThick
  change z ∈ V ∪ Metric.ball (1 : ℂ) rho at hzU
  rcases hzU with hzV | hzBankBall
  · exact hzV.2
  · have hzBank : ‖z - 1‖ <= rho := by
      have hzBankLt : ‖z - 1‖ < rho := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hzBankBall
      exact hzBankLt.le
    have hz0 : z ≠ 0 := by
      intro hzZero
      subst z
      norm_num at hzBank
      linarith
    simp only [normalizedContinuation, if_neg hz0, div_ne_zero_iff]
    exact ⟨hbank z hzOmega hzBank, pow_ne_zero _ hz0⟩

end D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFreeCollar

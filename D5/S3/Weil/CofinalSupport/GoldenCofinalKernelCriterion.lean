/- GID: D5/S3/Weil/CofinalSupport/GoldenCofinalKernelCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/CofinalSupport/GoldenCofinalKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A cofinal vanishing-scale kernel family is positive semidefinite exactly under RH. -/

import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaCore.OffLinePickWitness
import D5.S3.Weil.ZetaRvm.CountByIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Matrix.PosDef

/-!
# Golden cofinal kernel criterion

Library-search audit trail (2026-09-03):

* Six-way repository searches found the adjacent cofinal-support theorem and the frozen
  one-point off-line certificate, but no theorem combining a vanishing scale family with an RH
  equivalence. The in-flight `HalfPlanePositiveKernelCriterion` handles one fixed abstract kernel
  and assumes its RH equivalence, so it does not cover this cofinal reverse implication.
* The existing `golden_right_half_strip_implies_rh`,
  `completedRiemannZeta_eq_zero_iff`, `xi_reading_eq_completed_zeta`, and
  `off_line_one_point_pick_witness` are imported and applied directly.
* Pinned Mathlib supplies `Filter.Tendsto.eventually_lt_const`, the isolated-zero alternative,
  the analytic identity theorem, and `Matrix.PosSemidef.det_nonneg`. No pinned or installed
  third-party theorem states the complete cofinal criterion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set
open scoped ComplexOrder Topology

namespace D5.S3.Weil.CofinalSupport.GoldenCofinalKernelCriterion

open D5.S3.Zeros.CompletedZeta
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open D5.S3.Weil.ZetaCore.OffLinePickWitness

/-- A positive sequence tending to zero samples positive-semidefinite kernels at every scale
exactly under RH, provided RH gives the forward Hermite--Biehler positivity. In the reverse
direction, isolated xi zeros ensure that some sufficiently small sampled shift is nonzero; the
canonical one-point calculation then contradicts the diagonal of its positive Gram matrix. -/
theorem golden_cofinal_kernel_criterion
    (omega : Nat -> Real) (kernel : Nat -> Complex -> Complex -> Complex)
    (hOmegaPositive : forall n, 0 < omega n)
    (hOmegaZero : Tendsto omega atTop (nhds 0))
    (hKernelDiagonal : forall n z,
      kernel n z z = (diagonalValue (omega n) z : Complex))
    (hRhPositive : RiemannHypothesis ->
      forall n N (points : Fin N -> Complex),
        (Matrix.of fun i j => kernel n (points i) (points j)).PosSemidef) :
    RiemannHypothesis <->
      forall n N (points : Fin N -> Complex),
        (Matrix.of fun i j => kernel n (points i) (points j)).PosSemidef := by
  constructor
  · exact hRhPositive
  · intro hAllPositive
    apply golden_right_half_strip_implies_rh
    intro rho hZetaZero hRight hStrip
    let delta : Real := rho.re - 1 / 2
    let gamma : Real := rho.im
    have hDelta : 0 < delta := by
      dsimp only [delta]
      linarith
    have hRhoRepresentation :
        rho = (1 / 2 : Complex) + (delta : Complex) +
          Complex.I * (gamma : Complex) := by
      apply Complex.ext
      · simp [delta]
      · simp [gamma]
    have hRhoZero : rho ≠ 0 := by
      intro hRho
      have hReal : rho.re = 0 := by
        simpa using congrArg Complex.re hRho
      linarith
    have hRhoOne : rho ≠ 1 := by
      intro hRho
      have hReal : rho.re = 1 := by
        simpa using congrArg Complex.re hRho
      linarith
    have hXiZero : xiReading rho = 0 := by
      rw [xi_reading_eq_completed_zeta hRhoZero hRhoOne]
      have hCompleted : completedZetaReading rho = 0 := by
        exact Zeta23.RvM.completedRiemannZeta_eq_zero_iff.mpr
          ⟨hZetaZero, by linarith, hStrip⟩
      rw [hCompleted]
      ring
    have hXiAnalytic : AnalyticOnNhd Complex xiReading Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr xi_reading_differentiable
    rcases (hXiAnalytic rho (Set.mem_univ rho)).eventually_eq_zero_or_eventually_ne_zero with
      hLocallyZero | hIsolated
    · have hIdenticallyZero : xiReading = fun _ => 0 :=
        hXiAnalytic.eq_of_eventuallyEq analyticOnNhd_const hLocallyZero
      have hXiAtZero : xiReading 0 ≠ 0 := by
        norm_num [xiReading]
      exact (hXiAtZero (by simpa using congrFun hIdenticallyZero 0)).elim
    · let shiftedPoint : Nat -> Complex := fun n => rho - (2 * omega n : Complex)
      have hOmegaComplex :
          Tendsto (fun n => (omega n : Complex)) atTop (nhds 0) :=
        hOmegaZero.ofReal
      have hShiftedTendsto : Tendsto shiftedPoint atTop (nhds rho) := by
        dsimp only [shiftedPoint]
        simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hOmegaComplex)
      have hShiftedNe (n : Nat) : shiftedPoint n ≠ rho := by
        dsimp only [shiftedPoint]
        intro hEq
        have hZero : (2 * (omega n : Complex)) = 0 := sub_eq_self.mp hEq
        exact (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr (ne_of_gt (hOmegaPositive n)))) hZero
      have hShiftedPunctured :
          Tendsto shiftedPoint atTop (nhdsWithin rho {rho}ᶜ) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hShiftedTendsto, Filter.Eventually.of_forall fun n => by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hShiftedNe n⟩
      have hEventuallyNonzero :
          ∀ᶠ n in atTop, xiReading (shiftedPoint n) ≠ 0 :=
        hShiftedPunctured.eventually hIsolated
      have hEventuallySmall : ∀ᶠ n in atTop, omega n < delta :=
        hOmegaZero.eventually_lt_const hDelta
      obtain ⟨n, hOmegaSmall, hShiftNonzero⟩ :=
        (hEventuallySmall.and hEventuallyNonzero).exists
      have hWitness := off_line_one_point_pick_witness
        rho delta gamma (omega n) hRhoRepresentation hDelta
        (hOmegaPositive n) hOmegaSmall hXiZero (by
          simpa only [shiftedPoint] using hShiftNonzero)
      dsimp only at hWitness
      let zrho : Complex :=
        -(gamma : Complex) + Complex.I * ((delta - omega n : Real) : Complex)
      have hGramPositive := hAllPositive n 1 (fun _ => zrho)
      have hDetNonnegative := hGramPositive.det_nonneg
      have hDiagonalComplex : (0 : Complex) <= kernel n zrho zrho := by
        simpa [Matrix.det_fin_one] using hDetNonnegative
      have hDiagonalNonnegative : 0 <= diagonalValue (omega n) zrho := by
        have hRealNonnegative := (Complex.nonneg_iff.mp hDiagonalComplex).1
        rw [hKernelDiagonal n zrho] at hRealNonnegative
        simpa using hRealNonnegative
      exact (not_lt_of_ge hDiagonalNonnegative) hWitness.2.1

#print axioms golden_cofinal_kernel_criterion

end D5.S3.Weil.CofinalSupport.GoldenCofinalKernelCriterion

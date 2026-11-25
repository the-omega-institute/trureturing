/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEightNinths
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEightNinths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An order exponent arbitrarily close to eight ninths for the signed RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.PowerPrefixWindow
import D5.S3.Weil.ZetaPntBounds.MobiusEnergyPointwise

/-! The phase variation under exponential damping improves the signed prime-window bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (spectralPrimitive windowDiscrepancy)

/-- Under RH the signed prime-window residual has order exponent at most eight ninths plus
any positive slack, including coincident real endpoints. -/
theorem prime_window_mobius_eight_ninths_of_rh (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^(8/9+ε : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  let η := min (ε/2) (1/36)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηupper : η ≤ 1/36 := min_le_right _ _
  have hηε : η ≤ ε/2 := min_le_left _ _
  have hzero (z : ℂ) (hz : 1/2 < z.re) (hne : z ≠ 1) : riemannZeta z ≠ 0 := by
    intro hroot
    have htriv : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
      rintro ⟨n, rfl⟩
      simp at hz
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (ne_of_gt hz) (hRH z hroot htriv hne)
  obtain ⟨P, hP, hprefix⟩ :=
    @D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence.unweighted_mobius_prefix_power_bound
      (1/2) (3*η) (by norm_num) (by norm_num) hzero (by linarith) (by linarith)
  have hpre (k : ℕ) (hk : 1 ≤ k) :
      |∑ n ∈ Finset.Icc 1 k, (μ n : ℝ)| ≤ P*(k : ℝ)^(2/3+η) := by
    simpa only [show (2+3*η)/3 = 2/3+η by ring] using hprefix k hk
  have hwindow := prime_window_mobius_of_power_prefix hRH
    (show 0 ≤ 2/3+η by linarith) (show 2/3+η < 1 by linarith)
    hP (show 0 < ε-η/3 by linarith) hpre
  simpa only [show (2+(2/3+η))/3+(ε-η/3) = 8/9+ε by ring] using hwindow

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

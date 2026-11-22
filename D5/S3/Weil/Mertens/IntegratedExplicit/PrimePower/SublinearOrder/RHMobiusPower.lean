/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Power-saving order bound for the signed RH prime window. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusInverseLog
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.PowerWindowDensity
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.SignedOmittedSpectrum

/-! Power-saving bounds on the signed prime-tail remainder under RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open Real ArithmeticFunction Finset Chebyshev MeasureTheory
open Set (Ioi)
open scoped ArithmeticFunction.Moebius
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder
  (spectralPrimitive windowDiscrepancy)

private theorem density_power (hRH : RiemannHypothesis) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 2 ≤ m → ∀ u : ℝ, Real.log 2 ≤ u →
      |rootWindowDensity u - ((∑ n ∈ Finset.Icc 2 m, retainedDensity m n u) - 2)| ≤
        K * (((m : ℝ)+1)^(27/28 : ℝ)) * Real.exp (-(orderRate m)*u) := by
  obtain ⟨P, hP, hpre⟩ := mobius_prefix_rh_power hRH
  have hprefix (k : ℕ) (_ : 1 ≤ k) :
      |∑ n ∈ Finset.Ioc 0 k, (μ n : ℝ)| ≤ P*(k : ℝ)^(3/4 : ℝ) :=
    hpre k k le_rfl
  obtain ⟨F, hF, hfar⟩ := signed_omitted_root_density_power hRH
    (fun m _ => range_moebius_prefix_of_Ioc_power_bound
      (β := 3/4) (by norm_num) hP.le hprefix m)
  exact window_density_of_power_prefix hRH (by norm_num) (by norm_num)
    (by norm_num) hP hF hprefix hfar

/-- A uniform power-saving order bound for the signed Möbius prime-tail interval. -/
theorem prime_window_mobius_power_of_rh (hRH : RiemannHypothesis) :
    ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧
      ∀ m : ℕ, 2 ≤ m → ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |windowDiscrepancy a B - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        K * (m : ℝ)^(27/28 : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2)) := by
  obtain ⟨a₀, ha₀, hwindow⟩ := prime_window_threshold_of_rh hRH
  obtain ⟨D, hD, hDens⟩ := density_power hRH
  refine ⟨a₀, 12*D, ha₀, by positivity, fun m hm a B ha hAB => ?_⟩
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 2 m) {a B : ℝ} (ha : 2 ≤ a) (hab : a ≤ B) := by
    have ha₀ : 0 < a := by linarith
    exact retainedDensity_integral (m := m) (Finset.mem_Icc.mp hn).1 ha₀ (ha₀.trans_le hab)
  have h := hwindow m hm retainedDensity
    (fun n hn a B ha hab => by
      simpa only [arithmeticPrimitive, capturedPrimitive, powerGap, arithmeticRate, neg_sub]
        using hterm n hn ha hab)
    (D * ((m : ℝ)+1)^(27/28 : ℝ)) (hDens m hm) a B ha hAB
  have hm₂ : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpower : ((m : ℝ)+1)^(27/28 : ℝ) ≤ 2*(m : ℝ)^(27/28 : ℝ) := by
    refine (Real.rpow_le_rpow (by positivity) (show (m : ℝ)+1 ≤ 2*(m : ℝ) by linarith)
      (by norm_num : (0 : ℝ) ≤ 27/28)).trans ?_
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (27/28 : ℝ) ≤ 1)
  have ha' : 0 < a := by linarith
  have hgap : 0 ≤ a ^ ((m + 1 : ℝ)⁻¹ - 1/2) - B ^ ((m + 1 : ℝ)⁻¹ - 1/2) := by
    apply sub_nonneg.mpr
    apply Real.rpow_le_rpow_of_nonpos ha' hAB
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ m+1 by linarith)
    norm_num at hi
    linarith
  have hcoef : 6*(D*((m : ℝ)+1)^(27/28 : ℝ)) ≤ (12*D)*(m : ℝ)^(27/28 : ℝ) := by
    calc
      _ = (6*D)*((m : ℝ)+1)^(27/28 : ℝ) := by ring
      _ ≤ (6*D)*(2*(m : ℝ)^(27/28 : ℝ)) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right hcoef hgap)

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

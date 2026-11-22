import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

/-! The actual negative-tail mass and an equal-endpoint intervention for the uniform expansion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ArithmeticFunction.Moebius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (spectralPrimitive)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear

open _root_.Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection
  (windowSignature massActual windowAltered)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

def massConclusion (R : Realization windowSignature) : Prop :=
    ∃ a₀ : ℝ, 2 ≤ a₀ ∧ ∀ ε > (0 : ℝ), ∃ M : ℕ, 2 ≤ M ∧
      ∀ m ≥ M, ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |R.readout () () (a, B) - 2 * Real.log (B / a) - spectralPrimitive (phaseOrbit (Real.log B)) +
        spectralPrimitive (phaseOrbit (Real.log a)) -
        (∑ n ∈ Finset.Icc 3 m, -(μ n : ℝ) *
          (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
          (a ^ ((n : ℝ)⁻¹ - 1 / 2) - B ^ ((n : ℝ)⁻¹ - 1 / 2))) -
        (∑ n ∈ (Finset.Icc 2 m).filter (fun n => 2 * n < m + 1),
          -(μ n : ℝ) * (rootPrimitive (n : ℝ) B - rootPrimitive (n : ℝ) a))| ≤
        ε * (m : ℝ) *
          (a ^ ((m + 1 : ℝ)⁻¹ - 1 / 2) - B ^ ((m + 1 : ℝ)⁻¹ - 1 / 2))

abbrev massArena : Arena := ⟨windowSignature, fun R => RiemannHypothesis → massConclusion R⟩

theorem mass_source_bridge :
    (type_of% @prime_window_mobius_sublinear_of_rh) ↔ massArena.Law massActual :=
  Iff.rfl

theorem mass_altered_rejects : ¬ massConclusion windowAltered := by
  rintro ⟨a₀, ha₀, h⟩
  have hnonzero : a₀ ≠ 0 := by linarith
  obtain ⟨M, _, hM⟩ := h 1 zero_lt_one
  have hdiagonal := hM M le_rfl a₀ a₀ le_rfl le_rfl
  change |1 - 2 * Real.log (a₀ / a₀) -
    spectralPrimitive (phaseOrbit (Real.log a₀)) + spectralPrimitive (phaseOrbit (Real.log a₀)) -
    (∑ n ∈ Finset.Icc 3 M, -(μ n : ℝ) * (2 * (n : ℝ)^2 / (((n : ℝ) - 1) * ((n : ℝ) - 2))) *
      (a₀ ^ ((n : ℝ)⁻¹ - 1 / 2) - a₀ ^ ((n : ℝ)⁻¹ - 1 / 2))) -
    (∑ n ∈ (Finset.Icc 2 M).filter (fun n => 2 * n < M + 1),
      -(μ n : ℝ) * (rootPrimitive (n : ℝ) a₀ - rootPrimitive (n : ℝ) a₀))| ≤
    1 * (M : ℝ) * (a₀ ^ ((M + 1 : ℝ)⁻¹ - 1 / 2) - a₀ ^ ((M + 1 : ℝ)⁻¹ - 1 / 2)) at hdiagonal
  simp only [div_self hnonzero, Real.log_one, mul_zero, sub_zero, sub_add_cancel, sub_self,
    Finset.sum_const_zero, abs_one] at hdiagonal
  norm_num at hdiagonal

theorem mass_sensitivity_iff_rh : Sensitivity massArena massActual ↔ RiemannHypothesis := by
  constructor
  · intro hs
    obtain ⟨_, _, _, hrejected⟩ := hs.1 ()
    by_contra hn
    exact hrejected (fun h => (hn h).elim)
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity massArena.Law massActual
      windowAltered (fun h => mass_altered_rejects (h hRH))

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHMobiusSublinear

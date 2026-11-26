import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHFifthWindow
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

/-! A constant readout violates the fifth-root window conclusion at equal endpoints.
The intervention retains the source law's RH hypothesis. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (spectralPrimitive)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHFifthWindow

open RHRootCorrection (windowSignature massActual windowAltered)

def massConclusion (R : Realization windowSignature) : Prop :=
  ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
    |R.readout () () (a, B) - 2 * Real.log (B / a) -
      spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
      9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
      (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ))| ≤
        K * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ))

abbrev massArena : Arena := ⟨windowSignature, fun R => RiemannHypothesis → massConclusion R⟩

theorem mass_source_bridge :
    (type_of% @prime_window_fifth_of_rh) ↔ massArena.Law massActual :=
  Iff.rfl

theorem mass_altered_rejects : ¬ massConclusion windowAltered := by
  rintro ⟨a₀, K, ha₀, _, h⟩
  have hnonzero : a₀ ≠ 0 := by linarith
  have hdiagonal := h a₀ a₀ le_rfl le_rfl
  change |1 - 2 * Real.log (a₀ / a₀) -
    spectralPrimitive (phaseOrbit (Real.log a₀)) + spectralPrimitive (phaseOrbit (Real.log a₀)) -
    9 * (a₀ ^ (-(1 / 6) : ℝ) - a₀ ^ (-(1 / 6) : ℝ)) -
    squarePrimitive a₀ + squarePrimitive a₀ -
    (25 / 6) * (a₀ ^ (-(3 / 10) : ℝ) - a₀ ^ (-(3 / 10) : ℝ))| ≤
      K * (a₀ ^ (-(1 / 3) : ℝ) - a₀ ^ (-(1 / 3) : ℝ)) at hdiagonal
  norm_num [div_self hnonzero, sub_add_cancel] at hdiagonal

theorem mass_sensitivity_iff_rh : Sensitivity massArena massActual ↔ RiemannHypothesis := by
  constructor
  · intro hs
    obtain ⟨_, _, _, hrejected⟩ := hs.1 ()
    by_contra hn
    exact hrejected (fun h => (hn h).elim)
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity massArena.Law massActual
      windowAltered (fun h => mass_altered_rejects (h hRH))

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHFifthWindow

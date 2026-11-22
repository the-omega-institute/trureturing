import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHSeventhWindow
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

/-! The actual prime-window readout and the diagonal intervention under the source RH antecedent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster (phaseOrbit)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowRemainder (spectralPrimitive)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open _root_.D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero)

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHSeventhWindow

open RHRootCorrection (windowSignature massActual windowAltered)

def massConclusion (R : Realization windowSignature) : Prop :=
  let A₃ (x : ℝ) := 18 * (∑' k, (x : ℂ) ^ (actualZero k / 3 - 1 / 2) /
    (actualZero k * (3 - actualZero k) * (3 - 2 * actualZero k))).re
  ∃ a₀ K : ℝ, 2 ≤ a₀ ∧ 0 < K ∧ ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
    |R.readout () () (a, B) - 2 * Real.log (B / a) -
      spectralPrimitive (phaseOrbit (Real.log B)) + spectralPrimitive (phaseOrbit (Real.log a)) -
      9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) - squarePrimitive B + squarePrimitive a -
      (25 / 6) * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ)) +
      (18 / 5) * (a ^ (-(1 / 3) : ℝ) - B ^ (-(1 / 3) : ℝ)) -
      A₃ B + A₃ a -
      (49 / 15) * (a ^ (-(5 / 14) : ℝ) - B ^ (-(5 / 14) : ℝ))| ≤
        K * (a ^ (-(3 / 8) : ℝ) - B ^ (-(3 / 8) : ℝ))

abbrev massArena : Arena :=
  ⟨windowSignature, fun R => RiemannHypothesis → massConclusion R⟩

theorem mass_source_bridge :
    (type_of% @prime_window_seventh_of_rh) ↔ massArena.Law massActual := Iff.rfl

theorem mass_altered_rejects : ¬ massConclusion windowAltered := by
  rintro ⟨a₀, K, ha₀, _, h⟩
  have hnonzero : a₀ ≠ 0 := by linarith
  have hdiagonal := h a₀ a₀ le_rfl le_rfl
  simp only [windowAltered, realize, div_self hnonzero, Real.log_one, mul_zero, sub_zero,
    sub_self, sub_add_cancel] at hdiagonal
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

theorem mass_dependence_of_rh (hRH : RiemannHypothesis) :
    ObservationalDependence windowSignature massActual := by
  intro i
  cases i
  obtain ⟨T, hT⟩ := eventually_atTop.mp (late_strict_prime_tail hRH)
  let a : ℝ := max T 2
  have ha : 2 ≤ a := le_max_right _ _
  have hab : a < a + 1 := lt_add_one _
  have hcont : ContinuousOn (fun x : ℝ => max (-primeTail x) 0 / Real.sqrt x) (Ici 1) :=
    (prime_integrable.continuousOn_Ici_primitive_Ioi.neg.sup continuousOn_const).div
      Real.continuous_sqrt.continuousOn
      (fun _ hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (mem_Ici.mp hx))).ne')
  have hI : IntervalIntegrable (fun x : ℝ => max (-primeTail x) 0 / Real.sqrt x)
      volume a (a + 1) := by
    apply (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact fun _ hx => (by linarith : 1 ≤ a).trans hx.1
  have hpos : 0 < ∫ x in a..a + 1, max (-primeTail x) 0 / Real.sqrt x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hI (fun x hx => by
      have hneg : 0 < -primeTail x :=
        pos_of_mul_pos_right (hT x ((le_max_left _ _).trans hx.1.le)) (Real.sqrt_nonneg _)
      exact div_pos (hneg.trans_le (le_max_left _ _))
        (Real.sqrt_pos.mpr (by linarith [hx.1]))) hab
  refine ⟨(), (a, a + 1), (a, a), ?_⟩
  change (∫ x in a..a + 1, max (-primeTail x) 0 / Real.sqrt x) ≠
    (∫ x in a..a, max (-primeTail x) 0 / Real.sqrt x)
  rw [intervalIntegral.integral_same]
  exact hpos.ne'

theorem mass_variation_iff_rh : Variation massArena massActual ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨_, _, hn⟩
    by_contra h
    exact hn (fun hr => (h hr).elim)
  · intro hRH
    exact ⟨prime_window_seventh_of_rh, windowAltered, fun h => mass_altered_rejects (h hRH)⟩

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHSeventhWindow

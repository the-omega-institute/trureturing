import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection
import Reg.Support.SingleDependentReadout

/-! The source laws retain the fixed RH antecedent. An altered window readout
fails at the diagonal, and an altered pointwise readout outruns every constant. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

abbrev pointSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def pointActual : Realization pointSignature :=
  realize pointSignature (fun _ _ x => Real.sqrt x * (Q x - primeTail x)) (fun e => nomatch e)

def pointConclusion (R : Realization pointSignature) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 8 ≤ x →
    |R.readout () () x - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) - squareDensity (Real.log x)| ≤
      K * x ^ (-(3 / 10) : ℝ)

abbrev pointArena : Arena := ⟨pointSignature, fun R => RiemannHypothesis → pointConclusion R⟩

theorem point_source_bridge : (type_of% @rh_prime_power_density) ↔ pointArena.Law pointActual :=
  Iff.rfl

def pointAltered : Realization pointSignature :=
  realize pointSignature (fun _ _ x => x * x ^ (-(3 / 10) : ℝ) + 2 +
    (3 / 2) * x ^ (-(1 / 6) : ℝ) + squareDensity (Real.log x)) (fun e => nomatch e)

theorem point_altered_rejects : ¬ pointConclusion pointAltered := by
  rintro ⟨K, _, h⟩
  let x := max 8 (K + 1)
  have hx : 8 ≤ x := le_max_left _ _
  have hKx : K < x := (lt_add_one K).trans_le (le_max_right _ _)
  have hp : 0 < x ^ (-(3 / 10) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hh := h x hx
  change |x * x ^ (-(3 / 10) : ℝ) + 2 + (3 / 2) * x ^ (-(1 / 6) : ℝ) +
    squareDensity (Real.log x) - 2 - (3 / 2) * x ^ (-(1 / 6) : ℝ) -
    squareDensity (Real.log x)| ≤ _ at hh
  have he : ∀ w a b : ℝ, w + 2 + a + b - 2 - a - b = w := by intros; ring
  rw [he, abs_of_pos (mul_pos (by linarith) hp)] at hh
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hKx hp)) hh

theorem point_sensitivity_iff_rh : Sensitivity pointArena pointActual ↔ RiemannHypothesis := by
  constructor
  · intro hs
    obtain ⟨R, _, _, hrejected⟩ := hs.1 ()
    by_contra hn
    exact hrejected (fun h => (hn h).elim)
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity pointArena.Law pointActual
      pointAltered (fun h => point_altered_rejects (h hRH))

abbrev windowSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ × ℝ) (fun _ => ℝ)

def windowActual : Realization windowSignature :=
  realize windowSignature (fun _ _ cuts =>
    ∫ u in Real.log cuts.1..Real.log cuts.2, rootWindowDensity u) (fun e => nomatch e)

def windowConclusion (R : Realization windowSignature) : Prop :=
  ∃ a₀ K : ℝ, 8 ≤ a₀ ∧ 0 < K ∧
    (∀ x : ℝ, a₀ ≤ x → 0 < Real.sqrt x * (-primeTail x)) ∧
    ∀ a B : ℝ, a₀ ≤ a → a ≤ B →
      |R.readout () () (a, B) - 9 * (a ^ (-(1 / 6) : ℝ) - B ^ (-(1 / 6) : ℝ)) -
        squarePrimitive B + squarePrimitive a| ≤
          K * (a ^ (-(3 / 10) : ℝ) - B ^ (-(3 / 10) : ℝ))

abbrev windowArena : Arena :=
  ⟨windowSignature, fun R => RiemannHypothesis → windowConclusion R⟩

theorem window_source_bridge :
    (type_of% @rh_root_correction_window) ↔ windowArena.Law windowActual :=
  Iff.rfl

def windowAltered : Realization windowSignature :=
  realize windowSignature (fun _ _ _ => 1) (fun e => nomatch e)

theorem window_altered_rejects : ¬ windowConclusion windowAltered := by
  rintro ⟨a₀, K, _, _, _, h⟩
  have hh := h a₀ a₀ le_rfl le_rfl
  change |1 - 9 * (a₀ ^ (-(1 / 6) : ℝ) - a₀ ^ (-(1 / 6) : ℝ)) -
    squarePrimitive a₀ + squarePrimitive a₀| ≤
      K * (a₀ ^ (-(3 / 10) : ℝ) - a₀ ^ (-(3 / 10) : ℝ)) at hh
  norm_num [sub_add_cancel] at hh

theorem window_sensitivity_iff_rh :
    Sensitivity windowArena windowActual ↔ RiemannHypothesis := by
  constructor
  · intro hs
    obtain ⟨R, _, _, hrejected⟩ := hs.1 ()
    by_contra hn
    exact hrejected (fun h => (hn h).elim)
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity windowArena.Law windowActual
      windowAltered (fun h => window_altered_rejects (h hRH))

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.RHRootCorrection

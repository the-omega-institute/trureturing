import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
import Reg.Support.UniverseSingleReadout

/-! The normalized primitive as a time-dependent observation of a balanced spectrum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder

open _root_.NeumannCenteredOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

noncomputable section

universe u

private def witnessSpectrum : BalancedSpectrum PUnit.{u + 1} where
  modes := {PUnit.unit}
  fastRate := 2
  fastWeight := 2
  rate := fun _ => 1
  weight := fun _ => 1
  rate_pos := by intros; norm_num
  rate_lt := by intros; norm_num
  weight_nonneg := by intros; norm_num
  weight_pos := ⟨PUnit.unit, by simp, by norm_num⟩
  balance := by norm_num

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ ι : Type u, BalancedSpectrum ι) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ q t => q.2.primitive t / t) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι),
    StrictAntiOn (fun t => R.readout () ⟨ι, S⟩ t) (Ioi 0)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hlt := h witnessSpectrum (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)
  change (0 : ℝ) < 0 at hlt
  exact (lt_irrefl 0) hlt

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨PUnit.{u + 1}, witnessSpectrum⟩, 1, 2, ?_⟩
  cases i
  exact (witnessSpectrum.strictAntiOn_primitive_div
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1 : ℝ) < 2)).ne'

def family : Registration arena.{u}
    (type_of% (@BalancedSpectrum.strictAntiOn_primitive_div.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨BalancedSpectrum.strictAntiOn_primitive_div, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.strictAntiOn_primitive_div.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.strictAntiOn_primitive_div.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t => q.2.primitive t / t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
open MeasureTheory
open scoped BigOperators

private def witnessPlus (x : ℝ) : ℝ := 2 * Real.exp (-(2 * x))
private def witnessMinus (x : ℝ) : ℝ := Real.exp (-x)

private theorem witnessPlus_continuous : Continuous witnessPlus := by
  unfold witnessPlus
  fun_prop

private theorem witnessMinus_continuous : Continuous witnessMinus := by
  unfold witnessMinus
  fun_prop

private theorem witnessPlus_strictAnti : StrictAnti witnessPlus := by
  intro x y hxy
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) (by norm_num)

private theorem witnessMinus_antitone : Antitone witnessMinus := by
  intro x y hxy
  exact Real.exp_le_exp.mpr (neg_le_neg hxy)

private theorem witness_difference (x : ℝ) :
    witnessPlus x - witnessMinus x = (witnessSpectrum.{u}).difference x := by
  simp [witnessPlus, witnessMinus, witnessSpectrum, BalancedSpectrum.difference]

namespace CenteredPrefix

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ _ : ℝ → ℝ, Σ _ : ℝ → ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q t => ∫ x in 0..t, centered q.1 q.2.2 x - centered q.2.1 q.2.2 x)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι) {kp km : ℝ → ℝ} {t T : ℝ}
    (_ht : 0 < t) (_htT : t < T) (_hp : ContinuousOn kp (Icc 0 T))
    (_hm : ContinuousOn km (Icc 0 T))
    (_hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x),
    0 < R.readout () ⟨kp, ⟨km, T⟩⟩ t

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hlt := h (witnessSpectrum.{u}) (t := 1) (T := 2) (by norm_num) (by norm_num)
    witnessPlus_continuous.continuousOn witnessMinus_continuous.continuousOn
    (fun x _ => witness_difference x)
  exact (lt_irrefl (0 : ℝ)) hlt

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨witnessPlus, ⟨witnessMinus, 2⟩⟩, 1, 0, ?_⟩
  change (∫ x in 0..1, centered witnessPlus 2 x - centered witnessMinus 2 x) ≠
    (∫ x in 0..0, centered witnessPlus 2 x - centered witnessMinus 2 x)
  rw [intervalIntegral.integral_same]
  exact (witnessSpectrum.{0}.centered_prefix_pos
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    witnessPlus_continuous.continuousOn witnessMinus_continuous.continuousOn
    (fun x _ => witness_difference x)).ne'

def family : Registration arena.{u} (type_of% (@BalancedSpectrum.centered_prefix_pos.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@BalancedSpectrum.centered_prefix_pos.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.centered_prefix_pos.{u}) (Realization signature) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.centered_prefix_pos.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.CenteredPrefix.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t =>
    ∫ x in 0..t, centered q.1 q.2.2 x - centered q.2.1 q.2.2 x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CenteredPrefix

namespace MidpointOptimalGap

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ _ : ℝ → ℝ, ℝ) (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q input => response q.1 q.2 input) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q input => response q.1 q.2 input + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι) {kp km : ℝ → ℝ} {T : ℝ}
    (_hT : 0 < T) (_hp : ContinuousOn kp (Icc 0 T)) (_hm : ContinuousOn km (Icc 0 T))
    (_hmp : AntitoneOn kp (Icc 0 T)) (_hmm : AntitoneOn km (Icc 0 T))
    (_hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x),
    Admissible T (midpointPulse T) ∧
    (∀ input, Admissible T input →
      R.readout () ⟨kp, T⟩ input ≤ response kp T (midpointPulse T) ∧
      response km T input ≤ response km T (midpointPulse T)) ∧
    response kp T (midpointPulse T) - response km T (midpointPulse T) =
      2 * S.primitive (T / 2) - S.primitive T ∧
    0 < 2 * S.primitive (T / 2) - S.primitive T

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨hadmissible, hmax, _⟩ := h (witnessSpectrum.{u}) (T := 1) (by norm_num)
    witnessPlus_continuous.continuousOn witnessMinus_continuous.continuousOn
    (witnessPlus_strictAnti.antitone.antitoneOn _) (witnessMinus_antitone.antitoneOn _)
    (fun x _ => witness_difference x)
  have hle := (hmax (midpointPulse 1) hadmissible).1
  change response witnessPlus 1 (midpointPulse 1) + 1 ≤
    response witnessPlus 1 (midpointPulse 1) at hle
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨fun _ => 1, 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change response (fun _ => 1) 1 (fun _ => 0) ≠ response (fun _ => 1) 1 (fun _ => 1)
  norm_num [response]

def family : Registration arena.{u} (type_of% (@BalancedSpectrum.midpoint_optimal_gap.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@BalancedSpectrum.midpoint_optimal_gap.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.midpoint_optimal_gap.{u}) (Realization signature) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.midpoint_optimal_gap.__information_unit
  realizationName :=
    `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.MidpointOptimalGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q input => response q.1 q.2 input)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MidpointOptimalGap

namespace CenteredStopLoss

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ _ : ℝ → ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q z => stopLoss (centered q.1 q.2) q.2 z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι) {kp km : ℝ → ℝ} {T z : ℝ}
    (_hT : 0 < T) (_hp : ContinuousOn kp (Icc 0 T)) (_hm : ContinuousOn km (Icc 0 T))
    (_hmm : AntitoneOn km (Icc 0 T))
    (_hd : ∀ x ∈ Icc 0 T, kp x - km x = S.difference x)
    (_hlo : centered kp T T < z) (_hhi : z < centered kp T 0),
    stopLoss (centered km T) T z < R.readout () ⟨kp, T⟩ z

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let z := (centered witnessPlus 1 1 + centered witnessPlus 1 0) / 2
  have hends : centered witnessPlus 1 1 < centered witnessPlus 1 0 :=
    sub_lt_sub_right (witnessPlus_strictAnti (by norm_num : (0 : ℝ) < 1)) _
  have hlt := h (witnessSpectrum.{u}) (T := 1) (z := z) (by norm_num)
    witnessPlus_continuous.continuousOn witnessMinus_continuous.continuousOn
    (witnessMinus_antitone.antitoneOn _) (fun x _ => witness_difference x)
    (by dsimp [z]; linarith) (by dsimp [z]; linarith)
  change stopLoss (centered witnessMinus 1) 1 z < 0 at hlt
  have hnonneg : 0 ≤ stopLoss (centered witnessMinus 1) 1 z :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => le_max_right _ _)
  exact (not_lt_of_ge hnonneg) hlt

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨fun _ => 0, 1⟩, -1, 0, ?_⟩
  change stopLoss (centered (fun _ => 0) 1) 1 (-1) ≠
    stopLoss (centered (fun _ => 0) 1) 1 0
  norm_num [stopLoss, centered]

def family : Registration arena.{u} (type_of% (@BalancedSpectrum.centered_stopLoss_lt.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@BalancedSpectrum.centered_stopLoss_lt.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.centered_stopLoss_lt.{u}) (Realization signature) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.centered_stopLoss_lt.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.CenteredStopLoss.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q z => stopLoss (centered q.1 q.2) q.2 z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CenteredStopLoss

namespace Primitive

def actual : Realization signature.{u} :=
  realize signature (fun _ q t => q.2.primitive t) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ q t => q.2.primitive t + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι) (t : ℝ),
    R.readout () ⟨ι, S⟩ t = ∑ i ∈ S.modes, S.weight i / S.rate i *
      (Real.exp (-(S.rate i * t)) - Real.exp (-(S.fastRate * t)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have heq : (witnessSpectrum.{u}).primitive 0 + 1 = (witnessSpectrum.{u}).primitive 0 :=
    (h (witnessSpectrum.{u}) 0).trans ((witnessSpectrum.{u}).primitive_eq 0).symm
  linarith

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  cases i
  refine ⟨⟨PUnit.{u + 1}, witnessSpectrum⟩, 1, 0, ?_⟩
  change (witnessSpectrum.{u}).primitive 1 ≠ (witnessSpectrum.{u}).primitive 0
  have hzero : (witnessSpectrum.{u}).primitive 0 = 0 := intervalIntegral.integral_same
  rw [hzero, BalancedSpectrum.primitive_eq]
  have h := Real.exp_lt_exp.mpr (by norm_num : -(2 : ℝ) < -1)
  simpa [witnessSpectrum] using (sub_pos.mpr h).ne'

def family : Registration arena.{u} (type_of% (@BalancedSpectrum.primitive_eq.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@BalancedSpectrum.primitive_eq.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.primitive_eq.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.primitive_eq.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.Primitive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t => q.2.primitive t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Primitive

namespace PrimitiveDiv

def rejected : Realization signature.{u} :=
  realize signature (fun _ q t => q.2.primitive t / t + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} (S : BalancedSpectrum ι) {t : ℝ} (_ht : t ≠ 0),
    R.readout () ⟨ι, S⟩ t = ∑ i ∈ S.modes, S.weight i / S.rate i *
      (∫ r in S.rate i..S.fastRate, Real.exp (-(r * t)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have ht : (1 : ℝ) ≠ 0 := one_ne_zero
  have heq : (witnessSpectrum.{u}).primitive 1 / 1 + 1 =
      (witnessSpectrum.{u}).primitive 1 / 1 :=
    (h (witnessSpectrum.{u}) ht).trans ((witnessSpectrum.{u}).primitive_div_eq ht).symm
  linarith

def family : Registration arena.{u} (type_of% (@BalancedSpectrum.primitive_div_eq.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@BalancedSpectrum.primitive_div_eq.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@BalancedSpectrum.primitive_div_eq.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `NeumannCenteredOrder.BalancedSpectrum.primitive_div_eq.__information_unit
  realizationName := `Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder.PrimitiveDiv.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t => q.2.primitive t / t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimitiveDiv


end
end Reg.D5.S3.Analytic.ExponentialSum.NeumannCenteredOrder

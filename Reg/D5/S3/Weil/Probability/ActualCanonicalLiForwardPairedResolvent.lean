import D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The actual degree-dependent Li readouts and their complete source laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent

open _root_.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
open _root_.D5.S3.Zeros.CompletedZeta
open _root_.D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev HalfFree := ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0

abbrev coefficientSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e)

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change canonicalLiCoefficient 0 ≠ canonicalLiCoefficient 1
  rw [canonical_li_zero]
  exact ne_of_lt canonical_li_one_pos

namespace Equality

abbrev arena : Arena where
  signature := coefficientSignature
  Law R := ∀ n : ℕ, n = 0 ∨ HalfFree → R.readout () () n = pairSum n

def rejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 (.inl rfl)
  change (1 : ℝ) = pairSum 0 at hz
  have hzero := canonicalLiCoefficient_eq_actual_pairSum 0 (.inl rfl)
  rw [canonical_li_zero] at hzero
  rw [← hzero] at hz
  exact one_ne_zero hz

def family : Registration arena (type_of% @canonicalLiCoefficient_eq_actual_pairSum) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@canonicalLiCoefficient_eq_actual_pairSum, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual rejected rejectedLaw
  dependence := coefficientDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonicalLiCoefficient_eq_actual_pairSum) (Realization coefficientSignature) Unit Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.canonicalLiCoefficient_eq_actual_pairSum.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.Equality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equality

namespace ForwardEnvelope

abbrev arena : Arena where
  signature := coefficientSignature
  Law R := ∀ n : ℕ, n = 0 ∨ HalfFree →
    R.readout () () n ∈ Set.Icc 0 (canonicalLiCoefficient 1 * (n : ℝ) ^ 2)

def rejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hneg := (h 0 (.inl rfl)).1
  change (0 : ℝ) ≤ -1 at hneg
  norm_num at hneg

def family : Registration arena (type_of% @canonical_li_forward_fixed_quadratic) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@canonical_li_forward_fixed_quadratic, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual rejected rejectedLaw
  dependence := coefficientDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonical_li_forward_fixed_quadratic) (Realization coefficientSignature) Unit Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.canonical_li_forward_fixed_quadratic.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.ForwardEnvelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ForwardEnvelope

namespace NonnegativeCriterion

abbrev arena : Arena where
  signature := coefficientSignature
  Law R := RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ R.readout () () n

def rejected : Realization coefficientSignature := by
  classical
  exact realize coefficientSignature (fun _ _ _ => if RiemannHypothesis then -1 else 0)
    (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  classical
  intro h
  by_cases hrh : RiemannHypothesis
  · have hn := h.mp hrh 0
    change (0 : ℝ) ≤ if RiemannHypothesis then -1 else 0 at hn
    norm_num [hrh] at hn
  · apply hrh
    apply h.mpr
    intro n
    change (0 : ℝ) ≤ if RiemannHypothesis then -1 else 0
    simp [hrh]

def family : Registration arena (type_of% @rh_iff_canonical_li_nonnegative) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_canonical_li_nonnegative, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual rejected rejectedLaw
  dependence := coefficientDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_canonical_li_nonnegative) (Realization coefficientSignature) Unit Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_nonnegative.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.NonnegativeCriterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end NonnegativeCriterion

namespace EnvelopeCriterion

abbrev arena : Arena where
  signature := coefficientSignature
  Law R := RiemannHypothesis ↔ ∀ n : ℕ,
    R.readout () () n ∈ Set.Icc 0 (canonicalLiCoefficient 1 * (n : ℝ) ^ 2)

def rejected : Realization coefficientSignature := by
  classical
  exact realize coefficientSignature (fun _ _ _ => if RiemannHypothesis then -1 else 0)
    (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  classical
  intro h
  by_cases hrh : RiemannHypothesis
  · have hn := (h.mp hrh 0).1
    change (0 : ℝ) ≤ if RiemannHypothesis then -1 else 0 at hn
    norm_num [hrh] at hn
  · apply hrh
    apply h.mpr
    intro n
    change (if RiemannHypothesis then -1 else 0 : ℝ) ∈ Set.Icc 0
      (canonicalLiCoefficient 1 * (n : ℝ) ^ 2)
    rw [ite_eq_right hrh]
    exact ⟨le_rfl, mul_nonneg canonical_li_one_pos.le (sq_nonneg _)⟩

def family : Registration arena (type_of% @rh_iff_canonical_li_fixed_quadratic) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_canonical_li_fixed_quadratic, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law coefficientActual rejected rejectedLaw
  dependence := coefficientDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_canonical_li_fixed_quadratic) (Realization coefficientSignature) Unit Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.rh_iff_canonical_li_fixed_quadratic.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.EnvelopeCriterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ _ n => canonicalLiCoefficient n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EnvelopeCriterion

namespace Summability

open _root_.D5.S3.Weil.ZeroSum
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open Complex

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ n i => pairCoefficient n i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Summable (fun i : ℕ => |R.readout () n i|)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa only [rejected, realize, abs_one] using h 0
  have : Finite ℕ := Finite.of_summable_const zero_lt_one hs
  exact not_finite ℕ

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let Z := zetaZeroData
  have hne : (Z.gamma 0).re ≠ 0 := by
    have hn := _root_.D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero
      Z 0 (Z.zero_isNontrivial 0)
    have heq : (Z.gamma 0).re = (Z.zero 0).im := by
      simp [ZeroData.gamma, spectralParameter, _root_.D5.S3.Weil.Convention.criticalAbscissa]
    rwa [heq]
  obtain ⟨i, hi⟩ : ∃ i : ℕ, 0 < (Z.gamma i).re := by
    by_cases h : 0 < (Z.gamma 0).re
    · exact ⟨0, h⟩
    · refine ⟨Z.reflection 0, ?_⟩
      rw [Z.gamma_reflection, Complex.neg_re]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hne)
  refine ⟨1, i, Z.reflection i, ?_⟩
  change pairCoefficient 1 i ≠ pairCoefficient 1 (Z.reflection i)
  have href : ¬ 0 < (Z.gamma (Z.reflection i)).re := by
    rw [Z.gamma_reflection, Complex.neg_re]
    linarith
  have hp : 0 < (Z.zero i).re := (Z.zero_isNontrivial i).2.1
  have hrepr : pairCoefficient 1 i = 2 * Z.multiplicity i *
      ((Z.zero i).re / Complex.normSq (Z.zero i)) := by
    unfold pairCoefficient zeroRatio
    rw [ite_eq_left hi, pow_one, Complex.sub_re, Complex.one_re, one_div,
      Complex.inv_re, sub_sub_cancel]
  have hpos : 0 < pairCoefficient 1 i := by
    rw [hrepr]
    exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (Z.multiplicity_pos i)))
      (div_pos hp (Complex.normSq_pos.mpr (fun hzero => by simp [hzero] at hp)))
  have hz : pairCoefficient 1 (Z.reflection i) = 0 := by
    exact ite_eq_right href
  rw [hz]
  exact ne_of_gt hpos

def family : Registration arena (type_of% @pairCoefficient_abs_summable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pairCoefficient_abs_summable, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pairCoefficient_abs_summable) (Realization signature) ℕ Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.pairCoefficient_abs_summable.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent.Summability.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ n i => pairCoefficient n i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Summability

end Reg.D5.S3.Weil.Probability.ActualCanonicalLiForwardPairedResolvent

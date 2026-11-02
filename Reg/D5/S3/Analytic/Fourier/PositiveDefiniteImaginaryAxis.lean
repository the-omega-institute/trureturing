import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
open _root_.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Finset Complex
open scoped BigOperators
open scoped ComplexOrder
noncomputable section

abbrev momentSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def momentActual : Realization momentSignature :=
  realize momentSignature (fun _ _ m => m) (fun e => nomatch e)

def momentRejected : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev momentArena : Arena where
  signature := momentSignature
  Law R := ∀ (k m : ℕ), m ≤ 2 * k →
    (∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      ((-1 : ℝ) ^ i * k.choose i) * ((-1 : ℝ) ^ j * k.choose j) *
        ((i : ℝ) - j) ^ (R.readout () () m)) =
      if m = 2 * k then (-1 : ℝ) ^ k * (2 * k).factorial else 0

private theorem momentArenaRejected : ¬ momentArena.Law momentRejected := by
  intro h
  have he := h 1 2 (by omega)
  norm_num [momentRejected, realize, Finset.sum_range_succ] at he

private theorem momentArenaDependence : ObservationalDependence momentSignature momentActual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [momentActual, realize]⟩

def momentArenaSource : Registration momentArena (type_of% @finite_difference_moment) where
  actual := momentActual
  bridge := Iff.rfl
  variation := ⟨finite_difference_moment, momentRejected, momentArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨momentRejected, ?_, rfl, momentArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := momentArenaDependence

def momentAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_difference_moment) (Realization momentSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.momentAuditUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.momentArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨momentArena⟩
  objectArena := .source ⟨momentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source momentArena ⟨momentArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms momentAudit

abbrev radiusSignature : Signature where
  Params := ℂ → ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def radiusActual : Realization radiusSignature :=
  realize radiusSignature (fun _ F y => F ((y : ℂ) * Complex.I)) (fun e => nomatch e)

def radiusRejected : Realization radiusSignature :=
  realize radiusSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev radiusArena : Arena where
  signature := radiusSignature
  Law Q := ∀ {f : ℝ → ℂ}
    (hf : _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite f)
    (hreal : ∀ x, (f x).im = 0) {F : ℂ → ℂ} {R : ℝ}
    (hF : DifferentiableOn ℂ F (Metric.ball 0 R))
    (hFf : ∀ x : ℝ, |x| < R → F x = f x) {y : ℝ}
    (hy0 : 0 ≤ y) (hyR : y < R),
    (f 0).re ≤ (Q.readout () F y).re

private theorem radiusArenaRejected : ¬ radiusArena.Law radiusRejected := by
  intro h
  have hp : _root_.D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun _ => (0 : ℂ)) := fun m x => _root_.Matrix.PosSemidef.zero
  have he := @h (fun _ => 0) hp (fun _ => rfl) (fun _ => 0) 1
    (by fun_prop) (fun _ _ => rfl) 0 (by norm_num) (by norm_num)
  change (0 : ℝ) ≤ (-1 : ℂ).re at he
  norm_num at he

private theorem radiusArenaDependence : ObservationalDependence radiusSignature radiusActual := by
  intro i
  refine ⟨id, 0, 1, ?_⟩
  intro he
  have hi := congrArg Complex.im he
  norm_num [radiusActual, realize] at hi

def radiusArenaSource : Registration radiusArena (type_of% @le_re_of_positiveDefinite) where
  actual := radiusActual
  bridge := Iff.rfl
  variation := ⟨le_re_of_positiveDefinite, radiusRejected, radiusArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨radiusRejected, ?_, rfl, radiusArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := radiusArenaDependence

def radiusAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@le_re_of_positiveDefinite) (Realization radiusSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.radiusAuditUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.radiusArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨radiusArena⟩
  objectArena := .source ⟨radiusArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source radiusArena ⟨radiusArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize radiusSignature (fun _ F y => F ((y : ℂ) * Complex.I)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms radiusAudit


/-- Full real-function state and output for the binomial stencil identities. -/
abbrev shiftSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ → ℝ) (fun _ => ℝ → ℝ)

def shiftActual : Realization shiftSignature :=
  realize shiftSignature (fun _ _ g => g) (fun e => nomatch e)

def shiftRejected : Realization shiftSignature :=
  realize shiftSignature (fun _ _ _ => fun _ => 0) (fun e => nomatch e)

def shiftArena : Arena where
  signature := shiftSignature
  Law R := ∀ (k : ℕ) (g : ℝ → ℝ) (x : ℝ),
    ∑ j ∈ range (k + 1), weight k j * g (x + j) =
      (-1 : ℝ) ^ k * (fwdDiff (1 : ℝ))^[k] (R.readout () () g) x

def doubleShiftArena : Arena where
  signature := shiftSignature
  Law R := ∀ (k : ℕ) (g : ℝ → ℝ),
    ∑ i ∈ range (k + 1), ∑ j ∈ range (k + 1),
      weight k i * weight k j * g ((i : ℝ) - j) =
      (-1 : ℝ) ^ k * (fwdDiff (1 : ℝ))^[2 * k] (R.readout () () g) (-(k : ℝ))

private theorem shiftRejectedLaw : ¬ shiftArena.Law shiftRejected := by
  intro h
  have hzero := h 0 (fun _ => 1) 0
  norm_num [shiftRejected, realize, weight] at hzero

private theorem doubleShiftRejectedLaw : ¬ doubleShiftArena.Law shiftRejected := by
  intro h
  have hzero := h 0 (fun _ => 1)
  norm_num [shiftRejected, realize, weight] at hzero

private theorem shiftDependence : ObservationalDependence shiftSignature shiftActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hzero := congrFun h 0
  norm_num [shiftActual, realize] at hzero

def shiftArenaSource : Registration shiftArena (type_of% @weighted_shift) where
  actual := shiftActual
  bridge := Iff.rfl
  variation := ⟨weighted_shift, shiftRejected, shiftRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    shiftArena.Law shiftActual shiftRejected shiftRejectedLaw
  dependence := shiftDependence

def doubleShiftArenaSource : Registration doubleShiftArena (type_of% @double_weighted_shift) where
  actual := shiftActual
  bridge := Iff.rfl
  variation := ⟨double_weighted_shift, shiftRejected, doubleShiftRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    doubleShiftArena.Law shiftActual shiftRejected doubleShiftRejectedLaw
  dependence := shiftDependence

def shiftAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_shift) (Realization shiftSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.weighted_shift.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.shiftArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena⟩
  objectArena := .source ⟨shiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena ⟨shiftArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize shiftSignature (fun _ _ g => g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def doubleShiftAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@double_weighted_shift) (Realization shiftSignature) Unit Unit where
  unitName := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.double_weighted_shift.__information_unit
  realizationName := `Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.doubleShiftArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨doubleShiftArena⟩
  objectArena := .source ⟨doubleShiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source doubleShiftArena ⟨doubleShiftArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize shiftSignature (fun _ _ g => g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
import Reg.Support.SingleDependentReadout

/-! The source observation is the whole-line frequency integral on the right of Parseval. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory Set
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence (halfLineMellin mobiusPartialSum)
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval

namespace Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ g => integral volume g) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ g => integral volume g + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R :=
    IntegrableOn
      (fun x : ℝ => (mobiusPartialSum x - mobiusPartialSum (2 * x)) ^ 2 * x⁻¹) (Ioi 1) ∧
    Integrable (fun ξ : ℝ =>
      ‖mobiusDyadicMellinSymbol (((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ∧
    (∫ x in Ioi (1 : ℝ), (mobiusPartialSum x - mobiusPartialSum (2 * x)) ^ 2 * x⁻¹) =
      R.readout () () (fun ξ : ℝ =>
        ‖mobiusDyadicMellinSymbol (((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h.2.2
  change (∫ x in Ioi (1 : ℝ), (mobiusPartialSum x - mobiusPartialSum (2 * x)) ^ 2 * x⁻¹) =
    (∫ ξ : ℝ, ‖mobiusDyadicMellinSymbol (((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) + 1 at hbad
  linarith only [hbad, mobiusDyadicDifference_unitWeight_parseval.2.2]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (Icc (0 : ℝ) 1).indicator 1, ?_⟩
  change (∫ _ : ℝ, (0 : ℝ)) ≠ ∫ ξ : ℝ, (Icc (0 : ℝ) 1).indicator 1 ξ
  rw [integral_zero, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc]
  norm_num

def family : Registration arena (type_of% @mobiusDyadicDifference_unitWeight_parseval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mobiusDyadicDifference_unitWeight_parseval, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mobiusDyadicDifference_unitWeight_parseval) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval.mobiusDyadicDifference_unitWeight_parseval.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ g => integral volume g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace PositiveMellin

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℂ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ s transform => transform s) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ s transform => transform s + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {s : ℂ}, 0 < s.re →
    R.readout () s
        (halfLineMellin (fun x => ((mobiusPartialSum x - mobiusPartialSum (2 * x) : ℝ) : ℂ))) =
      mobiusDyadicMellinSymbol s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : 0 < (1 : ℂ).re := by norm_num
  have hbad := h hs
  change halfLineMellin (fun x => ((mobiusPartialSum x - mobiusPartialSum (2 * x) : ℝ) : ℂ)) 1 + 1 =
    mobiusDyadicMellinSymbol 1 at hbad
  rw [halfLineMellin_dyadic hs] at hbad
  exact one_ne_zero (add_left_cancel (hbad.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  exact zero_ne_one

def family : Registration arena (type_of% @halfLineMellin_dyadic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@halfLineMellin_dyadic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@halfLineMellin_dyadic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval.halfLineMellin_dyadic.audit
  realizationName := `Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval.PositiveMellin.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s transform => transform s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PositiveMellin

end Reg.D5.S3.Weil.ZetaPntBounds.MobiusDyadicUnitWeightParseval

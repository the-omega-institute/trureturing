import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.WallisRemainder.Measure
import Reg.D5.S3.Analytic.WallisRemainder.Laplace
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.WallisRemainder.Measure
open _root_.D5.S3.Analytic.WallisRemainder.Defs
open _root_.D5.S3.Analytic.WallisRemainder.Measure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory Set
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev logarithmSignature := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmSignature
abbrev logarithmActual := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmActual
abbrev logarithmRejected := _root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmRejected

abbrev stieltjesArena : Arena where
  signature := logarithmSignature
  Law R := ∀ {x : ℝ}, 0 < x → R.readout () () x = x / 8 * ∫ v, 1 / (x ^ 2 + v) ∂P

private theorem stieltjesRejected : ¬ stieltjesArena.Law logarithmRejected := by
  intro h
  have h0 := h (x := 1) zero_lt_one
  change 0 = _ at h0
  have h1 := r_eq_stieltjes (x := 1) zero_lt_one
  linarith [_root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmPositive (x := 1) zero_lt_one]

private theorem logarithmDependence : ObservationalDependence logarithmSignature logarithmActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change -Real.log (wallisB 0) ≠ -Real.log (wallisB 1)
  rw [show wallisB 0 = 0 by simp [wallisB], Real.log_zero, neg_zero]
  exact (_root_.Reg.D5.S3.Analytic.WallisRemainder.Laplace.logarithmPositive (x := 1) zero_lt_one).ne

def stieltjesFamily : Registration stieltjesArena (type_of% @r_eq_stieltjes) where
  actual := logarithmActual
  bridge := Iff.rfl
  variation := ⟨r_eq_stieltjes, logarithmRejected, stieltjesRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    stieltjesArena.Law logarithmActual logarithmRejected stieltjesRejected
  dependence := logarithmDependence

def stieltjesAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@r_eq_stieltjes) (Realization logarithmSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.stieltjesUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.stieltjesFamily
  realizationSource := none
  generated := false
  arena := .source ⟨stieltjesArena⟩
  objectArena := .source ⟨stieltjesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source stieltjesArena ⟨stieltjesFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logarithmSignature (fun _ _ x => -Real.log (wallisB x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
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

abbrev weightSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ _ n => spectralWeight n) (fun e => nomatch e)

def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law R := HasSum (R.readout () ()) 1

private theorem weightNegative : ¬ weightArena.Law weightRejected := by
  intro h
  have he := (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).unique h
  norm_num at he

private theorem weightDependence : ObservationalDependence weightSignature weightActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change spectralWeight 0 ≠ spectralWeight 1
  norm_num [spectralWeight]
  intro h
  field_simp at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

def weightFamily : Registration weightArena (type_of% @hasSum_spectralWeight) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨hasSum_spectralWeight, weightRejected, weightNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    weightArena.Law weightActual weightRejected weightNegative
  dependence := weightDependence

abbrev fractionSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ) (fun _ => ℝ)

def fractionActual : Realization fractionSignature :=
  realize fractionSignature
    (fun _ u n => 8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * u ^ 2))
    (fun e => nomatch e)

def fractionRejected : Realization fractionSignature :=
  realize fractionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev fractionArena : Arena where
  signature := fractionSignature
  Law R := ∀ {u : ℝ}, 0 < u → HasSum (R.readout () u) (Real.tanh u / u)

private theorem fractionNegative : ¬ fractionArena.Law fractionRejected := by
  intro h
  have he := (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0).unique
    (h (u := 1) zero_lt_one)
  have hp : 0 < Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr zero_lt_one) (Real.cosh_pos _)
  norm_num at he
  linarith

private theorem fractionDependence : ObservationalDependence fractionSignature fractionActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [fractionActual, realize]
  intro h
  field_simp at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

def fractionFamily : Registration fractionArena (type_of% @tanh_div_hasSum) where
  actual := fractionActual
  bridge := Iff.rfl
  variation := ⟨tanh_div_hasSum, fractionRejected, fractionNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    fractionArena.Law fractionActual fractionRejected fractionNegative
  dependence := fractionDependence

abbrev biasSignature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def biasActual : Realization biasSignature :=
  realize biasSignature (fun _ _ f => ∫ v, f v ∂Q) (fun e => nomatch e)

def biasRejected : Realization biasSignature :=
  realize biasSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev biasArena : Arena where
  signature := biasSignature
  Law R := ∀ (f : ℝ → ℝ), R.readout () () f = 24 * ∫ v, v * f v ∂P

private theorem biasNegative : ¬ biasArena.Law biasRejected := by
  intro h
  have he := h (fun _ => 1)
  norm_num [biasRejected, realize, integral_P_id] at he

private theorem biasDependence : ObservationalDependence biasSignature biasActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  norm_num [biasActual, realize]

def biasFamily : Registration biasArena (type_of% @integral_Q) where
  actual := biasActual
  bridge := Iff.rfl
  variation := ⟨integral_Q, biasRejected, biasNegative⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    biasArena.Law biasActual biasRejected biasNegative
  dependence := biasDependence

def weightAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@hasSum_spectralWeight) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.weightUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.weightFamily
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ _ n => spectralWeight n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fractionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tanh_div_hasSum) (Realization fractionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.fractionUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.fractionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fractionArena⟩
  objectArena := .source ⟨fractionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fractionArena ⟨fractionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fractionSignature (fun _ u n => 8 / (Real.pi ^ 2 * (2 * (n : ℝ) + 1) ^ 2 + 4 * u ^ 2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def biasAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@integral_Q) (Realization biasSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.biasUnit
  realizationName := `Reg.D5.S3.Analytic.WallisRemainder.Measure.biasFamily
  realizationSource := none
  generated := false
  arena := .source ⟨biasArena⟩
  objectArena := .source ⟨biasArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source biasArena ⟨biasFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize biasSignature (fun _ _ f => ∫ v, f v ∂Q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.WallisRemainder.Measure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.WallisRemainder.Measure

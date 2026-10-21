import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for ordered trigonometric coefficients. -/

namespace Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section

abbrev baseSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℕ) (fun _ => ℝ)

def baseActual : Realization baseSignature :=
  realize baseSignature (fun _ m l => Real.cos ((l : ℝ) * angle m)) (fun e => nomatch e)

def baseRejected : Realization baseSignature :=
  realize baseSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev baseArena : Arena where
  signature := baseSignature
  Law R := ∀ {m l : ℕ}, 1 ≤ l → l ≤ m → 0 < R.readout () m l ∧ R.readout () m l < 1

private theorem baseRejected_law : ¬ baseArena.Law baseRejected := by
  intro h
  have he := h (m := 1) (l := 1) (by omega) (by omega)
  norm_num [baseRejected, realize] at he

private theorem baseDependence : ObservationalDependence baseSignature baseActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [baseActual, realize, angle, Real.cos_pi_div_three]

def baseSource : Registration baseArena (type_of% @cosine_base_bounds) where
  actual := baseActual
  bridge := Iff.rfl
  variation := ⟨cosine_base_bounds, baseRejected, baseRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    baseArena.Law baseActual baseRejected baseRejected_law
  dependence := baseDependence

def baseAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cosine_base_bounds) (Realization baseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.baseUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.baseSource
  realizationSource := none
  generated := false
  arena := .source ⟨baseArena⟩
  objectArena := .source ⟨baseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source baseArena ⟨baseSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize baseSignature (fun _ m l => Real.cos ((l : ℝ) * angle m))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev decreasingSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℕ) (fun _ => ℝ)

def decreasingActual : Realization decreasingSignature :=
  realize decreasingSignature (fun _ m l => Real.cos ((l : ℝ) * angle m)) (fun e => nomatch e)

def decreasingRejected : Realization decreasingSignature :=
  realize decreasingSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev decreasingArena : Arena where
  signature := decreasingSignature
  Law R := ∀ {m a b : ℕ}, 1 ≤ a → a < b → b ≤ m → R.readout () m b < R.readout () m a

private theorem decreasingRejected_law : ¬ decreasingArena.Law decreasingRejected := by
  intro h
  have he := h (m := 2) (a := 1) (b := 2) (by omega) (by omega) (by omega)
  norm_num [decreasingRejected, realize] at he

private theorem decreasingDependence : ObservationalDependence decreasingSignature decreasingActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  norm_num [decreasingActual, realize, angle, Real.cos_pi_div_three]

def decreasingSource : Registration decreasingArena (type_of% @cosine_base_strictAnti) where
  actual := decreasingActual
  bridge := Iff.rfl
  variation := ⟨cosine_base_strictAnti, decreasingRejected, decreasingRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    decreasingArena.Law decreasingActual decreasingRejected decreasingRejected_law
  dependence := decreasingDependence

def decreasingAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cosine_base_strictAnti) (Realization decreasingSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.decreasingUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.decreasingSource
  realizationSource := none
  generated := false
  arena := .source ⟨decreasingArena⟩
  objectArena := .source ⟨decreasingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source decreasingArena ⟨decreasingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize decreasingSignature (fun _ m l => Real.cos ((l : ℝ) * angle m))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev logarithmSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℕ) (fun _ => ℝ)

def logarithmActual : Realization logarithmSignature :=
  realize logarithmSignature (fun _ m l => Real.log (Real.cos ((l : ℝ) * angle m))) (fun e => nomatch e)

def logarithmRejected : Realization logarithmSignature :=
  realize logarithmSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev logarithmArena : Arena where
  signature := logarithmSignature
  Law R := ∀ {m a b : ℕ}, 1 ≤ a → a < b → b ≤ m → R.readout () m b < R.readout () m a ∧ R.readout () m a < 0

private theorem logarithmRejected_law : ¬ logarithmArena.Law logarithmRejected := by
  intro h
  have he := h (m := 2) (a := 1) (b := 2) (by omega) (by omega) (by omega)
  norm_num [logarithmRejected, realize] at he

private theorem logarithmDependence : ObservationalDependence logarithmSignature logarithmActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  have hn := (cosine_base_bounds (m := 1) (l := 1) (by omega) (by omega))
  have hl := Real.log_neg hn.1 hn.2
  simpa only [logarithmActual, realize, Nat.cast_zero, zero_mul, Real.cos_zero, Real.log_one] using hl.ne.symm

def logarithmSource : Registration logarithmArena (type_of% @logarithmic_exponent_order) where
  actual := logarithmActual
  bridge := Iff.rfl
  variation := ⟨logarithmic_exponent_order, logarithmRejected, logarithmRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    logarithmArena.Law logarithmActual logarithmRejected logarithmRejected_law
  dependence := logarithmDependence

def logarithmAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@logarithmic_exponent_order) (Realization logarithmSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.logarithmUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.logarithmSource
  realizationSource := none
  generated := false
  arena := .source ⟨logarithmArena⟩
  objectArena := .source ⟨logarithmArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logarithmArena ⟨logarithmSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logarithmSignature (fun _ m l => Real.log (Real.cos ((l : ℝ) * angle m)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gapSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def gapActual : Realization gapSignature :=
  realize gapSignature (fun _ p r => modeValue p.1 p.2.1 r - modeValue p.1 (p.2.1 + p.2.2) r) (fun e => nomatch e)

def gapRejected : Realization gapSignature :=
  realize gapSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev gapArena : Arena where
  signature := gapSignature
  Law R := ∀ (m j d : ℕ) (r : ℝ), R.readout () ⟨m, j, d⟩ r = 4 * ∑ l ∈ Finset.Icc 1 m, Real.sin (((2 * j + d : ℕ) : ℝ) * (l : ℝ) * angle m) * Real.sin ((d : ℝ) * (l : ℝ) * angle m) * Real.cos ((l : ℝ) * angle m) ^ r

private theorem gapRejected_law : ¬ gapArena.Law gapRejected := by
  intro h
  have he := h 0 0 0 0
  norm_num [gapRejected, realize] at he

private theorem gapDependence : ObservationalDependence gapSignature gapActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, 0, 2, ?_⟩
  norm_num [gapActual, realize, modeValue, angle, Finset.sum_Icc_succ_top, Real.rpow_natCast, Real.cos_pi_div_three, Real.cos_two_mul]

def gapSource : Registration gapArena (type_of% @modeValue_sub) where
  actual := gapActual
  bridge := Iff.rfl
  variation := ⟨modeValue_sub, gapRejected, gapRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gapArena.Law gapActual gapRejected gapRejected_law
  dependence := gapDependence

def gapAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_sub) (Realization gapSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.gapUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.gapSource
  realizationSource := none
  generated := false
  arena := .source ⟨gapArena⟩
  objectArena := .source ⟨gapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapArena ⟨gapSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapSignature (fun _ p r => modeValue p.1 p.2.1 r - modeValue p.1 (p.2.1 + p.2.2) r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev shortSineSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def shortSineActual : Realization shortSineSignature :=
  realize shortSineSignature (fun _ p l => Real.sin ((p.2 : ℝ) * (l : ℝ) * angle p.1)) (fun e => nomatch e)

def shortSineRejected : Realization shortSineSignature :=
  realize shortSineSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev shortSineArena : Arena where
  signature := shortSineSignature
  Law R := ∀ {m d l : ℕ}, (d = 1 ∨ d = 2) → 1 ≤ l → l ≤ m → 0 < R.readout () ⟨m, d⟩ l

private theorem shortSineRejected_law : ¬ shortSineArena.Law shortSineRejected := by
  intro h
  have he := h (m := 1) (d := 1) (l := 1) (Or.inl rfl) (by omega) (by omega)
  norm_num [shortSineRejected, realize] at he

private theorem shortSineDependence : ObservationalDependence shortSineSignature shortSineActual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1, ?_⟩
  have hp := gap_short_sine_pos (m := 1) (d := 1) (l := 1) (Or.inl rfl) (by omega) (by omega)
  simpa only [shortSineActual, realize, Nat.cast_zero, mul_zero, zero_mul, Real.sin_zero] using hp.ne

def shortSineSource : Registration shortSineArena (type_of% @gap_short_sine_pos) where
  actual := shortSineActual
  bridge := Iff.rfl
  variation := ⟨gap_short_sine_pos, shortSineRejected, shortSineRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    shortSineArena.Law shortSineActual shortSineRejected shortSineRejected_law
  dependence := shortSineDependence

def shortSineAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gap_short_sine_pos) (Realization shortSineSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.shortSineUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.shortSineSource
  realizationSource := none
  generated := false
  arena := .source ⟨shortSineArena⟩
  objectArena := .source ⟨shortSineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shortSineArena ⟨shortSineSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize shortSineSignature (fun _ p l => Real.sin ((p.2 : ℝ) * (l : ℝ) * angle p.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev modeCountSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ) (fun _ => ℕ) (fun _ => ℕ)

def modeCountActual : Realization modeCountSignature :=
  realize modeCountSignature (fun _ m j => List.signVariations (1 :: ((List.range' 1 m).map (fun (l : ℕ) => 2 * Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m))))) (fun e => nomatch e)

def modeCountRejected : Realization modeCountSignature :=
  realize modeCountSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev modeCountArena : Arena where
  signature := modeCountSignature
  Law R := ∀ {m j : ℕ}, 1 ≤ j → j ≤ m → R.readout () m j = j

private theorem modeCountRejected_law : ¬ modeCountArena.Law modeCountRejected := by
  intro h
  have he := h (m := 1) (j := 1) (by omega) (by omega)
  norm_num [modeCountRejected, realize] at he

private theorem modeCountDependence : ObservationalDependence modeCountSignature modeCountActual := by
  intro i
  cases i
  refine ⟨1, 0, 1, ?_⟩
  have h1 := mode_coefficients_signVariations (m := 1) (j := 1) (by omega) (by omega)
  dsimp only [modeCountActual, realize]
  rw [h1]
  norm_num [List.range'_succ, List.signVariations]

def modeCountSource : Registration modeCountArena (type_of% @mode_coefficients_signVariations) where
  actual := modeCountActual
  bridge := Iff.rfl
  variation := ⟨mode_coefficients_signVariations, modeCountRejected, modeCountRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    modeCountArena.Law modeCountActual modeCountRejected modeCountRejected_law
  dependence := modeCountDependence

def modeCountAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mode_coefficients_signVariations) (Realization modeCountSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.modeCountUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.modeCountSource
  realizationSource := none
  generated := false
  arena := .source ⟨modeCountArena⟩
  objectArena := .source ⟨modeCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modeCountArena ⟨modeCountSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeCountSignature (fun _ m j => List.signVariations (1 :: ((List.range' 1 m).map (fun (l : ℕ) => 2 * Real.cos (2 * (j : ℝ) * (l : ℝ) * angle m)))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev gapCountSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℕ)

def gapCountActual : Realization gapCountSignature :=
  realize gapCountSignature (fun _ p d => List.signVariations ((List.range' 1 p.1).map (fun (l : ℕ) => Real.sin (((2 * p.2 + d : ℕ) : ℝ) * (l : ℝ) * angle p.1) * Real.sin ((d : ℝ) * (l : ℝ) * angle p.1)))) (fun e => nomatch e)

def gapCountRejected : Realization gapCountSignature :=
  realize gapCountSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev gapCountArena : Arena where
  signature := gapCountSignature
  Law R := ∀ {m j d : ℕ}, 1 ≤ j → (d = 1 ∨ d = 2) → j + d ≤ m → R.readout () ⟨m, j⟩ d = j

private theorem gapCountRejected_law : ¬ gapCountArena.Law gapCountRejected := by
  intro h
  have he := h (m := 2) (j := 1) (d := 1) (by omega) (Or.inl rfl) (by omega)
  norm_num [gapCountRejected, realize] at he

private theorem gapCountDependence : ObservationalDependence gapCountSignature gapCountActual := by
  intro i
  cases i
  refine ⟨⟨2, 1⟩, 0, 1, ?_⟩
  have h1 := gap_coefficients_signVariations (m := 2) (j := 1) (d := 1) (by omega) (Or.inl rfl) (by omega)
  dsimp only [gapCountActual, realize]
  rw [h1]
  norm_num [List.range'_succ, List.signVariations]

def gapCountSource : Registration gapCountArena (type_of% @gap_coefficients_signVariations) where
  actual := gapCountActual
  bridge := Iff.rfl
  variation := ⟨gap_coefficients_signVariations, gapCountRejected, gapCountRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gapCountArena.Law gapCountActual gapCountRejected gapCountRejected_law
  dependence := gapCountDependence

def gapCountAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gap_coefficients_signVariations) (Realization gapCountSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.gapCountUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.gapCountSource
  realizationSource := none
  generated := false
  arena := .source ⟨gapCountArena⟩
  objectArena := .source ⟨gapCountArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapCountArena ⟨gapCountSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gapCountSignature (fun _ p d => List.signVariations ((List.range' 1 p.1).map (fun (l : ℕ) => Real.sin (((2 * p.2 + d : ℕ) : ℝ) * (l : ℝ) * angle p.1) * Real.sin ((d : ℝ) * (l : ℝ) * angle p.1))))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev phaseSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℝ)

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ p d => ((2 * p.2 + d : ℕ) : ℝ) * angle p.1)
    (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev phaseArena : Arena where
  signature := phaseSignature
  Law R := ∀ {m j d : ℕ}, 1 ≤ j → (d = 1 ∨ d = 2) → j + d ≤ m →
    0 < R.readout () ⟨m, j⟩ d ∧ R.readout () ⟨m, j⟩ d < Real.pi

private theorem phaseRejected_law : ¬ phaseArena.Law phaseRejected := by
  intro h
  have he := h (m := 2) (j := 1) (d := 1) (by omega) (Or.inl rfl) (by omega)
  norm_num [phaseRejected, realize] at he

private theorem phaseDependence : ObservationalDependence phaseSignature phaseActual := by
  intro i
  refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
  norm_num [phaseActual, realize, angle]
  exact ne_of_lt Real.pi_pos

def phaseSource : Registration phaseArena (type_of% @gap_first_phase_bounds) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨gap_first_phase_bounds, phaseRejected, phaseRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    phaseArena.Law phaseActual phaseRejected phaseRejected_law
  dependence := phaseDependence

def phaseAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gap_first_phase_bounds) (Realization phaseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.phaseUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges.phaseSource
  realizationSource := none
  generated := false
  arena := .source ⟨phaseArena⟩
  objectArena := .source ⟨phaseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phaseArena ⟨phaseSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phaseSignature
    (fun _ p d => ((2 * p.2 + d : ℕ) : ℝ) * angle p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.JainAbsCosine.TrigSignChanges

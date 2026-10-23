import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.GaussZeroBalanced.Series
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.GaussZeroBalanced.Series
open _root_.D5.S3.Analytic.GaussZeroBalanced.Defs
open _root_.D5.S3.Analytic.GaussZeroBalanced.Series
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
noncomputable section

abbrev gaussSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ → ℝ)
abbrev fSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ)

def gaussActual : Realization gaussSignature :=
  realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e)
def fActual : Realization fSignature :=
  realize fSignature (fun _ a b => f a b) (fun e => nomatch e)
def gaussRejected (v : ℝ) : Realization gaussSignature :=
  realize gaussSignature (fun _ _ _ _ _ => v) (fun e => nomatch e)
def fRejected (v : ℝ) : Realization fSignature :=
  realize fSignature (fun _ _ _ _ => v) (fun e => nomatch e)
def fAffine : Realization fSignature :=
  realize fSignature (fun _ _ _ x => 4 * x) (fun e => nomatch e)
def fDiscontinuous : Realization fSignature :=
  realize fSignature (fun _ _ _ x => if x = 1/2 then 0 else 1) (fun e => nomatch e)

private theorem gaussDependence : ObservationalDependence gaussSignature gaussActual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change gauss 1 1 ≠ gauss 1 2
  intro he
  have hfun := congrArg (fun g : ℝ → ℝ → ℝ => g 1) he
  have hd := congrArg (fun g : ℝ → ℝ => deriv g 0) hfun
  rw [(hasDerivAt_gauss (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) (by norm_num) (by norm_num)).deriv,
    (hasDerivAt_gauss (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)
      (by norm_num : (0:ℝ)<1) (by norm_num) (by norm_num)).deriv] at hd
  norm_num [gauss] at hd

private theorem fDependence : ObservationalDependence fSignature fActual := by
  intro i
  refine ⟨1, 1, 3, ?_⟩
  change f 1 1 ≠ f 1 3
  intro he
  have hd := congrArg (fun g : ℝ → ℝ => deriv g 0) he
  rw [deriv_f_zero (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1),
    deriv_f_zero (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<3)] at hd
  norm_num at hd

abbrev coefficientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ)
    (fun _ => ℝ → ℕ → ℝ)

def coefficientActual : Realization coefficientSignature :=
  realize coefficientSignature (fun _ a b => ordinaryHypergeometricCoefficient a b)
    (fun e => nomatch e)
def coefficientRejected : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ _ _ => 1) (fun e => nomatch e)

def coefficient_recurrenceArena : Arena where
  signature := coefficientSignature
  Law R := ∀ {a b c : ℝ}, 0 < c → ∀ n : ℕ,
    ((n + 1 : ℕ) : ℝ) * R.readout () a b c (n + 1) * (c + n) =
      (a + n) * (b + n) * R.readout () a b c n

private theorem coefficient_recurrenceRejected :
    ¬ coefficient_recurrenceArena.Law coefficientRejected := by
  intro h
  have he := @h 0 0 1 zero_lt_one 0
  norm_num [coefficientRejected, realize] at he

private theorem coefficientDependence :
    ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  intro he
  have hv := congrArg (fun f : ℝ → ℕ → ℝ => f 1 1) he
  norm_num [coefficientActual, realize, ordinaryHypergeometricCoefficient,
    ascPochhammer_succ_eval] at hv

def coefficient_recurrenceEvidence : Registration coefficient_recurrenceArena
    (type_of% @coefficient_recurrence) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@coefficient_recurrence, coefficientRejected, coefficient_recurrenceRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coefficient_recurrenceArena.Law coefficientActual coefficientRejected
    coefficient_recurrenceRejected
  dependence := coefficientDependence

def coefficient_recurrenceAudit :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@coefficient_recurrence) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_recurrenceUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_recurrenceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coefficient_recurrenceArena⟩
  objectArena := .source ⟨coefficient_recurrenceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficient_recurrenceArena ⟨coefficient_recurrenceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ a b => ordinaryHypergeometricCoefficient a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def coefficientZero : Realization coefficientSignature :=
  realize coefficientSignature (fun _ _ _ _ _ => 0) (fun e => nomatch e)

def coefficient_posArena : Arena where
  signature := coefficientSignature
  Law R := ∀ {a b c : ℝ}, 0 < a → 0 < b → 0 < c → ∀ n : ℕ,
    0 < R.readout () a b c n

private theorem coefficient_posRejected : ¬ coefficient_posArena.Law coefficientZero := by
  intro h
  exact lt_irrefl 0 (@h 1 1 1 zero_lt_one zero_lt_one zero_lt_one 0)

def coefficient_posEvidence : Registration coefficient_posArena
    (type_of% @coefficient_pos) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨@coefficient_pos, coefficientZero, coefficient_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    coefficient_posArena.Law coefficientActual coefficientZero coefficient_posRejected
  dependence := coefficientDependence

def coefficient_posAudit :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@coefficient_pos) (Realization coefficientSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_posUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.coefficient_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coefficient_posArena⟩
  objectArena := .source ⟨coefficient_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coefficient_posArena ⟨coefficient_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature
    (fun _ a b => ordinaryHypergeometricCoefficient a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def one_le_gaussArena : Arena where
  signature := gaussSignature
  Law R := ∀ {a b c x : ℝ} (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (_hx : 0 ≤ x) (_hx1 : x < 1), 1 ≤ R.readout () a b c x

private theorem one_le_gaussRejected : ¬ one_le_gaussArena.Law (gaussRejected 0) := by
  intro h
  have hh := @h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [gaussRejected, realize] at hh

def one_le_gaussEvidence : Registration one_le_gaussArena (type_of% @one_le_gauss) where
  actual := gaussActual
  bridge := Iff.rfl
  variation := ⟨@one_le_gauss, gaussRejected 0, one_le_gaussRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    one_le_gaussArena.Law gaussActual (gaussRejected 0) one_le_gaussRejected
  dependence := gaussDependence

def one_le_gaussAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@one_le_gauss) (Realization gaussSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.one_le_gaussUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.one_le_gaussEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨one_le_gaussArena⟩
  objectArena := .source ⟨one_le_gaussArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source one_le_gaussArena ⟨one_le_gaussEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gauss_posArena : Arena where
  signature := gaussSignature
  Law R := ∀ {a b c x : ℝ} (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (_hx : 0 ≤ x) (_hx1 : x < 1), 0 < R.readout () a b c x

private theorem gauss_posRejected : ¬ gauss_posArena.Law (gaussRejected 0) := by
  intro h
  have hh := @h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [gaussRejected, realize] at hh

def gauss_posEvidence : Registration gauss_posArena (type_of% @gauss_pos) where
  actual := gaussActual
  bridge := Iff.rfl
  variation := ⟨@gauss_pos, gaussRejected 0, gauss_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    gauss_posArena.Law gaussActual (gaussRejected 0) gauss_posRejected
  dependence := gaussDependence

def gauss_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gauss_pos) (Realization gaussSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.gauss_posUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.gauss_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gauss_posArena⟩
  objectArena := .source ⟨gauss_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gauss_posArena ⟨gauss_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def hasDerivAt_gaussArena : Arena where
  signature := gaussSignature
  Law R := ∀ {a b c x : ℝ} (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (_hx : 0 ≤ x) (_hx1 : x < 1), HasDerivAt (R.readout () a b c)
      (a * b / c * gauss (a + 1) (b + 1) (c + 1) x) x

private theorem hasDerivAt_gaussRejected : ¬ hasDerivAt_gaussArena.Law (gaussRejected 0) := by
  intro h
  have hh := @h 1 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := hh.unique (hasDerivAt_const (0:ℝ) (0:ℝ))
  norm_num [gaussRejected, realize, gauss] at he

def hasDerivAt_gaussEvidence : Registration hasDerivAt_gaussArena (type_of% @hasDerivAt_gauss) where
  actual := gaussActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_gauss, gaussRejected 0, hasDerivAt_gaussRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hasDerivAt_gaussArena.Law gaussActual (gaussRejected 0) hasDerivAt_gaussRejected
  dependence := gaussDependence

def hasDerivAt_gaussAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_gauss) (Realization gaussSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.hasDerivAt_gaussUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.hasDerivAt_gaussEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨hasDerivAt_gaussArena⟩
  objectArena := .source ⟨hasDerivAt_gaussArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hasDerivAt_gaussArena ⟨hasDerivAt_gaussEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def contiguous_GArena : Arena where
  signature := gaussSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 ≤ x) (_hx1 : x < 1), x * deriv (R.readout () a b (a + b + 1)) x =
      (a + b) * (gauss a b (a + b) x - gauss a b (a + b + 1) x)

private theorem contiguous_GRejected : ¬ contiguous_GArena.Law (gaussRejected 0) := by
  intro h
  have hh := @h 1 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hg := contiguous_G (a:=1) (b:=1) (x:=1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hd := (hasDerivAt_gauss (a:=1) (b:=1) (c:=3) (x:=1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).deriv
  have hp := gauss_pos (a:=2) (b:=2) (c:=4) (x:=1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [gaussRejected, realize] at hh hg
  norm_num at hd
  nlinarith [hh, hg, hd, hp]

def contiguous_GEvidence : Registration contiguous_GArena (type_of% @contiguous_G) where
  actual := gaussActual
  bridge := Iff.rfl
  variation := ⟨@contiguous_G, gaussRejected 0, contiguous_GRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    contiguous_GArena.Law gaussActual (gaussRejected 0) contiguous_GRejected
  dependence := gaussDependence

def contiguous_GAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contiguous_G) (Realization gaussSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.contiguous_GUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.contiguous_GEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨contiguous_GArena⟩
  objectArena := .source ⟨contiguous_GArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source contiguous_GArena ⟨contiguous_GEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def contiguous_HArena : Arena where
  signature := gaussSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 ≤ x) (_hx1 : x < 1), (1 - x) * deriv (R.readout () a b (a + b)) x =
      (a * b / (a + b)) * gauss a b (a + b + 1) x

private theorem contiguous_HRejected : ¬ contiguous_HArena.Law (gaussRejected 0) := by
  intro h
  have hh := @h 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [gaussRejected, realize, gauss] at hh

def contiguous_HEvidence : Registration contiguous_HArena (type_of% @contiguous_H) where
  actual := gaussActual
  bridge := Iff.rfl
  variation := ⟨@contiguous_H, gaussRejected 0, contiguous_HRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    contiguous_HArena.Law gaussActual (gaussRejected 0) contiguous_HRejected
  dependence := gaussDependence

def contiguous_HAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contiguous_H) (Realization gaussSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.contiguous_HUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.contiguous_HEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨contiguous_HArena⟩
  objectArena := .source ⟨contiguous_HArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source contiguous_HArena ⟨contiguous_HEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussSignature (fun _ a b => gauss a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def f_zeroArena : Arena where
  signature := fSignature
  Law R := ∀ (a b : ℝ), R.readout () a b 0 = 1

private theorem f_zeroRejected : ¬ f_zeroArena.Law (fRejected 0) := by
  intro h
  have hh := h 1 1
  norm_num [fRejected, realize] at hh

def f_zeroEvidence : Registration f_zeroArena (type_of% @f_zero) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@f_zero, fRejected 0, f_zeroRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    f_zeroArena.Law fActual (fRejected 0) f_zeroRejected
  dependence := fDependence

def f_zeroAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@f_zero) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_zeroUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_zeroEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨f_zeroArena⟩
  objectArena := .source ⟨f_zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source f_zeroArena ⟨f_zeroEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def f_posArena : Arena where
  signature := fSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 ≤ x) (_hx1 : x < 1), 0 < R.readout () a b x

private theorem f_posRejected : ¬ f_posArena.Law (fRejected 0) := by
  intro h
  have hh := @h 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [fRejected, realize] at hh

def f_posEvidence : Registration f_posArena (type_of% @f_pos) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@f_pos, fRejected 0, f_posRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    f_posArena.Law fActual (fRejected 0) f_posRejected
  dependence := fDependence

def f_posAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@f_pos) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_posUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_posEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨f_posArena⟩
  objectArena := .source ⟨f_posArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source f_posArena ⟨f_posEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def f_lt_oneArena : Arena where
  signature := fSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 < x) (_hx1 : x < 1), R.readout () a b x < 1

private theorem f_lt_oneRejected : ¬ f_lt_oneArena.Law (fRejected 2) := by
  intro h
  have hh := @h 1 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [fRejected, realize] at hh

def f_lt_oneEvidence : Registration f_lt_oneArena (type_of% @f_lt_one) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@f_lt_one, fRejected 2, f_lt_oneRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    f_lt_oneArena.Law fActual (fRejected 2) f_lt_oneRejected
  dependence := fDependence

def f_lt_oneAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@f_lt_one) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_lt_oneUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.f_lt_oneEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨f_lt_oneArena⟩
  objectArena := .source ⟨f_lt_oneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source f_lt_oneArena ⟨f_lt_oneEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def hasDerivAt_fArena : Arena where
  signature := fSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 ≤ x) (_hx1 : x < 1), HasDerivAt (R.readout () a b)
      ((deriv (gauss a b (a + b + 1)) x * gauss a b (a + b) x -
        gauss a b (a + b + 1) x * deriv (gauss a b (a + b)) x) /
          (gauss a b (a + b) x) ^ 2) x

private theorem hasDerivAt_fRejected : ¬ hasDerivAt_fArena.Law (fRejected 0) := by
  intro h
  have hh := @h 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := hh.unique (hasDerivAt_const (0:ℝ) (0:ℝ))
  have hd0 := (hasDerivAt_gauss (a:=1) (b:=1) (c:=2) (x:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).deriv
  have hd1 := (hasDerivAt_gauss (a:=1) (b:=1) (c:=3) (x:=0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).deriv
  norm_num [fRejected, realize] at he
  norm_num [gauss] at he hd0 hd1
  linarith

def hasDerivAt_fEvidence : Registration hasDerivAt_fArena (type_of% @hasDerivAt_f) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_f, fRejected 0, hasDerivAt_fRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hasDerivAt_fArena.Law fActual (fRejected 0) hasDerivAt_fRejected
  dependence := fDependence

def hasDerivAt_fAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_f) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.hasDerivAt_fUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.hasDerivAt_fEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨hasDerivAt_fArena⟩
  objectArena := .source ⟨hasDerivAt_fArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hasDerivAt_fArena ⟨hasDerivAt_fEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def continuousOn_fArena : Arena where
  signature := fSignature
  Law R := ∀ {a b : ℝ} (_ha : 0 < a) (_hb : 0 < b), ContinuousOn (R.readout () a b) (Ico 0 1)

private theorem continuousOn_fRejected : ¬ continuousOn_fArena.Law (fDiscontinuous) := by
  intro h
  have hc := @h 1 1 (by norm_num) (by norm_num)
  have hct : ContinuousAt (fun x : ℝ => if x = 1/2 then (0:ℝ) else 1) (1/2) :=
    hc.continuousAt (Ico_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨d, hd, hbound⟩ := Metric.continuousAt_iff.mp hct (1/2) (by norm_num)
  let y := (1/2:ℝ) + d/2
  have hy : y ≠ 1/2 := by dsimp [y]; linarith
  have hdist : dist y (1/2:ℝ) < d := by
    rw [Real.dist_eq, abs_of_pos]; all_goals dsimp [y]; linarith
  have he := hbound hdist
  norm_num [hy] at he

def continuousOn_fEvidence : Registration continuousOn_fArena (type_of% @continuousOn_f) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@continuousOn_f, fDiscontinuous, continuousOn_fRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    continuousOn_fArena.Law fActual (fDiscontinuous) continuousOn_fRejected
  dependence := fDependence

def continuousOn_fAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuousOn_f) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.continuousOn_fUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.continuousOn_fEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨continuousOn_fArena⟩
  objectArena := .source ⟨continuousOn_fArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source continuousOn_fArena ⟨continuousOn_fEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def quot_eqArena : Arena where
  signature := fSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 ≤ x) (_hx1 : x < 1), quot a b x = R.readout () a b x / (1 - x)

private theorem quot_eqRejected : ¬ quot_eqArena.Law (fRejected 0) := by
  intro h
  have hh := @h 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [fRejected, realize, quot, gauss] at hh

def quot_eqEvidence : Registration quot_eqArena (type_of% @quot_eq) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@quot_eq, fRejected 0, quot_eqRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    quot_eqArena.Law fActual (fRejected 0) quot_eqRejected
  dependence := fDependence

def quot_eqAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quot_eq) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.quot_eqUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.quot_eqEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨quot_eqArena⟩
  objectArena := .source ⟨quot_eqArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quot_eqArena ⟨quot_eqEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def riccatiArena : Arena where
  signature := fSignature
  Law R := ∀ {a b x : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (_hx : 0 < x) (_hx1 : x < 1), x * deriv (R.readout () a b) x = (a + b) * (1 - f a b x) -
      (a * b / (a + b)) * (x / (1 - x)) * (f a b x) ^ 2

private theorem riccatiRejected : ¬ riccatiArena.Law (fAffine) := by
  intro h
  have hh := @h 1 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : deriv (fun x : ℝ => 4 * x) (1/2) = 4 := by
    simpa using ((hasDerivAt_id (1/2:ℝ)).const_mul 4).deriv
  change (1/2:ℝ) * deriv (fun x : ℝ => 4*x) (1/2) = _ at hh
  rw [hd] at hh
  have hp := f_pos (a:=1) (b:=1) (x:=1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hh
  nlinarith [sq_nonneg (f 1 1 (1/2))]

def riccatiEvidence : Registration riccatiArena (type_of% @riccati) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@riccati, fAffine, riccatiRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    riccatiArena.Law fActual (fAffine) riccatiRejected
  dependence := fDependence

def riccatiAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@riccati) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.riccatiUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.riccatiEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨riccatiArena⟩
  objectArena := .source ⟨riccatiArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source riccatiArena ⟨riccatiEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def deriv_f_zeroArena : Arena where
  signature := fSignature
  Law R := ∀ {a b : ℝ} (_ha : 0 < a) (_hb : 0 < b), deriv (R.readout () a b) 0 = -(a * b / ((a + b) * (a + b + 1)))

private theorem deriv_f_zeroRejected : ¬ deriv_f_zeroArena.Law (fRejected 0) := by
  intro h
  have hh := @h 1 1 (by norm_num) (by norm_num)
  norm_num [fRejected, realize] at hh

def deriv_f_zeroEvidence : Registration deriv_f_zeroArena (type_of% @deriv_f_zero) where
  actual := fActual
  bridge := Iff.rfl
  variation := ⟨@deriv_f_zero, fRejected 0, deriv_f_zeroRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    deriv_f_zeroArena.Law fActual (fRejected 0) deriv_f_zeroRejected
  dependence := fDependence

def deriv_f_zeroAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@deriv_f_zero) (Realization fSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.deriv_f_zeroUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Series.deriv_f_zeroEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨deriv_f_zeroArena⟩
  objectArena := .source ⟨deriv_f_zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deriv_f_zeroArena ⟨deriv_f_zeroEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Series
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.GaussZeroBalanced.Series

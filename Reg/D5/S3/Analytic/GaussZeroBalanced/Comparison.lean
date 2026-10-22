import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.GaussZeroBalanced.Comparison
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison
open _root_.D5.S3.Analytic.GaussZeroBalanced.Defs
open _root_.D5.S3.Analytic.GaussZeroBalanced.Comparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
noncomputable section

abbrev comparison_iffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ)
def comparison_iffActual : Realization comparison_iffSignature :=
  realize comparison_iffSignature (fun _ a b => f a b) (fun e => nomatch e)
def comparison_iffRejected : Realization comparison_iffSignature :=
  realize comparison_iffSignature (fun _ _ _ _ => 0) (fun e => nomatch e)
def comparison_iffArena : Arena where
  signature := comparison_iffSignature
  Law R := ∀ {a b₁ b₂ : ℝ} (_ha : 0 < a) (_h1 : 0 < b₁) (_h12 : b₁ < b₂),
    (∀ x ∈ Ioo (0:ℝ) 1, R.readout () a b₂ x < R.readout () a b₁ x) ↔
      b₁ * b₂ ≤ a * (a + 1)
private theorem comparison_iffRejected_not_law : ¬ comparison_iffArena.Law comparison_iffRejected := by
  intro h
  have hh := (@h 1 1 2 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
    (1/2) (by constructor <;> norm_num)
  norm_num [comparison_iffRejected, realize] at hh
private theorem comparison_iffDependence : ObservationalDependence comparison_iffSignature comparison_iffActual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change f 1 1 ≠ f 1 2
  intro heq
  have hh := (comparison_iff (a:=1) (b₁:=1) (b₂:=2) (by norm_num) (by norm_num)
    (by norm_num)).2 (by norm_num) (1/2) (by constructor <;> norm_num)
  rw [heq] at hh
  exact (lt_irrefl _ hh)
def comparison_iffEvidence : Registration comparison_iffArena (type_of% @comparison_iff) where
  actual := comparison_iffActual
  bridge := Iff.rfl
  variation := ⟨@comparison_iff, comparison_iffRejected, comparison_iffRejected_not_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    comparison_iffArena.Law comparison_iffActual comparison_iffRejected comparison_iffRejected_not_law
  dependence := comparison_iffDependence

abbrev comparison_iff_quotSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ → ℝ)
def comparison_iff_quotActual : Realization comparison_iff_quotSignature :=
  realize comparison_iff_quotSignature (fun _ a b => quot a b) (fun e => nomatch e)
def comparison_iff_quotRejected : Realization comparison_iff_quotSignature :=
  realize comparison_iff_quotSignature (fun _ _ _ _ => 0) (fun e => nomatch e)
def comparison_iff_quotArena : Arena where
  signature := comparison_iff_quotSignature
  Law R := ∀ {a b₁ b₂ : ℝ} (_ha : 0 < a) (_h1 : 0 < b₁) (_h12 : b₁ < b₂),
    (∀ x ∈ Ioo (0:ℝ) 1, R.readout () a b₂ x < R.readout () a b₁ x) ↔
      b₁ * b₂ ≤ a * (a + 1)
private theorem comparison_iff_quotRejected_not_law : ¬ comparison_iff_quotArena.Law comparison_iff_quotRejected := by
  intro h
  have hh := (@h 1 1 2 (by norm_num) (by norm_num) (by norm_num)).2 (by norm_num)
    (1/2) (by constructor <;> norm_num)
  norm_num [comparison_iff_quotRejected, realize] at hh
private theorem comparison_iff_quotDependence : ObservationalDependence comparison_iff_quotSignature comparison_iff_quotActual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change quot 1 1 ≠ quot 1 2
  intro heq
  have hh := (comparison_iff_quot (a:=1) (b₁:=1) (b₂:=2) (by norm_num) (by norm_num)
    (by norm_num)).2 (by norm_num) (1/2) (by constructor <;> norm_num)
  rw [heq] at hh
  exact (lt_irrefl _ hh)
def comparison_iff_quotEvidence : Registration comparison_iff_quotArena (type_of% @comparison_iff_quot) where
  actual := comparison_iff_quotActual
  bridge := Iff.rfl
  variation := ⟨@comparison_iff_quot, comparison_iff_quotRejected, comparison_iff_quotRejected_not_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    comparison_iff_quotArena.Law comparison_iff_quotActual comparison_iff_quotRejected comparison_iff_quotRejected_not_law
  dependence := comparison_iff_quotDependence

def comparison_iffAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@comparison_iff) (Realization comparison_iffSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison.comparison_iffUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison.comparison_iffEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨comparison_iffArena⟩
  objectArena := .source ⟨comparison_iffArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparison_iffArena ⟨comparison_iffEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparison_iffSignature (fun _ a b => f a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Comparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def comparison_iff_quotAudit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@comparison_iff_quot) (Realization comparison_iff_quotSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison.comparison_iff_quotUnit
  realizationName := `Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison.comparison_iff_quotEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨comparison_iff_quotArena⟩
  objectArena := .source ⟨comparison_iff_quotArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source comparison_iff_quotArena ⟨comparison_iff_quotEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize comparison_iff_quotSignature (fun _ a b => quot a b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.GaussZeroBalanced.Comparison
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.GaussZeroBalanced.Comparison

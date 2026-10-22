import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MeijerZeroCount.Control
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.MeijerZeroCount.Control
open _root_.D5.S3.Analytic.MeijerZeroCount.Defs
open _root_.D5.S3.Analytic.MeijerZeroCount.Control
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℕ × ℕ × ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p x =>
    control ![(p.1 : ℝ)+p.2.2, (p.1 : ℝ)+p.2.2]
      ![p.2.2, ((2*p.1+p.2.1 : ℕ) : ℝ)+p.2.2] x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (c : ℝ), 0 < n → 0 < d →
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ R.readout () (n,d,c) x = 0}.encard = 1

private theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1 0 (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1,1,0), 0, 1, ?_⟩
  norm_num [actual, realize, _root_.D5.S3.Analytic.MeijerZeroCount.Defs.control, Fin.sum_univ_two]

def evidence : Registration arena (type_of% @zeros_control) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zeros_control, rejected, rejected_not_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_not_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zeros_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MeijerZeroCount.Control.unit
  realizationName := `Reg.D5.S3.Analytic.MeijerZeroCount.Control.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x =>
    control ![(p.1 : ℝ)+p.2.2, (p.1 : ℝ)+p.2.2]
      ![p.2.2, ((2*p.1+p.2.1 : ℕ) : ℝ)+p.2.2] x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MeijerZeroCount.Control
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end
end Reg.D5.S3.Analytic.MeijerZeroCount.Control

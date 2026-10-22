import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MeijerZeroCount.Rodrigues
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.Analytic.MeijerZeroCount.Rodrigues
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
namespace Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues
namespace Expansion
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ × ℝ) (fun _ => ℝ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p x => f p.1 p.2.1 p.2.2 x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (c x : ℝ), x ∈ Set.Ioo 0 1 →
    R.readout () (n, d, c) x = ∑ k ∈ range (n+d-1+1),
      (coeffA n d k : ℂ) * ((x ^ ((n : ℝ)+c+k) : ℝ) : ℂ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0 1 0 (1/2) (by norm_num)
  norm_num [rejected, realize, coeffA, Finset.sum_range_succ] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 1, 0), 0, 1/2, ?_⟩
  norm_num [actual, realize, f, rodriguesPoly, W]
def family : Registration arena (type_of% @f_eq_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨f_eq_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@f_eq_sum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues.Expansion.unit
  realizationName := `Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues.Expansion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => f p.1 p.2.1 p.2.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MeijerZeroCount.Rodrigues
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Expansion

namespace ZeroCount
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℝ) (fun _ => ℕ) (fun _ => ℕ∞)
def actual : Realization signature :=
  realize signature (fun _ p n =>
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f n p.1 p.2 x = 0}.encard) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (n d : ℕ) (c : ℝ), 1 ≤ d → R.readout () (d, c) n = (n : ℕ∞)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 1 0 (by norm_num)
  norm_num [rejected, realize] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1, 0), 0, 1, ?_⟩
  change {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f 0 1 0 x = 0}.encard ≠
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f 1 1 0 x = 0}.encard
  rw [zeros_f 0 1 0 (by norm_num), zeros_f 1 1 0 (by norm_num)]
  norm_num
def family : Registration arena (type_of% @zeros_f) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨zeros_f, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zeros_f) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues.ZeroCount.unit
  realizationName := `Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues.ZeroCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n =>
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f n p.1 p.2 x = 0}.encard) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MeijerZeroCount.Rodrigues
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ZeroCount
#print axioms Expansion.audit
#print axioms ZeroCount.audit
end Reg.D5.S3.Analytic.MeijerZeroCount.Rodrigues

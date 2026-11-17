import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

namespace Polynomial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ s => laplacePolynomial s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ}, 0 ≤ s → 0 ≤ R.readout () () s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (s := 0) (by norm_num)
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize, laplacePolynomial]

def family : Registration arena (type_of% (@laplacePolynomial_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@laplacePolynomial_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@laplacePolynomial_nonneg) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.laplacePolynomial_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.Polynomial.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => laplacePolynomial s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Polynomial


namespace Weight
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ y => W y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 4) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x y : ℝ}, 0 < x → x ≤ y → R.readout () x y ≤ W x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 1) (y := 1) (by norm_num) (by norm_num)
  norm_num [rejected, realize, W] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  norm_num [actual, realize, W]
def family : Registration arena (type_of% (@W_antitone)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@W_antitone, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@W_antitone) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.W_antitone.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.Weight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ y => W y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
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
end Weight

namespace Denominator
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℂ (fun _ => ℝ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ z s => denominator z s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨11 * Complex.I, 0, 1, ?_⟩
  change denominator (11 * Complex.I) 0 ≠ denominator (11 * Complex.I) 1
  intro he
  have hr := congrArg Complex.re he
  norm_num [denominator] at hr

namespace Norm
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, 10 ≤ |z.im| → ∀ s : ℝ, 10 ≤ ‖R.readout () z s‖
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 11 * Complex.I) (by norm_num) 0
  norm_num [rejected, realize] at hh
def family : Registration arena (type_of% (@denominator_norm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@denominator_norm, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@denominator_norm) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.denominator_norm.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.Denominator.Norm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z s => denominator z s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Norm

namespace Nonzero
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, 10 ≤ |z.im| → ∀ s : ℝ, R.readout () z s ≠ 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (z := 11 * Complex.I) (by norm_num) 0
  exact hh rfl
def family : Registration arena (type_of% (@denominator_ne)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@denominator_ne, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@denominator_ne) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.denominator_ne.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent.Denominator.Nonzero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z s => denominator z s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Nonzero
end Denominator

end
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent

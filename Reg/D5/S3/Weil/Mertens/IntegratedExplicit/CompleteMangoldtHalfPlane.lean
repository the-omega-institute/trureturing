import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (U)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

/-- Observe the transform of the logarithmic correction at the same complex exponent. -/
def actual : Realization signature :=
  realize signature (fun _ _ s => 1 / (s - 1) ^ 2) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ s => 1 / (s - 1) ^ 2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {s : ℂ}, 1 < s.re →
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * (U (Real.exp y) : ℂ)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * (U (Real.exp y) : ℂ)) =
        (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) -
          V.readout () () s + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1)

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h₁ := (h (s := 2) hs).2
  have h₂ := (u_laplace_half_plane hs).2
  change _ = _ - (1 / ((2 : ℂ) - 1) ^ 2 + 1) + _ at h₁
  have he := h₁.symm.trans h₂
  have hzero : (1 : ℂ) = 0 := by linear_combination -he
  exact one_ne_zero hzero

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (2 : ℂ), (3 : ℂ), ?_⟩
  change 1 / ((2 : ℂ) - 1) ^ 2 ≠ 1 / ((3 : ℂ) - 1) ^ 2
  norm_num

def family : Registration arena (type_of% @u_laplace_half_plane) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@u_laplace_half_plane, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@u_laplace_half_plane) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane.u_laplace_half_plane
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ s => 1 / (s - 1) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace MomentIntegrable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => fun w => z * w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℂ} (hs : 1 < s.re),
    IntegrableOn (fun y : ℝ => R.readout () () (y : ℂ)
      (Complex.exp ((1 - s) * y))) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (s := 2) (by norm_num)
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi 0) at he
  simpa [IntegrableOn, integrable_const_iff, isFiniteMeasure_iff] using he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (1 : ℂ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @first_moment_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@first_moment_integrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@first_moment_integrable) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane.first_moment_integrable
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane.MomentIntegrable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => fun w => z * w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentIntegrable

namespace Moment

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ s => 1 / (s - 1) ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ s => 1 / (s - 1) ^ 2 + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℂ} (hs : 1 < s.re),
    (∫ y : ℝ in Ioi 0, (y : ℂ) * Complex.exp ((1 - s) * y)) = R.readout () () s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (s := 2) (by norm_num)
  rw [first_moment (by norm_num : 1 < (2 : ℂ).re)] at he
  norm_num [rejected, realize] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @first_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@first_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@first_moment) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane.first_moment
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane.Moment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => 1 / (s - 1) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
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

end Moment

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
